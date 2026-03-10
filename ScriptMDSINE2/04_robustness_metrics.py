#!/usr/bin/env python3
"""
R-XVII Robustesse aux métriques alternatives — Microbiome MDSINE2
==================================================================
Refait le test R-XVII central (input vs hardware, cohorte dysbiotique)
avec 5 métriques de distance indépendantes.

Objectif : montrer que le résultat p=0.0006, d=1.16 (Bray-Curtis)
n'est pas un artefact du choix de métrique.

Métriques :
  1. Bray-Curtis         (référence, résultat publié)
  2. Jensen-Shannon      (information-théorique, symétrique)
  3. Aitchison (CLR+Euc) (compositionnelle, log-ratio)
  4. Hellinger           (racine carrée, adapté aux proportions)
  5. Canberra            (pondérée par l'abondance)

Usage :  python 04_robustness_metrics.py
"""

import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
OUTPUT_DIR = PROJECT_ROOT / 'output'
OUTPUT_DIR.mkdir(exist_ok=True)
_data_base = PROJECT_ROOT / 'MDSINE2_Paper' / 'datasets' / 'gibson'

import numpy as np
import pandas as pd
from scipy import stats, spatial
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
import warnings, json, sys
warnings.filterwarnings('ignore')

plt.rcParams.update({
    'font.size': 10, 'axes.titlesize': 12, 'axes.labelsize': 11,
    'figure.dpi': 150, 'savefig.dpi': 300, 'savefig.bbox': 'tight',
})

# ── Patch llvmlite/numba pour que mdsine2 charge ───────────
# Le problème : mdsine2 → numba → llvmlite → libllvmlite.dylib (cassé)
# Solution : on injecte des modules factices AVANT l'import mdsine2

import types, ctypes

def _patch_llvmlite():
    """Injecte des stubs pour llvmlite et numba si le vrai est cassé."""
    try:
        import llvmlite.binding
        return  # ça marche, rien à faire
    except (ImportError, OSError):
        pass

    # Stub llvmlite
    for mod_name in [
        'llvmlite', 'llvmlite.binding', 'llvmlite.binding.dylib',
        'llvmlite.binding.ffi', 'llvmlite.ir', 'llvmlite.binding.module',
        'llvmlite.binding.value', 'llvmlite.binding.executionengine',
        'llvmlite.binding.targets', 'llvmlite.binding.initfini',
        'llvmlite.binding.linker', 'llvmlite.binding.context',
        'llvmlite.binding.passmanagers', 'llvmlite.binding.transforms',
        'llvmlite.binding.analysis', 'llvmlite.binding.object_file',
        'llvmlite.utils',
    ]:
        if mod_name not in sys.modules:
            m = types.ModuleType(mod_name)
            m.__path__ = []
            sys.modules[mod_name] = m

    # Stub numba (il a beaucoup de sous-modules)
    numba_stubs = [
        'numba', 'numba.core', 'numba.core.config', 'numba.core.types',
        'numba.core.typing', 'numba.core.errors', 'numba.core.decorators',
        'numba.np', 'numba.np.ufunc', 'numba.typed', 'numba.typed.typedlist',
        'numba.typed.typeddict', 'numba.experimental',
    ]
    for mod_name in numba_stubs:
        if mod_name not in sys.modules:
            m = types.ModuleType(mod_name)
            m.__path__ = []
            sys.modules[mod_name] = m

    # numba.njit et numba.jit doivent être des no-op decorators
    def _noop_decorator(*args, **kwargs):
        if len(args) == 1 and callable(args[0]):
            return args[0]
        return lambda f: f

    numba_mod = sys.modules['numba']
    numba_mod.njit = _noop_decorator
    numba_mod.jit = _noop_decorator
    numba_mod.vectorize = _noop_decorator
    numba_mod.prange = range
    numba_mod.float64 = float
    numba_mod.int64 = int
    numba_mod.boolean = bool
    numba_mod.types = sys.modules['numba.core.types']

_patch_llvmlite()

import mdsine2 as md2

# ── Chargement ──────────────────────────────────────────────

phases = {
    'equilibration': (0, 21.5),
    'HFD': (21.5, 28.5),
    'recovery_1': (28.5, 35.5),
    'vancomycin': (35.5, 42.5),
    'recovery_2': (42.5, 50.5),
    'gentamicin': (50.5, 57.5),
    'recovery_3': (57.5, 65.0),
}

def get_phase(t):
    for name, (start, end) in phases.items():
        if start <= t < end:
            return name
    return 'post'

def extract_data(study, cohort_name):
    records = []
    for subj in study:
        M = subj.matrix()
        abs_m = M['abs']
        rel_m = M['rel']
        times = subj.times
        for i, t in enumerate(times):
            records.append({
                'cohort': cohort_name,
                'subject': subj.name,
                'time': t,
                'phase': get_phase(t),
                'abs_profile': abs_m[:, i],
                'rel_profile': rel_m[:, i],
            })
    return records

print("Chargement des données...")
h_pkl = _data_base / 'healthy' / 'preprocessed' / 'gibson_healthy_agg_filtered.pkl'
u_pkl = _data_base / 'uc' / 'preprocessed' / 'gibson_uc_agg_filtered.pkl'

study_h = md2.Study.load(str(h_pkl))
study_u = md2.Study.load(str(u_pkl))

h_data = extract_data(study_h, 'healthy')
u_data = extract_data(study_u, 'dysbiotic')

print(f"  Healthy:   {len(h_data)} samples, {len(study_h.taxa)} taxa, "
      f"{len(set(r['subject'] for r in h_data))} sujets")
print(f"  Dysbiotic: {len(u_data)} samples, {len(study_u.taxa)} taxa, "
      f"{len(set(r['subject'] for r in u_data))} sujets")


# ── Métriques de distance ───────────────────────────────────

def bray_curtis(p, q):
    """Bray-Curtis dissimilarity (référence)."""
    return spatial.distance.braycurtis(p, q)


def jensen_shannon(p, q):
    """Jensen-Shannon divergence (racine carrée = distance métrique)."""
    return spatial.distance.jensenshannon(p, q)


def aitchison(p, q):
    """
    Distance d'Aitchison : euclidienne dans l'espace CLR.
    CLR = Centered Log-Ratio : log(x_i / geometric_mean(x))
    Standard pour les données compositionnelles (Gloor et al. 2017).
    """
    eps = 1e-10  # pseudocount pour éviter log(0)
    p_safe = p + eps
    q_safe = q + eps
    # Normaliser après pseudocount
    p_safe = p_safe / p_safe.sum()
    q_safe = q_safe / q_safe.sum()
    # CLR
    clr_p = np.log(p_safe) - np.mean(np.log(p_safe))
    clr_q = np.log(q_safe) - np.mean(np.log(q_safe))
    return np.sqrt(np.sum((clr_p - clr_q) ** 2))


def hellinger(p, q):
    """
    Distance de Hellinger : euclidienne sur les racines carrées.
    Bornée [0, sqrt(2)], très utilisée en écologie.
    """
    p_norm = p / (p.sum() + 1e-15)
    q_norm = q / (q.sum() + 1e-15)
    return np.sqrt(np.sum((np.sqrt(p_norm) - np.sqrt(q_norm)) ** 2)) / np.sqrt(2)


def canberra(p, q):
    """
    Distance de Canberra : pondère chaque taxon par son abondance.
    Plus sensible aux taxons rares que Bray-Curtis.
    """
    return spatial.distance.canberra(p, q)


METRICS = {
    'Bray-Curtis': bray_curtis,
    'Jensen-Shannon': jensen_shannon,
    'Aitchison (CLR)': aitchison,
    'Hellinger': hellinger,
    'Canberra': canberra,
}


# ── Test R-XVII avec chaque métrique ────────────────────────

def compute_rxvii_all_metrics(data, label):
    """
    Pour chaque métrique, calcule la distance entre le profil de baseline
    global et les profils de late recovery, séparés par type de perturbation.
    """
    subjects = sorted(set(r['subject'] for r in data))
    all_results = {name: {'input': [], 'hardware': []} for name in METRICS}

    for subj in subjects:
        sdata = sorted([r for r in data if r['subject'] == subj],
                       key=lambda x: x['time'])

        # Baseline global : late equilibration (t = 15–21.5)
        baseline_samples = [r for r in sdata if 15 <= r['time'] < 21.5]
        if len(baseline_samples) < 3:
            continue

        baseline_rel = np.mean([r['rel_profile'] for r in baseline_samples], axis=0)
        baseline_rel = baseline_rel / (baseline_rel.sum() + 1e-15)

        # Recovery windows (late = t_since_pert >= 4)
        recovery_map = {
            'HFD':        ('input',    28.5, 35.5),
            'vancomycin': ('hardware', 42.5, 50.5),
            'gentamicin': ('hardware', 57.5, 65.0),
        }

        for pert_name, (ptype, pert_end, phase_end) in recovery_map.items():
            late_samples = [r for r in sdata
                           if pert_end + 4 <= r['time'] < phase_end]
            for r in late_samples:
                profile = r['rel_profile']
                profile = profile / (profile.sum() + 1e-15)

                for metric_name, metric_fn in METRICS.items():
                    d = metric_fn(baseline_rel, profile)
                    all_results[metric_name][ptype].append(d)

    return all_results


def test_rxvii(results, label):
    """Test statistique pour chaque métrique."""
    print(f"\n{'='*70}")
    print(f"  R-XVII — {label}")
    print(f"{'='*70}")
    print(f"\n  {'Métrique':<20s} {'Input':>10s} {'Hardware':>10s} "
          f"{'p':>12s} {'d':>8s} {'Ratio':>8s}")
    print("  " + "-" * 72)

    table = []

    for metric_name in METRICS:
        inp = np.array(results[metric_name]['input'])
        hw = np.array(results[metric_name]['hardware'])

        if len(inp) < 3 or len(hw) < 3:
            print(f"  {metric_name:<20s}  n trop petit")
            continue

        U, p = stats.mannwhitneyu(hw, inp, alternative='greater')
        pooled_std = np.sqrt((np.var(hw) + np.var(inp)) / 2)
        d = (np.mean(hw) - np.mean(inp)) / pooled_std if pooled_std > 0 else 0
        ratio = np.mean(hw) / np.mean(inp) if np.mean(inp) > 1e-10 else np.nan

        sig = "***" if p < 0.001 else "**" if p < 0.01 else "*" if p < 0.05 else "ns"

        print(f"  {metric_name:<20s} {np.mean(inp):10.4f} {np.mean(hw):10.4f} "
              f"{p:12.6f} {d:8.3f} {ratio:8.2f}x  {sig}")

        table.append({
            'metric': metric_name,
            'cohort': label,
            'input_mean': float(np.mean(inp)),
            'input_std': float(np.std(inp)),
            'hw_mean': float(np.mean(hw)),
            'hw_std': float(np.std(hw)),
            'n_input': len(inp),
            'n_hw': len(hw),
            'U': float(U),
            'p': float(p),
            'd': float(d),
            'ratio': float(ratio),
        })

    return table


# ── Bootstrap CI pour chaque métrique ───────────────────────

def bootstrap_ci(results, n_boot=10000, seed=42):
    """Bootstrap 95% CI sur le Cohen's d pour chaque métrique."""
    rng = np.random.RandomState(seed)
    boot_results = {}

    for metric_name in METRICS:
        inp = np.array(results[metric_name]['input'])
        hw = np.array(results[metric_name]['hardware'])

        if len(inp) < 3 or len(hw) < 3:
            continue

        boot_d = np.zeros(n_boot)
        boot_ratio = np.zeros(n_boot)
        for b in range(n_boot):
            bi = rng.choice(inp, len(inp), replace=True)
            bh = rng.choice(hw, len(hw), replace=True)
            pooled = np.sqrt((np.var(bi) + np.var(bh)) / 2)
            boot_d[b] = (np.mean(bh) - np.mean(bi)) / pooled if pooled > 0 else 0
            boot_ratio[b] = np.mean(bh) / np.mean(bi) if np.mean(bi) > 1e-10 else np.nan

        boot_d = boot_d[np.isfinite(boot_d)]
        boot_ratio = boot_ratio[np.isfinite(boot_ratio)]

        boot_results[metric_name] = {
            'd_ci': (float(np.percentile(boot_d, 2.5)),
                     float(np.percentile(boot_d, 97.5))),
            'd_mean': float(np.mean(boot_d)),
            'ratio_ci': (float(np.percentile(boot_ratio, 2.5)),
                         float(np.percentile(boot_ratio, 97.5))),
            'ratio_mean': float(np.mean(boot_ratio)),
            'boot_d': boot_d,
        }

    return boot_results


# ── Figures ─────────────────────────────────────────────────

def plot_robustness(table_d, table_h, boot_d, boot_h):
    """Figure de synthèse : robustesse aux métriques."""

    fig = plt.figure(figsize=(20, 20))
    gs = gridspec.GridSpec(4, 2, hspace=0.4, wspace=0.3)
    fig.suptitle("R-XVII Robustesse aux métriques — Microbiome MDSINE2\n"
                 "Le résultat tient-il sous 5 métriques de distance indépendantes ?",
                 fontsize=14, fontweight='bold', y=0.995)

    C_IN = '#2196F3'
    C_HW = '#E53935'
    C_D = '#C62828'
    C_H = '#1565C0'

    metric_names = [r['metric'] for r in table_d]

    # A : Forest plot — Cohen's d par métrique (dysbiotic)
    ax = fig.add_subplot(gs[0, 0])
    y = np.arange(len(metric_names))
    ds = [r['d'] for r in table_d]
    ci_lo = [boot_d[m]['d_ci'][0] for m in metric_names]
    ci_hi = [boot_d[m]['d_ci'][1] for m in metric_names]
    errs = [[d - lo for d, lo in zip(ds, ci_lo)],
            [hi - d for d, hi in zip(ds, ci_hi)]]

    colors = ['#4CAF50' if r['p'] < 0.001 else '#FF9800' if r['p'] < 0.05 else '#9E9E9E'
              for r in table_d]
    ax.barh(y, ds, xerr=errs, color=colors, alpha=0.8, edgecolor='black',
            capsize=4, height=0.6)
    ax.axvline(0, color='gray', ls=':', lw=1)
    ax.set_yticks(y)
    ax.set_yticklabels(metric_names)
    ax.set_xlabel("Cohen's d")
    ax.set_title("A. Dysbiotic — Cohen's d par métrique\n(vert = p<0.001, orange = p<0.05)")
    ax.invert_yaxis()

    # B : Forest plot — ratio par métrique (dysbiotic)
    ax = fig.add_subplot(gs[0, 1])
    ratios = [r['ratio'] for r in table_d]
    r_lo = [boot_d[m]['ratio_ci'][0] for m in metric_names]
    r_hi = [boot_d[m]['ratio_ci'][1] for m in metric_names]
    r_errs = [[r - lo for r, lo in zip(ratios, r_lo)],
              [hi - r for r, hi in zip(ratios, r_hi)]]

    ax.barh(y, ratios, xerr=r_errs, color=colors, alpha=0.8, edgecolor='black',
            capsize=4, height=0.6)
    ax.axvline(1, color='gray', ls=':', lw=1, label='ratio = 1 (pas d\'asymétrie)')
    ax.axvline(1.86, color='#7B1FA2', ls='--', lw=2, alpha=0.7,
               label='Bray-Curtis publié (1.86×)')
    ax.set_yticks(y)
    ax.set_yticklabels(metric_names)
    ax.set_xlabel("Ratio Hardware / Input")
    ax.set_title("B. Dysbiotic — Ratio struct/input par métrique")
    ax.legend(fontsize=8)
    ax.invert_yaxis()

    # C : Barplot input vs hardware par métrique (dysbiotic)
    ax = fig.add_subplot(gs[1, 0])
    x = np.arange(len(metric_names))
    w = 0.35
    inp_vals = [r['input_mean'] for r in table_d]
    hw_vals = [r['hw_mean'] for r in table_d]
    inp_std = [r['input_std'] for r in table_d]
    hw_std = [r['hw_std'] for r in table_d]

    # Normaliser pour comparabilité (chaque métrique a une échelle différente)
    for i in range(len(metric_names)):
        scale = max(inp_vals[i], hw_vals[i], 1e-10)
        inp_vals[i] /= scale
        hw_vals[i] /= scale
        inp_std[i] /= scale
        hw_std[i] /= scale

    ax.bar(x - w/2, inp_vals, w, yerr=inp_std, color=C_IN, alpha=0.7,
           capsize=3, label='Input (HFD)', edgecolor='black')
    ax.bar(x + w/2, hw_vals, w, yerr=hw_std, color=C_HW, alpha=0.7,
           capsize=3, label='Hardware (antibio)', edgecolor='black')
    ax.set_xticks(x)
    ax.set_xticklabels(metric_names, fontsize=9, rotation=15, ha='right')
    ax.set_ylabel("Distance normalisée")
    ax.set_title("C. Dysbiotic — Input vs Hardware (normalisé)")
    ax.legend(fontsize=9)

    # D : Bootstrap distributions du d (dysbiotic)
    ax = fig.add_subplot(gs[1, 1])
    metric_colors = ['#2196F3', '#4CAF50', '#FF9800', '#9C27B0', '#795548']
    for i, m in enumerate(metric_names):
        if m in boot_d:
            ax.hist(boot_d[m]['boot_d'], bins=50, alpha=0.35,
                    color=metric_colors[i % len(metric_colors)],
                    density=True, label=m)
    ax.axvline(0, color='gray', ls=':', lw=1)
    ax.set_xlabel("Cohen's d (bootstrap)")
    ax.set_ylabel("Densité")
    ax.set_title("D. Distributions bootstrap du d")
    ax.legend(fontsize=8)

    # E : Même analyse sur la cohorte saine (contrôle)
    ax = fig.add_subplot(gs[2, 0])
    if table_h:
        y = np.arange(len(table_h))
        ds_h = [r['d'] for r in table_h]
        names_h = [r['metric'] for r in table_h]
        colors_h = ['#4CAF50' if r['p'] < 0.05 else '#9E9E9E' for r in table_h]

        if boot_h:
            ci_lo_h = [boot_h[m]['d_ci'][0] if m in boot_h else 0 for m in names_h]
            ci_hi_h = [boot_h[m]['d_ci'][1] if m in boot_h else 0 for m in names_h]
            errs_h = [[d - lo for d, lo in zip(ds_h, ci_lo_h)],
                      [hi - d for d, hi in zip(ds_h, ci_hi_h)]]
            ax.barh(y, ds_h, xerr=errs_h, color=colors_h, alpha=0.8,
                    edgecolor='black', capsize=4, height=0.6)
        else:
            ax.barh(y, ds_h, color=colors_h, alpha=0.8,
                    edgecolor='black', height=0.6)

        ax.axvline(0, color='gray', ls=':', lw=1)
        ax.set_yticks(y)
        ax.set_yticklabels(names_h)
        ax.set_xlabel("Cohen's d")
        ax.set_title("E. Healthy (contrôle) — d par métrique\n(effets attendus plus faibles)")
        ax.invert_yaxis()

    # F : Cohérence inter-métriques (scatter d_metric vs d_BC)
    ax = fig.add_subplot(gs[2, 1])
    d_bc = table_d[0]['d']  # Bray-Curtis comme référence
    for i, r in enumerate(table_d):
        ax.scatter(d_bc, r['d'], s=200, color=metric_colors[i % len(metric_colors)],
                   edgecolor='black', zorder=5)
        ax.annotate(r['metric'], (d_bc, r['d']),
                    textcoords='offset points', xytext=(10, 5), fontsize=9)
    lim = (0, max(r['d'] for r in table_d) * 1.3)
    ax.plot(lim, lim, 'k:', alpha=0.3, label='y = x')
    ax.set_xlabel("Cohen's d (Bray-Curtis)")
    ax.set_ylabel("Cohen's d (autre métrique)")
    ax.set_title("F. Cohérence inter-métriques")
    ax.legend(fontsize=9)

    # G : Convergence trans-domaniale (toutes métriques)
    ax = fig.add_subplot(gs[3, 0])
    # Ratios pour chaque métrique micro + ratio récifs + ratio GDSC
    micro_ratios = [r['ratio'] for r in table_d]
    reef_ratio = 1.80   # du manuscrit
    gdsc_ratio = 1.87   # GDSC2

    all_ratios = micro_ratios + [reef_ratio, gdsc_ratio]
    all_labels = metric_names + ['Récifs (GCBD)', 'Cancer (GDSC)']
    all_colors = metric_colors[:len(metric_names)] + ['#26A69A', '#AB47BC']

    x = np.arange(len(all_labels))
    bars = ax.bar(x, all_ratios, color=all_colors, alpha=0.8, edgecolor='black')
    ax.axhline(1, color='gray', ls=':', lw=1)
    ax.axhline(np.mean(all_ratios), color='red', ls='--', lw=1.5, alpha=0.7,
               label=f'Moyenne = {np.mean(all_ratios):.2f}×')
    ax.set_xticks(x)
    ax.set_xticklabels(all_labels, fontsize=8, rotation=30, ha='right')
    ax.set_ylabel("Ratio Structure / Input")
    ax.set_title("G. Convergence trans-domaniale (toutes métriques)")
    ax.legend(fontsize=9)

    # H : Tableau résumé
    ax = fig.add_subplot(gs[3, 1])
    ax.axis('off')

    n_sig = sum(1 for r in table_d if r['p'] < 0.05)
    n_strong = sum(1 for r in table_d if r['p'] < 0.001)
    all_d = [r['d'] for r in table_d]
    all_p = [r['p'] for r in table_d]

    lines = [
        "=" * 55,
        "  ROBUSTESSE R-XVII — RÉSUMÉ",
        "=" * 55, "",
        f"  Métriques testées : {len(table_d)}",
        f"  Significatives (p<0.05) : {n_sig}/{len(table_d)}",
        f"  Très significatives (p<0.001) : {n_strong}/{len(table_d)}",
        "",
        f"  Cohen's d :",
        f"    min = {min(all_d):.3f}",
        f"    max = {max(all_d):.3f}",
        f"    mean = {np.mean(all_d):.3f}",
        "",
        f"  p-values :",
        f"    min = {min(all_p):.6f}",
        f"    max = {max(all_p):.6f}",
        "",
    ]

    if n_sig == len(table_d):
        lines.append("  ★ ROBUSTE : R-XVII significatif")
        lines.append("    sous TOUTES les métriques testées.")
    elif n_sig >= len(table_d) * 0.8:
        lines.append("  ★ LARGEMENT ROBUSTE : R-XVII")
        lines.append(f"    significatif sous {n_sig}/{len(table_d)} métriques.")
    else:
        lines.append(f"  ⚠ PARTIELLEMENT ROBUSTE :")
        lines.append(f"    {n_sig}/{len(table_d)} métriques significatives.")

    ax.text(0.02, 0.98, '\n'.join(lines), transform=ax.transAxes, fontsize=11,
            va='top', fontfamily='monospace',
            bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))

    fig.savefig(str(OUTPUT_DIR / 'rXVII_robustness_metrics.png'),
                dpi=200, bbox_inches='tight', facecolor='white')
    fig.savefig(str(OUTPUT_DIR / 'rXVII_robustness_metrics.pdf'),
                bbox_inches='tight')
    plt.close()
    print(f"\n  -> {OUTPUT_DIR / 'rXVII_robustness_metrics.png'}")


# ── MAIN ────────────────────────────────────────────────────

if __name__ == "__main__":

    print("\n" + "=" * 70)
    print("  R-XVII ROBUSTESSE AUX MÉTRIQUES — MICROBIOME MDSINE2")
    print("  5 métriques de distance indépendantes")
    print("=" * 70)

    # 1. Calculer les distances
    print("\n[1/5] Distances — Cohorte dysbiotique...")
    results_d = compute_rxvii_all_metrics(u_data, "Dysbiotic")

    print("\n[2/5] Distances — Cohorte saine (contrôle)...")
    results_h = compute_rxvii_all_metrics(h_data, "Healthy")

    # 2. Tests statistiques
    print("\n[3/5] Tests statistiques...")
    table_d = test_rxvii(results_d, "Dysbiotic (test principal)")
    table_h = test_rxvii(results_h, "Healthy (contrôle)")

    # 3. Bootstrap CI
    print("\n[4/5] Bootstrap CI (10 000 tirages)...")
    print("  Dysbiotic...", end=" ", flush=True)
    boot_d = bootstrap_ci(results_d)
    print("OK")
    print("  Healthy...", end=" ", flush=True)
    boot_h = bootstrap_ci(results_h)
    print("OK")

    for m in METRICS:
        if m in boot_d:
            ci = boot_d[m]['d_ci']
            print(f"    {m:<20s} d = {boot_d[m]['d_mean']:.3f} "
                  f"IC95 [{ci[0]:.3f}, {ci[1]:.3f}]")

    # 4. Figures
    print("\n[5/5] Figures...")
    plot_robustness(table_d, table_h, boot_d, boot_h)

    # 5. Export JSON
    export = {
        'dysbiotic': table_d,
        'healthy': table_h,
        'bootstrap_dysbiotic': {
            m: {k: v for k, v in boot_d[m].items() if k != 'boot_d'}
            for m in boot_d
        },
        'bootstrap_healthy': {
            m: {k: v for k, v in boot_h[m].items() if k != 'boot_d'}
            for m in boot_h
        },
    }
    json_path = OUTPUT_DIR / 'rXVII_robustness_metrics.json'
    with open(json_path, 'w') as f:
        json.dump(export, f, indent=2)
    print(f"  -> {json_path}")

    # Résumé final
    n_sig = sum(1 for r in table_d if r['p'] < 0.05)
    print(f"""
{'='*70}
  RÉSUMÉ — ROBUSTESSE R-XVII MICROBIOME
{'='*70}

  Résultat principal (cohorte dysbiotique) :

  {'Métrique':<20s} {'d':>8s} {'IC95':>20s} {'p':>12s} {'Ratio':>8s}
  {'-'*72}""")

    for r in table_d:
        m = r['metric']
        if m in boot_d:
            ci = boot_d[m]['d_ci']
            print(f"  {m:<20s} {r['d']:8.3f} [{ci[0]:.3f}, {ci[1]:.3f}]"
                  f" {r['p']:12.6f} {r['ratio']:8.2f}x")

    print(f"""
  Significatif sous {n_sig}/{len(table_d)} métriques.

  Phrase pour le manuscrit :
  "L'asymétrie R-XVII est robuste sous cinq métriques de distance
   indépendantes (Bray-Curtis, Jensen-Shannon, Aitchison, Hellinger,
   Canberra ; tous p < [max_p], d > [min_d])."
""")