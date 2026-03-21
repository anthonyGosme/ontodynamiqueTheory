#!/usr/bin/env python3
"""
=============================================================================
R-XVII RIVAL PARTITION TEST — MDSINE2 MICROBIOME
=============================================================================
Analogue du test GDSC pour le domaine microbiome.

Avec 3 perturbations seulement (HFD, vancomycin, gentamicin), il n'y a que
3 partitions binaires possibles. On les teste toutes exhaustivement.

PARTITIONS:
  (1) ONTODYNAMIQUE: {HFD} vs {vancomycin, gentamicin}
      input (signal)   vs hardware (structure)
  (2) RIVALE A:        {vancomycin} vs {HFD, gentamicin}
      (aucune motivation théorique)
  (3) RIVALE B:        {gentamicin} vs {HFD, vancomycin}
      (aucune motivation théorique)

TESTS SUPPLÉMENTAIRES:
  - CV par sujet (stabilité intra-cohorte)
  - Contrôle par intensité (normalisation par displacement initial)
  - Bootstrap sur sujets

Usage:
  python 05_rival_partitions_mdsine2.py

Prérequis:
  - MDSINE2_Paper/ cloné (git clone https://github.com/gerberlab/MDSINE2_Paper.git)
  - mdsine2 installé (pip install mdsine2)
=============================================================================
"""

import sys, os, time, json, warnings
from pathlib import Path
import numpy as np
import pandas as pd
from scipy import stats, spatial
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec

warnings.filterwarnings('ignore')

PROJECT_ROOT = Path(__file__).resolve().parent.parent
OUTPUT_DIR = PROJECT_ROOT / 'output'
OUTPUT_DIR.mkdir(exist_ok=True)
_data_base = PROJECT_ROOT / 'MDSINE2_Paper' / 'datasets' / 'gibson'

# ── Patch llvmlite/numba ───────────────────────────────────
import types

def _patch_llvmlite():
    try:
        import llvmlite.binding
        return
    except (ImportError, OSError):
        pass
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

plt.rcParams.update({
    'font.size': 10, 'axes.titlesize': 12, 'axes.labelsize': 11,
    'figure.dpi': 150, 'savefig.dpi': 300, 'savefig.bbox': 'tight',
})


# ============================================================================
# DATA LOADING (from phase 2)
# ============================================================================

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
                'total_conc': abs_m[:, i].sum(),
            })
    return records


# ============================================================================
# R-XVII WITH GLOBAL BASELINE (from phase 2)
# ============================================================================

def compute_recovery_global_baseline(data):
    """
    Distance from GLOBAL baseline (late equilibration t=15-21.5)
    for each perturbation's recovery phase.
    Returns per-sample distances + peak perturbation displacement.
    """
    results = []
    subjects = sorted(set(r['subject'] for r in data))

    for subj in subjects:
        sdata = sorted([r for r in data if r['subject'] == subj],
                       key=lambda x: x['time'])

        # Global baseline: late equilibration
        baseline_samples = [r for r in sdata if 15 <= r['time'] < 21.5]
        if len(baseline_samples) < 3:
            continue
        baseline_rel = np.mean([r['rel_profile'] for r in baseline_samples], axis=0)
        baseline_rel = baseline_rel / (baseline_rel.sum() + 1e-15)

        # Map: recovery phase → (perturbation name, pert end time, pert phase name)
        recovery_map = {
            'recovery_1': ('HFD', 28.5, 'HFD'),
            'recovery_2': ('vancomycin', 42.5, 'vancomycin'),
            'recovery_3': ('gentamicin', 57.5, 'gentamicin'),
        }

        for phase_name, (pert_name, pert_end, pert_phase) in recovery_map.items():
            # Peak displacement during perturbation
            pert_samples = [r for r in sdata if r['phase'] == pert_phase]
            if pert_samples:
                peak_bc = max(
                    spatial.distance.braycurtis(
                        baseline_rel,
                        r['rel_profile'] / (r['rel_profile'].sum() + 1e-15)
                    )
                    for r in pert_samples
                )
            else:
                peak_bc = np.nan

            # Recovery samples
            recovery_samples = [r for r in sdata if r['phase'] == phase_name]
            for r in recovery_samples:
                profile = r['rel_profile']
                profile = profile / (profile.sum() + 1e-15)
                bc = spatial.distance.braycurtis(baseline_rel, profile)

                results.append({
                    'subject': subj,
                    'cohort': r['cohort'],
                    'perturbation': pert_name,
                    'phase': phase_name,
                    'time': r['time'],
                    'time_since_pert': r['time'] - pert_end,
                    'bc_from_baseline': bc,
                    'peak_bc': peak_bc,
                })

    return pd.DataFrame(results)


# ============================================================================
# PARTITION DEFINITIONS
# ============================================================================

# All 3 possible binary partitions of {HFD, vancomycin, gentamicin}
PARTITIONS = {
    'Ontodynamique': {
        'class_A': ['HFD'],
        'class_B': ['vancomycin', 'gentamicin'],
        'label_A': 'INPUT (HFD)',
        'label_B': 'HARDWARE (antibio)',
        'motivation': 'R-XVII: input (signal) vs structure (maintenance)',
    },
    'Rivale A': {
        'class_A': ['vancomycin'],
        'class_B': ['HFD', 'gentamicin'],
        'label_A': 'Vancomycin seul',
        'label_B': 'HFD + Gentamicin',
        'motivation': 'Gram+ ciblé vs reste (aucune motivation ontodynamique)',
    },
    'Rivale B': {
        'class_A': ['gentamicin'],
        'class_B': ['HFD', 'vancomycin'],
        'label_A': 'Gentamicin seul',
        'label_B': 'HFD + Vancomycin',
        'motivation': 'Gram- ciblé vs reste (aucune motivation ontodynamique)',
    },
}


def compute_partition_stats(rec_df, partition, late_threshold=4):
    """
    For a given partition, compute ratio, Cohen's d, p-value.
    Uses late recovery (time_since_pert >= late_threshold).
    """
    cls_a = partition['class_A']
    cls_b = partition['class_B']

    late = rec_df[rec_df['time_since_pert'] >= late_threshold]
    vals_a = late[late['perturbation'].isin(cls_a)]['bc_from_baseline'].values
    vals_b = late[late['perturbation'].isin(cls_b)]['bc_from_baseline'].values

    if len(vals_a) < 3 or len(vals_b) < 3:
        return None

    # Magnitude = mean BC (higher BC = more displacement = more damage)
    mag_a = np.mean(vals_a)
    mag_b = np.mean(vals_b)

    # Ratio: higher/lower
    if mag_a >= mag_b:
        ratio = mag_a / mag_b if mag_b > 0.001 else float('inf')
        direction = 'A>B'
    else:
        ratio = mag_b / mag_a if mag_a > 0.001 else float('inf')
        direction = 'B>A'

    # Mann-Whitney
    U, p = stats.mannwhitneyu(vals_a, vals_b, alternative='two-sided')

    # Cohen's d
    n1, n2 = len(vals_a), len(vals_b)
    pooled = np.sqrt(((n1-1)*np.var(vals_a, ddof=1) + (n2-1)*np.var(vals_b, ddof=1)) / (n1+n2-2))
    d = (np.mean(vals_b) - np.mean(vals_a)) / pooled if pooled > 0 else 0

    return {
        'n_a': n1, 'n_b': n2,
        'mean_a': float(mag_a), 'mean_b': float(mag_b),
        'ratio': float(ratio), 'direction': direction,
        'abs_d': float(abs(d)), 'd': float(d),
        'p_MW': float(p),
    }


def compute_per_subject_ratios(rec_df, partition, late_threshold=4):
    """Compute ratio per subject → CV."""
    cls_a = partition['class_A']
    cls_b = partition['class_B']
    late = rec_df[rec_df['time_since_pert'] >= late_threshold]

    ratios = []
    subjects = sorted(late['subject'].unique())

    for subj in subjects:
        s = late[late['subject'] == subj]
        vals_a = s[s['perturbation'].isin(cls_a)]['bc_from_baseline'].values
        vals_b = s[s['perturbation'].isin(cls_b)]['bc_from_baseline'].values

        if len(vals_a) < 1 or len(vals_b) < 1:
            continue

        ma, mb = np.mean(vals_a), np.mean(vals_b)
        if ma > 0.001 and mb > 0.001:
            ratio = max(ma, mb) / min(ma, mb)
            ratios.append({
                'subject': subj,
                'ratio': ratio,
                'direction': 'A>B' if ma >= mb else 'B>A',
                'mean_a': ma, 'mean_b': mb,
            })

    if len(ratios) < 2:
        return None

    arr = np.array([r['ratio'] for r in ratios])
    # Check direction consistency
    onto_direction = 'B>A'  # hardware > input (expected for ontodynamique)
    n_correct = sum(1 for r in ratios if r['direction'] == onto_direction)

    return {
        'ratios': ratios,
        'mean_ratio': float(np.mean(arr)),
        'median_ratio': float(np.median(arr)),
        'std_ratio': float(np.std(arr, ddof=1)),
        'cv_ratio': float(np.std(arr, ddof=1) / np.mean(arr) * 100) if np.mean(arr) > 0 else float('inf'),
        'n_subjects': len(ratios),
        'n_correct_direction': n_correct,
    }


def compute_intensity_normalized(rec_df, partition, late_threshold=4):
    """
    Normalize late recovery BC by peak perturbation BC.
    This controls for the objection "antibiotics just hit harder".
    Normalized displacement = late_BC / peak_BC
    """
    cls_a = partition['class_A']
    cls_b = partition['class_B']

    late = rec_df[rec_df['time_since_pert'] >= late_threshold].copy()
    late = late.dropna(subset=['peak_bc'])
    late['normalized_bc'] = late['bc_from_baseline'] / (late['peak_bc'] + 1e-10)

    vals_a = late[late['perturbation'].isin(cls_a)]['normalized_bc'].values
    vals_b = late[late['perturbation'].isin(cls_b)]['normalized_bc'].values

    if len(vals_a) < 3 or len(vals_b) < 3:
        return None

    mag_a = np.mean(vals_a)
    mag_b = np.mean(vals_b)

    if mag_a >= mag_b:
        ratio = mag_a / mag_b if mag_b > 0.001 else float('inf')
        direction = 'A>B'
    else:
        ratio = mag_b / mag_a if mag_a > 0.001 else float('inf')
        direction = 'B>A'

    U, p = stats.mannwhitneyu(vals_a, vals_b, alternative='two-sided')
    n1, n2 = len(vals_a), len(vals_b)
    pooled = np.sqrt(((n1-1)*np.var(vals_a, ddof=1) + (n2-1)*np.var(vals_b, ddof=1)) / (n1+n2-2))
    d = (np.mean(vals_b) - np.mean(vals_a)) / pooled if pooled > 0 else 0

    return {
        'n_a': n1, 'n_b': n2,
        'mean_a_norm': float(mag_a), 'mean_b_norm': float(mag_b),
        'ratio_normalized': float(ratio), 'direction': direction,
        'abs_d': float(abs(d)), 'd': float(d),
        'p_MW': float(p),
    }


def bootstrap_partition(rec_df, partition, n_boot=10000, late_threshold=4):
    """Bootstrap the ratio by resampling subjects."""
    cls_a = partition['class_A']
    cls_b = partition['class_B']
    late = rec_df[rec_df['time_since_pert'] >= late_threshold]
    subjects = sorted(late['subject'].unique())

    rng = np.random.RandomState(42)
    boot_ratios = []
    boot_d = []

    for _ in range(n_boot):
        boot_subjs = rng.choice(subjects, len(subjects), replace=True)
        boot_data = pd.concat([late[late['subject'] == s] for s in boot_subjs])

        vals_a = boot_data[boot_data['perturbation'].isin(cls_a)]['bc_from_baseline'].values
        vals_b = boot_data[boot_data['perturbation'].isin(cls_b)]['bc_from_baseline'].values

        if len(vals_a) < 2 or len(vals_b) < 2:
            continue

        ma, mb = np.mean(vals_a), np.mean(vals_b)
        if ma > 0.001 and mb > 0.001:
            ratio = max(ma, mb) / min(ma, mb)
            boot_ratios.append(ratio)

        pooled = np.sqrt((np.var(vals_a, ddof=1) + np.var(vals_b, ddof=1)) / 2)
        if pooled > 0:
            boot_d.append((np.mean(vals_b) - np.mean(vals_a)) / pooled)

    arr_r = np.array(boot_ratios)
    arr_d = np.array(boot_d)

    return {
        'mean_ratio': float(np.mean(arr_r)),
        'ci_ratio_95': [float(np.percentile(arr_r, 2.5)), float(np.percentile(arr_r, 97.5))],
        'cv_ratio': float(np.std(arr_r, ddof=1) / np.mean(arr_r) * 100),
        'mean_d': float(np.mean(arr_d)),
        'ci_d_95': [float(np.percentile(arr_d, 2.5)), float(np.percentile(arr_d, 97.5))],
    }


# ============================================================================
# MAIN
# ============================================================================

def main():
    t0 = time.time()

    print("=" * 75)
    print("  R-XVII RIVAL PARTITION TEST — MDSINE2 MICROBIOME")
    print("  3 partitions exhaustives × 2 cohortes × contrôle intensité")
    print("=" * 75)

    # Load
    h_pkl = _data_base / 'healthy' / 'preprocessed' / 'gibson_healthy_agg_filtered.pkl'
    u_pkl = _data_base / 'uc' / 'preprocessed' / 'gibson_uc_agg_filtered.pkl'

    if not h_pkl.exists() or not u_pkl.exists():
        print(f"\nERREUR: données MDSINE2 introuvables.")
        print(f"  Attendu: {h_pkl}")
        print(f"  git clone https://github.com/gerberlab/MDSINE2_Paper.git")
        sys.exit(1)

    study_h = md2.Study.load(str(h_pkl))
    study_u = md2.Study.load(str(u_pkl))

    h_data = extract_data(study_h, 'healthy')
    u_data = extract_data(study_u, 'dysbiotic')

    n_h_subj = len(set(r['subject'] for r in h_data))
    n_u_subj = len(set(r['subject'] for r in u_data))
    print(f"\n  Healthy: {len(h_data)} samples, {len(study_h.taxa)} taxa, {n_h_subj} sujets")
    print(f"  Dysbiotic: {len(u_data)} samples, {len(study_u.taxa)} taxa, {n_u_subj} sujets")

    # Compute recovery
    print(f"\n  Calcul des distances de recovery (baseline globale)...")
    h_rec = compute_recovery_global_baseline(h_data)
    u_rec = compute_recovery_global_baseline(u_data)

    print(f"  Healthy: {len(h_rec)} recovery observations")
    print(f"  Dysbiotic: {len(u_rec)} recovery observations")

    # ================================================================
    # TEST EXHAUSTIF DES 3 PARTITIONS
    # ================================================================
    for cohort_name, rec_df in [('DYSBIOTIC (test principal)', u_rec),
                                 ('HEALTHY (contrôle)', h_rec)]:
        print(f"\n{'=' * 75}")
        print(f"  {cohort_name}")
        print(f"{'=' * 75}")

        all_results = {}

        for pname, partition in PARTITIONS.items():
            print(f"\n  ── {pname} ──")
            print(f"  {partition['label_A']} vs {partition['label_B']}")
            print(f"  Motivation: {partition['motivation']}")

            # Global stats
            r = compute_partition_stats(rec_df, partition)
            if r:
                all_results[pname] = {'global': r}
                eff = "négligeable" if r['abs_d'] < 0.2 else (
                    "faible" if r['abs_d'] < 0.5 else (
                        "moyen" if r['abs_d'] < 0.8 else "FORT"))
                print(f"\n    Global:")
                print(f"      {partition['label_A']} (n={r['n_a']}): BC={r['mean_a']:.4f}")
                print(f"      {partition['label_B']} (n={r['n_b']}): BC={r['mean_b']:.4f}")
                print(f"      Ratio = {r['ratio']:.3f}× ({r['direction']})")
                print(f"      |d| = {r['abs_d']:.3f} ({eff}), p = {r['p_MW']:.4f}")

            # Per-subject CV
            ps = compute_per_subject_ratios(rec_df, partition)
            if ps:
                all_results[pname]['per_subject'] = ps
                print(f"\n    Par sujet (CV):")
                print(f"      N sujets: {ps['n_subjects']}")
                print(f"      Ratio moyen: {ps['mean_ratio']:.3f}×")
                print(f"      CV = {ps['cv_ratio']:.1f}%")
                print(f"      Direction correcte: {ps['n_correct_direction']}/{ps['n_subjects']}")
                for sr in ps['ratios']:
                    dir_mark = '✓' if sr['direction'] == 'B>A' else '✗'
                    print(f"        {sr['subject']}: ratio={sr['ratio']:.3f}× "
                          f"(A={sr['mean_a']:.4f} B={sr['mean_b']:.4f}) {dir_mark}")

            # Intensity-normalized
            inorm = compute_intensity_normalized(rec_df, partition)
            if inorm:
                all_results[pname]['intensity_norm'] = inorm
                eff = "négligeable" if inorm['abs_d'] < 0.2 else (
                    "faible" if inorm['abs_d'] < 0.5 else (
                        "moyen" if inorm['abs_d'] < 0.8 else "FORT"))
                print(f"\n    Normalisé par intensité (late_BC / peak_BC):")
                print(f"      {partition['label_A']}: {inorm['mean_a_norm']:.4f}")
                print(f"      {partition['label_B']}: {inorm['mean_b_norm']:.4f}")
                print(f"      Ratio = {inorm['ratio_normalized']:.3f}× ({inorm['direction']})")
                print(f"      |d| = {inorm['abs_d']:.3f} ({eff}), p = {inorm['p_MW']:.4f}")

            # Bootstrap CI
            boot = bootstrap_partition(rec_df, partition)
            if boot:
                all_results[pname]['bootstrap'] = boot
                print(f"\n    Bootstrap (10k, resample sujets):")
                print(f"      Ratio: {boot['mean_ratio']:.3f}× "
                      f"IC95 [{boot['ci_ratio_95'][0]:.3f}, {boot['ci_ratio_95'][1]:.3f}]")
                print(f"      d: {boot['mean_d']:.3f} "
                      f"IC95 [{boot['ci_d_95'][0]:.3f}, {boot['ci_d_95'][1]:.3f}]")

        # ── Summary table ──
        print(f"\n  {'─' * 70}")
        print(f"  RÉSUMÉ {cohort_name}")
        print(f"  {'─' * 70}")
        print(f"  {'Partition':<18s} {'Ratio':>7s} {'|d|':>6s} {'p':>8s} "
              f"{'CV%':>6s} {'R_norm':>7s} {'p_norm':>8s}")
        print(f"  {'─'*18} {'─'*7} {'─'*6} {'─'*8} {'─'*6} {'─'*7} {'─'*8}")

        for pname in PARTITIONS:
            if pname not in all_results:
                continue
            ar = all_results[pname]
            g = ar.get('global', {})
            ps = ar.get('per_subject', {})
            inorm = ar.get('intensity_norm', {})

            ratio = g.get('ratio', 0)
            d = g.get('abs_d', 0)
            p = g.get('p_MW', 1)
            cv = ps.get('cv_ratio', float('inf'))
            r_norm = inorm.get('ratio_normalized', 0)
            p_norm = inorm.get('p_MW', 1)

            sig = '***' if p < 0.001 else ('**' if p < 0.01 else ('*' if p < 0.05 else ' '))
            sig_n = '***' if p_norm < 0.001 else ('**' if p_norm < 0.01 else ('*' if p_norm < 0.05 else ' '))

            print(f"  {pname:<18s} {ratio:>6.3f}× {d:>6.3f} {p:>7.4f}{sig} "
                  f"{cv:>5.1f}% {r_norm:>6.3f}× {p_norm:>7.4f}{sig_n}")

    # ================================================================
    # VISUALIZATION
    # ================================================================
    print(f"\n{'=' * 75}")
    print(f"  FIGURES")
    print(f"{'=' * 75}")

    fig, axes = plt.subplots(2, 3, figsize=(18, 11))
    fig.suptitle('R-XVII Rival Partition Test — MDSINE2 Microbiome\n'
                 '3 partitions exhaustives × contrôle intensité',
                 fontsize=13, fontweight='bold')
    C_ONTO = '#1565C0'
    C_RA = '#6A1B9A'
    C_RB = '#E65100'
    colors = {'Ontodynamique': C_ONTO, 'Rivale A': C_RA, 'Rivale B': C_RB}

    # Panel 1: Ratio comparison — Dysbiotic
    ax = axes[0, 0]
    names = list(PARTITIONS.keys())
    for cohort_label, rec_df, row in [('Dysbiotic', u_rec, 0), ('Healthy', h_rec, 1)]:
        ax = axes[row, 0]
        ratios_raw = []
        ratios_norm = []
        for pname in names:
            r = compute_partition_stats(rec_df, PARTITIONS[pname])
            inorm = compute_intensity_normalized(rec_df, PARTITIONS[pname])
            ratios_raw.append(r['ratio'] if r else 0)
            ratios_norm.append(inorm['ratio_normalized'] if inorm else 0)

        x = np.arange(len(names))
        w = 0.35
        ax.bar(x - w/2, ratios_raw, w, color=[colors[n] for n in names],
               alpha=0.8, label='Brut', edgecolor='black')
        ax.bar(x + w/2, ratios_norm, w, color=[colors[n] for n in names],
               alpha=0.4, label='Norm. intensité', edgecolor='black', hatch='//')
        ax.axhline(1.0, color='gray', ls=':', lw=1)
        ax.set_xticks(x)
        ax.set_xticklabels(names, fontsize=9)
        ax.set_ylabel('Ratio')
        ax.set_title(f'{cohort_label}: Ratio par partition')
        ax.legend(fontsize=8)
        for i, (rr, rn) in enumerate(zip(ratios_raw, ratios_norm)):
            ax.text(i - w/2, rr + 0.02, f'{rr:.2f}', ha='center', fontsize=8, fontweight='bold')

    # Panel 2: Per-subject ratios — Dysbiotic
    for cohort_label, rec_df, row in [('Dysbiotic', u_rec, 0), ('Healthy', h_rec, 1)]:
        ax = axes[row, 1]
        for i, pname in enumerate(names):
            ps = compute_per_subject_ratios(rec_df, PARTITIONS[pname])
            if ps:
                subj_ratios = [r['ratio'] for r in ps['ratios']]
                jitter = np.random.RandomState(i).normal(0, 0.05, len(subj_ratios))
                ax.scatter([i] * len(subj_ratios) + jitter, subj_ratios,
                           color=colors[pname], alpha=0.7, s=80, edgecolor='black', zorder=5)
                ax.errorbar(i, np.mean(subj_ratios), yerr=np.std(subj_ratios),
                            color=colors[pname], capsize=6, capthick=2, lw=2, zorder=10)
        ax.axhline(1.0, color='gray', ls=':', lw=1)
        ax.set_xticks(range(len(names)))
        ax.set_xticklabels(names, fontsize=9)
        ax.set_ylabel('Ratio par sujet')
        ax.set_title(f'{cohort_label}: Variabilité inter-sujets')

    # Panel 3: Bootstrap CI — Dysbiotic
    for cohort_label, rec_df, row in [('Dysbiotic', u_rec, 0), ('Healthy', h_rec, 1)]:
        ax = axes[row, 2]
        for i, pname in enumerate(names):
            boot = bootstrap_partition(rec_df, PARTITIONS[pname], n_boot=5000)
            if boot:
                ci = boot['ci_ratio_95']
                ax.barh(i, boot['mean_ratio'], color=colors[pname], alpha=0.7,
                        edgecolor='black', height=0.5)
                ax.errorbar(boot['mean_ratio'], i,
                            xerr=[[boot['mean_ratio'] - ci[0]], [ci[1] - boot['mean_ratio']]],
                            color='black', capsize=5, capthick=2, lw=1.5)
                ax.text(ci[1] + 0.05, i, f"{boot['mean_ratio']:.2f}×\n[{ci[0]:.2f}, {ci[1]:.2f}]",
                        va='center', fontsize=8)
        ax.axvline(1.0, color='gray', ls=':', lw=1)
        ax.set_yticks(range(len(names)))
        ax.set_yticklabels(names, fontsize=9)
        ax.set_xlabel('Ratio (bootstrap IC95)')
        ax.set_title(f'{cohort_label}: Bootstrap CI')

    plt.tight_layout()
    fig_path = OUTPUT_DIR / 'rXVII_rival_partitions_mdsine2.png'
    plt.savefig(fig_path, dpi=200, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"  → {fig_path}")

    # ================================================================
    # EXPORT JSON
    # ================================================================
    # Recompute all for export
    export = {'protocol': 'R-XVII rival partition test — MDSINE2'}
    for cohort_label, rec_df in [('dysbiotic', u_rec), ('healthy', h_rec)]:
        export[cohort_label] = {}
        for pname, partition in PARTITIONS.items():
            g = compute_partition_stats(rec_df, partition)
            ps = compute_per_subject_ratios(rec_df, partition)
            inorm = compute_intensity_normalized(rec_df, partition)
            boot = bootstrap_partition(rec_df, partition, n_boot=5000)
            export[cohort_label][pname] = {
                'global': g,
                'per_subject': {k: v for k, v in (ps or {}).items() if k != 'ratios'},
                'intensity_normalized': inorm,
                'bootstrap': boot,
            }

    def nc(o):
        if isinstance(o, (np.integer,)): return int(o)
        if isinstance(o, (np.floating,)): return float(o)
        if isinstance(o, np.ndarray): return o.tolist()
        if isinstance(o, np.bool_): return bool(o)
        raise TypeError(f"{type(o)}")

    json_path = OUTPUT_DIR / 'rXVII_rival_partitions_mdsine2.json'
    with open(json_path, 'w') as f:
        json.dump(export, f, indent=2, default=nc)
    print(f"  → {json_path}")

    # ================================================================
    # VERDICT
    # ================================================================
    print(f"\n{'=' * 75}")
    print(f"  VERDICT")
    print(f"{'=' * 75}")

    # Dysbiotic cohort results
    onto_r = compute_partition_stats(u_rec, PARTITIONS['Ontodynamique'])
    ra_r = compute_partition_stats(u_rec, PARTITIONS['Rivale A'])
    rb_r = compute_partition_stats(u_rec, PARTITIONS['Rivale B'])
    onto_norm = compute_intensity_normalized(u_rec, PARTITIONS['Ontodynamique'])

    if onto_r and ra_r and rb_r:
        print(f"\n  Cohorte dysbiotique (test principal):")
        print(f"    Ontodynamique: ratio={onto_r['ratio']:.3f}×, |d|={onto_r['abs_d']:.3f}, p={onto_r['p_MW']:.4f}")
        print(f"    Rivale A:      ratio={ra_r['ratio']:.3f}×, |d|={ra_r['abs_d']:.3f}, p={ra_r['p_MW']:.4f}")
        print(f"    Rivale B:      ratio={rb_r['ratio']:.3f}×, |d|={rb_r['abs_d']:.3f}, p={rb_r['p_MW']:.4f}")

        if onto_norm:
            print(f"\n  Contrôle intensité (ontodynamique):")
            print(f"    Ratio normalisé = {onto_norm['ratio_normalized']:.3f}×, "
                  f"|d|={onto_norm['abs_d']:.3f}, p={onto_norm['p_MW']:.4f}")

        # Verdict logic
        onto_sig = onto_r['p_MW'] < 0.05
        rivals_sig = ra_r['p_MW'] < 0.05 or rb_r['p_MW'] < 0.05
        onto_best = onto_r['ratio'] > max(ra_r['ratio'], rb_r['ratio'])
        norm_sig = onto_norm and onto_norm['p_MW'] < 0.05

        if onto_sig and onto_best and not rivals_sig:
            print(f"\n  ★ RÉSULTAT FORT: seule la partition ontodynamique est significative.")
            print(f"    Les deux rivales ne produisent pas d'asymétrie comparable.")
            if norm_sig:
                print(f"    L'effet survit au contrôle d'intensité.")
        elif onto_sig and onto_best:
            print(f"\n  ★ RÉSULTAT MODÉRÉ: la partition ontodynamique donne le ratio")
            print(f"    le plus élevé, mais une rivale est aussi significative.")
        elif onto_sig:
            print(f"\n  ★ RÉSULTAT MIXTE: la partition ontodynamique est significative")
            print(f"    mais n'a pas le ratio le plus élevé.")
        else:
            print(f"\n  ★ RÉSULTAT NÉGATIF: la partition ontodynamique n'est pas")
            print(f"    significative dans cette cohorte.")

    elapsed = time.time() - t0
    print(f"\n  Temps: {elapsed:.1f}s")


if __name__ == '__main__':
    main()