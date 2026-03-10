#!/usr/bin/env python3
"""
R-XVII Robustesse aux transformations — Récifs coralliens (GCBD)
================================================================
Refait les tests R-XVII principaux avec 4 transformations du
bleaching % pour vérifier que d=0.39 et le seuil sigmoïde DHW≈8
ne dépendent pas du choix d'échelle.

Transformations :
  1. Brut (%)           — référence, résultat publié
  2. Arcsin-sqrt        — standard pour proportions (Sokal & Rohlf)
  3. Log(1+x)           — compresse la queue droite
  4. Binaire ≥ 25%      — seuil de sévérité (indépendant de l'échelle)

Usage :  python 05_robustness_reef.py
Prérequis : global_bleaching_environmental.csv dans ../data/ ou ./
"""

import sys
from pathlib import Path
import numpy as np
import pandas as pd
from scipy import stats, optimize
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
import warnings, json
warnings.filterwarnings('ignore')

plt.rcParams.update({
    'font.size': 10, 'axes.titlesize': 12, 'axes.labelsize': 11,
    'figure.dpi': 150, 'savefig.dpi': 300, 'savefig.bbox': 'tight',
})

# ── Chemins ─────────────────────────────────────────────────
SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
OUTPUT_DIR = PROJECT_ROOT / 'output'
OUTPUT_DIR.mkdir(exist_ok=True)

# Chercher le CSV dans plusieurs emplacements possibles
_candidates = [
    SCRIPT_DIR / 'global_bleaching_environmental.csv',
    PROJECT_ROOT / 'data' / 'global_bleaching_environmental.csv',
    PROJECT_ROOT / 'global_bleaching_environmental.csv',
    SCRIPT_DIR.parent / 'data' / 'global_bleaching_environmental.csv',
]
CSV_PATH = None
for c in _candidates:
    if c.exists():
        CSV_PATH = c
        break

if CSV_PATH is None:
    print("ERREUR : global_bleaching_environmental.csv introuvable.")
    print("  Cherché dans :", [str(c) for c in _candidates])
    sys.exit(1)


# ── Chargement et classification ────────────────────────────

print(f"Chargement : {CSV_PATH}")
df = pd.read_csv(CSV_PATH)

# Colonnes attendues (van Woesik & Kratochwill 2022)
# Essayer plusieurs noms possibles
bleach_col = None
for col in ['Percent_Bleaching', 'percent_bleaching', 'Bleaching_Percentage',
            'bleaching_percent', 'Percent_Bleached']:
    if col in df.columns:
        bleach_col = col
        break
if bleach_col is None:
    # Chercher par pattern
    for col in df.columns:
        if 'bleach' in col.lower() and 'percent' in col.lower():
            bleach_col = col
            break
if bleach_col is None:
    print("ERREUR : colonne de bleaching % introuvable.")
    print("  Colonnes disponibles :", list(df.columns))
    sys.exit(1)

dhw_col = None
for col in ['DHW_Max', 'DHW', 'Degree_Heating_Weeks', 'dhw_max',
            'Temperature_DHW', 'ClimSST_DHW']:
    if col in df.columns:
        dhw_col = col
        break
if dhw_col is None:
    for col in df.columns:
        if 'dhw' in col.lower():
            dhw_col = col
            break
if dhw_col is None:
    print("ERREUR : colonne DHW introuvable.")
    print("  Colonnes disponibles :", list(df.columns))
    sys.exit(1)

cyclone_col = None
for col in ['Cyclone_Frequency', 'cyclone_frequency', 'Cyclone_Freq',
            'cyclone_freq', 'SSTA_Frequency_Standard_Deviation']:
    if col in df.columns:
        cyclone_col = col
        break
if cyclone_col is None:
    for col in df.columns:
        if 'cyclone' in col.lower() or 'storm' in col.lower():
            cyclone_col = col
            break

print(f"  Bleaching : {bleach_col}")
print(f"  DHW       : {dhw_col}")
print(f"  Cyclone   : {cyclone_col or 'non trouvé (DHW seul)'}")

# Nettoyage
df = df.dropna(subset=[bleach_col, dhw_col])
df['bleach_raw'] = pd.to_numeric(df[bleach_col], errors='coerce')
df = df.dropna(subset=['bleach_raw'])
df['bleach_raw'] = df['bleach_raw'].clip(0, 100)
df['dhw'] = pd.to_numeric(df[dhw_col], errors='coerce')
df = df.dropna(subset=['bleach_raw', 'dhw'])

if cyclone_col and cyclone_col in df.columns:
    df['cyclone'] = pd.to_numeric(df[cyclone_col], errors='coerce').fillna(0)
    cyclone_median = df.loc[df['cyclone'] > 0, 'cyclone'].median() if (df['cyclone'] > 0).any() else 999
else:
    df['cyclone'] = 0
    cyclone_median = 999  # désactive le critère cyclone


def classify(row):
    """Classification R-XVII propre — alignée sur rXVII_reef_CLEAN.py."""
    dhw = row['dhw']
    cyc = row['cyclone']
    # Structure en priorité (comme dans l'original : appliqué en dernier, écrase)
    if (dhw >= 8) or (cyc > cyclone_median * 1.5):
        return 'STRUCTURE'
    elif (dhw >= 4) and (dhw < 8) and (cyc <= cyclone_median):
        return 'INPUT'
    else:
        return 'BASELINE'


df['class'] = df.apply(classify, axis=1)
n_base = (df['class'] == 'BASELINE').sum()
n_inp = (df['class'] == 'INPUT').sum()
n_str = (df['class'] == 'STRUCTURE').sum()
print(f"  Classification : BASELINE={n_base}, INPUT={n_inp}, STRUCTURE={n_str}")
print(f"  Total : {len(df)} observations")

# Sous-ensembles
df_inp = df[df['class'] == 'INPUT']
df_str = df[df['class'] == 'STRUCTURE']


# ── Transformations ─────────────────────────────────────────

def arcsin_sqrt(x):
    """Arcsin-sqrt : transformation standard pour proportions (Sokal & Rohlf 1995)."""
    return np.arcsin(np.sqrt(x / 100.0))

def log1p(x):
    """Log(1+x) : compresse la queue droite."""
    return np.log1p(x)

def binary_25(x):
    """Seuil de sévérité ≥ 25% : binaire, indépendant de l'échelle."""
    return (x >= 25).astype(float)


TRANSFORMS = {
    'Brut (%)': lambda x: x,
    'Arcsin-sqrt': arcsin_sqrt,
    'Log(1+x)': log1p,
    'Binaire ≥25%': binary_25,
}


# ── Test 1 : Asymétrie R-XVII sous chaque transformation ───

def test_asymmetry(inp_vals, str_vals, label, is_binary=False):
    """Mann-Whitney + Cohen's d."""
    if is_binary:
        # Pour les données binaires : test de proportion (Fisher exact ou chi²)
        n_inp_pos = inp_vals.sum()
        n_str_pos = str_vals.sum()
        n_inp = len(inp_vals)
        n_str = len(str_vals)
        # Chi² test
        table = np.array([[n_inp_pos, n_inp - n_inp_pos],
                          [n_str_pos, n_str - n_str_pos]])
        chi2, p_chi, _, _ = stats.chi2_contingency(table)
        # Effect size : odds ratio
        p1 = n_inp_pos / n_inp
        p2 = n_str_pos / n_str
        # Cohen's h (effect size for proportions)
        h = 2 * (np.arcsin(np.sqrt(p2)) - np.arcsin(np.sqrt(p1)))
        ratio = p2 / p1 if p1 > 0 else np.nan
        return {
            'p': float(p_chi),
            'd': float(h),
            'input_mean': float(p1),
            'str_mean': float(p2),
            'ratio': float(ratio),
            'test': 'chi²',
        }
    else:
        U, p = stats.mannwhitneyu(str_vals, inp_vals, alternative='greater')
        pooled = np.sqrt((np.var(str_vals) + np.var(inp_vals)) / 2)
        d = (np.mean(str_vals) - np.mean(inp_vals)) / pooled if pooled > 0 else 0
        ratio = np.mean(str_vals) / np.mean(inp_vals) if np.mean(inp_vals) > 1e-10 else np.nan
        return {
            'p': float(p),
            'd': float(d),
            'input_mean': float(np.mean(inp_vals)),
            'str_mean': float(np.mean(str_vals)),
            'ratio': float(ratio),
            'test': 'Mann-Whitney',
        }


# ── Test 2 : Sigmoïde dose-réponse sous chaque transformation ──

def fit_sigmoid(dhw_vals, response_vals, is_binary=False):
    """Fit sigmoïde : y = L / (1 + exp(-k*(x - x0))) + b"""
    try:
        if is_binary:
            # Logistic regression pour données binaires
            from scipy.special import expit
            # Bin par DHW pour ajustement
            bins = np.arange(0, dhw_vals.max() + 1, 0.5)
            dig = np.digitize(dhw_vals, bins)
            bin_means = []
            bin_dhw = []
            for i in range(1, len(bins)):
                mask = dig == i
                if mask.sum() >= 10:
                    bin_means.append(response_vals[mask].mean())
                    bin_dhw.append((bins[i-1] + bins[i]) / 2)
            if len(bin_dhw) < 4:
                return None
            bin_dhw = np.array(bin_dhw)
            bin_means = np.array(bin_means)
            dhw_fit = bin_dhw
            resp_fit = bin_means
        else:
            dhw_fit = dhw_vals
            resp_fit = response_vals

        def sigmoid(x, L, k, x0, b):
            return L / (1 + np.exp(-k * (x - x0))) + b

        # Bounds et p0 adaptatifs
        y_max = np.max(resp_fit)
        y_min = np.min(resp_fit)
        p0 = [y_max - y_min, 0.5, 8.0, y_min]
        bounds = ([0, 0.01, 1, -y_max], [y_max * 2, 5, 20, y_max])

        popt, pcov = optimize.curve_fit(sigmoid, dhw_fit, resp_fit,
                                        p0=p0, bounds=bounds, maxfev=10000)

        y_pred_sig = sigmoid(dhw_fit, *popt)
        ss_res_sig = np.sum((resp_fit - y_pred_sig) ** 2)
        ss_tot = np.sum((resp_fit - np.mean(resp_fit)) ** 2)
        r2_sig = 1 - ss_res_sig / ss_tot if ss_tot > 0 else 0

        # Comparaison linéaire
        slope, intercept, _, _, _ = stats.linregress(dhw_fit, resp_fit)
        y_pred_lin = slope * dhw_fit + intercept
        ss_res_lin = np.sum((resp_fit - y_pred_lin) ** 2)
        r2_lin = 1 - ss_res_lin / ss_tot if ss_tot > 0 else 0

        # AIC (n paramètres : sigmoïde=4, linéaire=2)
        n = len(resp_fit)
        aic_sig = n * np.log(ss_res_sig / n + 1e-15) + 2 * 4
        aic_lin = n * np.log(ss_res_lin / n + 1e-15) + 2 * 2
        delta_aic = aic_lin - aic_sig  # positif = sigmoïde meilleure

        return {
            'midpoint': float(popt[2]),
            'k': float(popt[1]),
            'r2_sigmoid': float(r2_sig),
            'r2_linear': float(r2_lin),
            'delta_aic': float(delta_aic),
            'sigmoid_better': bool(delta_aic > 0),
        }
    except (RuntimeError, ValueError, TypeError) as e:
        return None


# ── Test 3 : Bootstrap CI ───────────────────────────────────

def bootstrap_d(inp_vals, str_vals, n_boot=10000, seed=42, is_binary=False):
    rng = np.random.RandomState(seed)
    boot_d = np.zeros(n_boot)
    for b in range(n_boot):
        bi = rng.choice(inp_vals, len(inp_vals), replace=True)
        bs = rng.choice(str_vals, len(str_vals), replace=True)
        if is_binary:
            p1 = bi.mean()
            p2 = bs.mean()
            boot_d[b] = 2 * (np.arcsin(np.sqrt(max(p2, 1e-10))) -
                             np.arcsin(np.sqrt(max(p1, 1e-10))))
        else:
            pooled = np.sqrt((np.var(bi) + np.var(bs)) / 2)
            boot_d[b] = (np.mean(bs) - np.mean(bi)) / pooled if pooled > 0 else 0
    return {
        'd_mean': float(np.mean(boot_d)),
        'd_ci': (float(np.percentile(boot_d, 2.5)),
                 float(np.percentile(boot_d, 97.5))),
        'boot_d': boot_d,
    }


# ── MAIN ────────────────────────────────────────────────────

if __name__ == "__main__":

    print("\n" + "=" * 70)
    print("  R-XVII ROBUSTESSE AUX TRANSFORMATIONS — RÉCIFS (GCBD)")
    print("  4 transformations du bleaching %")
    print("=" * 70)

    all_results = []

    for t_name, t_fn in TRANSFORMS.items():
        is_bin = (t_name == 'Binaire ≥25%')
        inp_t = t_fn(df_inp['bleach_raw'].values)
        str_t = t_fn(df_str['bleach_raw'].values)

        # Test asymétrie
        asym = test_asymmetry(inp_t, str_t, t_name, is_binary=is_bin)

        # Sigmoïde (sur tout le dataset, pas juste input/structure)
        all_dhw = df['dhw'].values
        all_resp = t_fn(df['bleach_raw'].values)
        sig = fit_sigmoid(all_dhw, all_resp, is_binary=is_bin)

        # Bootstrap
        boot = bootstrap_d(inp_t, str_t, is_binary=is_bin)

        result = {
            'transform': t_name,
            **asym,
            'boot_d_mean': boot['d_mean'],
            'boot_d_ci': boot['d_ci'],
            'sigmoid': sig,
            'n_input': len(inp_t),
            'n_structure': len(str_t),
        }
        all_results.append(result)

    # ── Affichage ───────────────────────────────────────────

    print(f"\n{'='*70}")
    print(f"  ASYMÉTRIE R-XVII")
    print(f"{'='*70}")
    print(f"\n  {'Transform.':<16s} {'Input':>10s} {'Structure':>10s} "
          f"{'p':>12s} {'d':>8s} {'IC95':>20s} {'Ratio':>8s}")
    print("  " + "-" * 88)

    for r in all_results:
        ci = r['boot_d_ci']
        sig = "***" if r['p'] < 0.001 else "**" if r['p'] < 0.01 else "*" if r['p'] < 0.05 else "ns"
        print(f"  {r['transform']:<16s} {r['input_mean']:10.4f} {r['str_mean']:10.4f} "
              f"{r['p']:12.2e} {r['d']:8.3f} [{ci[0]:.3f}, {ci[1]:.3f}] "
              f"{r['ratio']:8.2f}x  {sig}")

    print(f"\n{'='*70}")
    print(f"  SIGMOÏDE DOSE-RÉPONSE")
    print(f"{'='*70}")
    print(f"\n  {'Transform.':<16s} {'Midpoint':>10s} {'R² sig':>10s} {'R² lin':>10s} "
          f"{'ΔAIC':>10s} {'Meilleur':>12s}")
    print("  " + "-" * 72)

    for r in all_results:
        s = r['sigmoid']
        if s:
            best = "Sigmoïde" if s['sigmoid_better'] else "Linéaire"
            print(f"  {r['transform']:<16s} {s['midpoint']:10.1f} {s['r2_sigmoid']:10.4f} "
                  f"{s['r2_linear']:10.4f} {s['delta_aic']:10.1f} {best:>12s}")
        else:
            print(f"  {r['transform']:<16s}  {'(échec fit)':>50s}")

    # ── Figure ──────────────────────────────────────────────

    fig = plt.figure(figsize=(18, 14))
    gs = gridspec.GridSpec(3, 2, hspace=0.4, wspace=0.3)
    fig.suptitle("R-XVII Robustesse aux transformations — Récifs coralliens (GCBD)\n"
                 "Le résultat tient-il sous 4 transformations du bleaching % ?",
                 fontsize=14, fontweight='bold', y=0.995)

    # A : Forest plot d
    ax = fig.add_subplot(gs[0, 0])
    names = [r['transform'] for r in all_results]
    ds = [r['d'] for r in all_results]
    ci_lo = [r['boot_d_ci'][0] for r in all_results]
    ci_hi = [r['boot_d_ci'][1] for r in all_results]
    y = np.arange(len(names))
    errs = [[d - lo for d, lo in zip(ds, ci_lo)],
            [hi - d for d, hi in zip(ds, ci_hi)]]
    colors = ['#4CAF50' if r['p'] < 0.001 else '#FF9800' if r['p'] < 0.05 else '#9E9E9E'
              for r in all_results]
    ax.barh(y, ds, xerr=errs, color=colors, alpha=0.8, edgecolor='black',
            capsize=4, height=0.6)
    ax.axvline(0, color='gray', ls=':', lw=1)
    ax.set_yticks(y)
    ax.set_yticklabels(names)
    ax.set_xlabel("Effect size (Cohen's d / h)")
    ax.set_title("A. Effect size par transformation\n(vert = p<0.001)")
    ax.invert_yaxis()

    # B : Ratios
    ax = fig.add_subplot(gs[0, 1])
    ratios = [r['ratio'] for r in all_results]
    ax.barh(y, ratios, color=colors, alpha=0.8, edgecolor='black', height=0.6)
    ax.axvline(1, color='gray', ls=':', lw=1, label='ratio = 1')
    ax.axvline(1.80, color='#7B1FA2', ls='--', lw=2, alpha=0.7,
               label='Publié (1.80×)')
    ax.set_yticks(y)
    ax.set_yticklabels(names)
    ax.set_xlabel("Ratio Structure / Input")
    ax.set_title("B. Ratio par transformation")
    ax.legend(fontsize=9)
    ax.invert_yaxis()

    # C : Dose-réponse sigmoïdes superposées
    ax = fig.add_subplot(gs[1, 0])
    dhw_range = np.linspace(0, 20, 200)
    t_colors = ['#2196F3', '#4CAF50', '#FF9800', '#9C27B0']

    for i, (t_name, t_fn) in enumerate(TRANSFORMS.items()):
        s = all_results[i]['sigmoid']
        if s and t_name != 'Binaire ≥25%':
            def sigmoid(x, L, k, x0, b):
                return L / (1 + np.exp(-k * (x - x0))) + b
            # Re-fit pour récupérer les paramètres
            all_resp = t_fn(df['bleach_raw'].values)
            try:
                p0 = [np.max(all_resp), 0.5, 8.0, np.min(all_resp)]
                bounds = ([0, 0.01, 1, -np.max(all_resp)],
                          [np.max(all_resp)*2, 5, 20, np.max(all_resp)])
                popt, _ = optimize.curve_fit(sigmoid, df['dhw'].values, all_resp,
                                            p0=p0, bounds=bounds, maxfev=10000)
                y_pred = sigmoid(dhw_range, *popt)
                # Normaliser pour comparabilité
                y_norm = (y_pred - y_pred.min()) / (y_pred.max() - y_pred.min() + 1e-10)
                ax.plot(dhw_range, y_norm, color=t_colors[i], lw=2,
                        label=f"{t_name} (mid={popt[2]:.1f})")
            except:
                pass

    ax.axvline(8, color='red', ls=':', lw=1.5, alpha=0.7, label='NOAA Alert 2 (DHW=8)')
    ax.set_xlabel("DHW")
    ax.set_ylabel("Réponse normalisée [0,1]")
    ax.set_title("C. Sigmoïdes dose-réponse (normalisées)")
    ax.legend(fontsize=8)

    # D : Bootstrap distributions
    ax = fig.add_subplot(gs[1, 1])
    for i, r in enumerate(all_results):
        # Re-bootstrap pour le plot
        is_bin = (r['transform'] == 'Binaire ≥25%')
        t_fn = list(TRANSFORMS.values())[i]
        inp_t = t_fn(df_inp['bleach_raw'].values)
        str_t = t_fn(df_str['bleach_raw'].values)
        boot = bootstrap_d(inp_t, str_t, n_boot=5000, is_binary=is_bin)
        ax.hist(boot['boot_d'], bins=50, alpha=0.35, color=t_colors[i],
                density=True, label=r['transform'])
    ax.axvline(0, color='gray', ls=':', lw=1)
    ax.set_xlabel("Effect size (bootstrap)")
    ax.set_ylabel("Densité")
    ax.set_title("D. Distributions bootstrap")
    ax.legend(fontsize=8)

    # E : Convergence avec microbiome
    ax = fig.add_subplot(gs[2, 0])
    # Ratios récifs (toutes transfo) + ratios microbiome (du script 04)
    reef_ratios = [r['ratio'] for r in all_results if r['transform'] != 'Binaire ≥25%']
    reef_labels = [r['transform'] for r in all_results if r['transform'] != 'Binaire ≥25%']
    # Microbiome : résultats du script 04 (connus)
    micro_ratios = [1.61, 1.62, 1.33, 1.68, 1.39]
    micro_labels = ['BC', 'JS', 'Ait', 'Hel', 'Can']

    all_r = reef_ratios + micro_ratios
    all_l = [f"Récif\n{l}" for l in reef_labels] + [f"Micro\n{l}" for l in micro_labels]
    all_c = ['#26A69A'] * len(reef_ratios) + ['#AB47BC'] * len(micro_ratios)

    x = np.arange(len(all_l))
    ax.bar(x, all_r, color=all_c, alpha=0.8, edgecolor='black')
    ax.axhline(1, color='gray', ls=':', lw=1)
    ax.axhline(np.mean(all_r), color='red', ls='--', lw=1.5,
               label=f'Moyenne = {np.mean(all_r):.2f}×')
    ax.set_xticks(x)
    ax.set_xticklabels(all_l, fontsize=7, rotation=30, ha='right')
    ax.set_ylabel("Ratio Structure / Input")
    ax.set_title("E. Convergence trans-domaniale (toutes métriques/transformations)")
    ax.legend(fontsize=9)

    # F : Résumé
    ax = fig.add_subplot(gs[2, 1])
    ax.axis('off')

    n_sig = sum(1 for r in all_results if r['p'] < 0.05)
    n_strong = sum(1 for r in all_results if r['p'] < 0.001)
    sig_results = [r for r in all_results if r['sigmoid'] is not None]
    midpoints = [r['sigmoid']['midpoint'] for r in sig_results if r['sigmoid']]
    n_sig_better = sum(1 for r in sig_results
                       if r['sigmoid'] and r['sigmoid']['sigmoid_better'])

    lines = [
        "=" * 55,
        "  ROBUSTESSE R-XVII RÉCIFS — RÉSUMÉ",
        "=" * 55, "",
        f"  Transformations testées : {len(all_results)}",
        f"  Significatives (p<0.05) : {n_sig}/{len(all_results)}",
        f"  Très significatives (p<0.001) : {n_strong}/{len(all_results)}",
        "",
        f"  Sigmoïde > linéaire : {n_sig_better}/{len(sig_results)}",
        f"  Midpoints : {', '.join(f'{m:.1f}' for m in midpoints)}",
        f"  Midpoint moyen : {np.mean(midpoints):.1f}" if midpoints else "",
        "",
    ]

    if n_sig == len(all_results):
        lines.append("  ★ ROBUSTE : R-XVII significatif")
        lines.append("    sous TOUTES les transformations.")
    else:
        lines.append(f"  ⚠ {n_sig}/{len(all_results)} significatives.")

    ax.text(0.02, 0.98, '\n'.join(lines), transform=ax.transAxes, fontsize=11,
            va='top', fontfamily='monospace',
            bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))

    fig.savefig(str(OUTPUT_DIR / 'rXVII_robustness_reef.png'),
                dpi=200, bbox_inches='tight', facecolor='white')
    fig.savefig(str(OUTPUT_DIR / 'rXVII_robustness_reef.pdf'),
                bbox_inches='tight')
    plt.close()
    print(f"\n  -> {OUTPUT_DIR / 'rXVII_robustness_reef.png'}")

    # Export JSON
    export = []
    for r in all_results:
        entry = {k: v for k, v in r.items()}
        export.append(entry)
    json_path = OUTPUT_DIR / 'rXVII_robustness_reef.json'
    with open(json_path, 'w') as f:
        json.dump(export, f, indent=2, default=str)
    print(f"  -> {json_path}")

    # Résumé final
    print(f"""
{'='*70}
  RÉSUMÉ — ROBUSTESSE R-XVII RÉCIFS
{'='*70}

  {'Transform.':<16s} {'d':>8s} {'IC95':>20s} {'p':>12s} {'Ratio':>8s} {'Midpoint':>10s}
  {'-'*78}""")

    for r in all_results:
        ci = r['boot_d_ci']
        mid = f"{r['sigmoid']['midpoint']:.1f}" if r['sigmoid'] else "—"
        print(f"  {r['transform']:<16s} {r['d']:8.3f} [{ci[0]:.3f}, {ci[1]:.3f}] "
              f"{r['p']:12.2e} {r['ratio']:8.2f}x {mid:>10s}")

    print(f"""
  Significatif sous {n_sig}/{len(all_results)} transformations.
  Midpoint sigmoïde stable autour de DHW ≈ {np.mean(midpoints):.1f} (± {np.std(midpoints):.1f}).

  Phrase pour le manuscrit :
  "L'asymétrie R-XVII est robuste sous quatre transformations de
   la variable de réponse (brut, arcsin-sqrt, log, binaire ;
   tous p < [max_p]). Le seuil sigmoïde est stable
   (DHW = {np.mean(midpoints):.1f} ± {np.std(midpoints):.1f})."
""")