#!/usr/bin/env python3
"""
CR-02 PARTIE A — Split temporel GCBD (récifs coralliens)
=========================================================

Transforme la rétrodiction R-XVII en quasi-prédiction temporelle :
la signature dérivée sur 1983-2009 (TRAIN) est testée sur 2010-2019 (TEST).

Source : van Woesik & Kratochwill 2022, BCO-DMO
         doi:10.26008/1912/bco-dmo.773466.2

Protocole pré-spécifié : CR-02, §A
  - Split primaire : 2010
  - Classification exogène : DHW + cyclone_freq uniquement
  - Bleaching % = variable réponse exclusivement

Seed : 20240601 (date de rédaction du protocole)

Usage :
  python CR02_A_reef_temporal_split.py [chemin/global_bleaching_environmental.csv]
"""

import sys, os, json, warnings
from pathlib import Path
import numpy as np
import pandas as pd
from scipy import stats
from scipy.optimize import curve_fit
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

warnings.filterwarnings('ignore')
np.random.seed(20240601)

plt.rcParams.update({
    'font.size': 10, 'axes.titlesize': 12, 'axes.labelsize': 11,
    'figure.dpi': 150, 'savefig.dpi': 300, 'savefig.bbox': 'tight',
})

SEED = 20240601
SPLIT_YEAR = 2010  # pré-spécifié
N_BOOT = 10_000
OUT_DIR = Path('output_CR02A')
OUT_DIR.mkdir(exist_ok=True)


# ════════════════════════════════════════════════════════════════
# CHARGEMENT
# ════════════════════════════════════════════════════════════════

def find_csv():
    """Cherche le CSV dans les emplacements courants."""
    if len(sys.argv) > 1 and os.path.exists(sys.argv[1]):
        return sys.argv[1]
    candidates = [
        'global_bleaching_environmental.csv',
        '../data/global_bleaching_environmental.csv',
        'data/global_bleaching_environmental.csv',
        '../ScriptCorail/global_bleaching_environmental.csv',
    ]
    for c in candidates:
        if os.path.exists(c):
            return c
    print("ERREUR : global_bleaching_environmental.csv introuvable.")
    print("  Usage : python CR02_A_reef_temporal_split.py <chemin.csv>")
    sys.exit(1)


def load_data(path):
    df = pd.read_csv(path)
    rn = {
        'Latitude_Degrees': 'lat', 'Longitude_Degrees': 'lon',
        'Date_Year': 'year', 'Percent_Bleaching': 'bleaching',
        'SSTA_DHW': 'dhw', 'SSTA_DHWMax': 'dhw_max',
        'Cyclone_Frequency': 'cyclone_freq',
        'Country_Name': 'country', 'Ocean_Name': 'ocean',
        'Ecoregion_Name': 'ecoregion', 'Realm_Name': 'realm',
        'Site_ID': 'site_id', 'Reef_ID': 'reef_id',
    }
    df = df.rename(columns=rn)
    for c in ['bleaching', 'dhw', 'dhw_max', 'cyclone_freq', 'lat', 'lon', 'year']:
        if c in df.columns:
            df[c] = pd.to_numeric(df[c], errors='coerce')
    df = df.dropna(subset=['bleaching', 'dhw', 'year'])
    return df


# ════════════════════════════════════════════════════════════════
# CLASSIFICATION EXOGÈNE (identique à corail.py — classify_clean)
# ════════════════════════════════════════════════════════════════

def classify_clean(df, cyc_median_override=None):
    """
    Classification CLEAN — bleaching JAMAIS utilisé.

    BASELINE  : DHW < 4
    INPUT     : 4 ≤ DHW < 8, cyclone ≤ médiane
    STRUCTURE : DHW ≥ 8 OU cyclone > 1.5×médiane

    Si cyc_median_override est fourni, utilise cette valeur
    (cas TEST : médiane dérivée de TRAIN).
    """
    dhw = df['dhw'].fillna(0)
    cyc = df['cyclone_freq'].fillna(0)

    if cyc_median_override is not None:
        cyc_med = cyc_median_override
    else:
        cyc_med = cyc[cyc > 0].median() if (cyc > 0).any() else 999

    pt = pd.Series('baseline', index=df.index)
    pt[(dhw >= 4) & (dhw < 8) & (cyc <= cyc_med)] = 'input'
    pt[(dhw >= 8) | (cyc > cyc_med * 1.5)] = 'structure'
    df = df.copy()
    df['ptype'] = pt
    return df, cyc_med


# ════════════════════════════════════════════════════════════════
# BATTERIE STATISTIQUE
# ════════════════════════════════════════════════════════════════

def compute_stats(df, label=''):
    """Cohen's d, ratio S/I, p-value, bootstrap CI."""
    inp = df.loc[df['ptype'] == 'input', 'bleaching'].dropna().values
    stc = df.loc[df['ptype'] == 'structure', 'bleaching'].dropna().values

    if len(inp) < 10 or len(stc) < 10:
        print(f"  [{label}] ATTENTION : n trop faible (input={len(inp)}, struct={len(stc)})")
        return None

    # Cohen's d (pooled)
    n1, n2 = len(inp), len(stc)
    pooled = np.sqrt(((n1 - 1) * np.var(inp, ddof=1) + (n2 - 1) * np.var(stc, ddof=1)) / (n1 + n2 - 2))
    d = (np.mean(stc) - np.mean(inp)) / pooled if pooled > 0 else 0

    # Mann-Whitney
    U, p = stats.mannwhitneyu(stc, inp, alternative='greater')

    # Ratio S/I (moyennes brutes)
    ratio = np.mean(stc) / max(np.mean(inp), 0.01)

    # Bootstrap CI
    rng = np.random.RandomState(SEED)
    boot_d = np.zeros(N_BOOT)
    boot_ratio = np.zeros(N_BOOT)
    for i in range(N_BOOT):
        bi = rng.choice(inp, n1, replace=True)
        bs = rng.choice(stc, n2, replace=True)
        ps_b = np.sqrt(((n1 - 1) * np.var(bi, ddof=1) + (n2 - 1) * np.var(bs, ddof=1)) / (n1 + n2 - 2))
        boot_d[i] = (np.mean(bs) - np.mean(bi)) / ps_b if ps_b > 0 else 0
        boot_ratio[i] = np.mean(bs) / max(np.mean(bi), 0.01)

    ci_d = np.percentile(boot_d, [2.5, 97.5])
    ci_ratio = np.percentile(boot_ratio, [2.5, 97.5])

    return {
        'label': label,
        'n_input': n1, 'n_structure': n2,
        'mean_input': float(np.mean(inp)), 'mean_struct': float(np.mean(stc)),
        'median_input': float(np.median(inp)), 'median_struct': float(np.median(stc)),
        'd': float(d), 'U': float(U), 'p': float(p),
        'ratio': float(ratio),
        'boot_d': boot_d,
        'boot_ratio': boot_ratio,
        'd_ci': [float(ci_d[0]), float(ci_d[1])],
        'ratio_ci': [float(ci_ratio[0]), float(ci_ratio[1])],
    }


def fit_sigmoid(df, label=''):
    """Ajuste sigmoïde dose-réponse DHW → bleaching."""
    v = df.dropna(subset=['dhw', 'bleaching'])
    v = v[(v['dhw'] >= 0) & (v['bleaching'] >= 0)]
    x = v['dhw'].values
    y = v['bleaching'].values

    def sigm(x, L, k, x0, b):
        return L / (1 + np.exp(-k * (x - x0))) + b

    try:
        po, _ = curve_fit(sigm, x, y,
                          p0=[80, 0.5, 8, 0], maxfev=10000,
                          bounds=([0, 0, 0, -50], [100, 5, 30, 50]))
        yp = sigm(x, *po)
        ss_res = np.sum((y - yp) ** 2)
        ss_tot = np.sum((y - np.mean(y)) ** 2)
        r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0
        return {
            'label': label,
            'params': [float(p) for p in po],
            'L': float(po[0]), 'k': float(po[1]),
            'midpoint': float(po[2]), 'b': float(po[3]),
            'r2': float(r2), 'n': len(x),
            'x': x, 'y': y,
        }
    except Exception as e:
        print(f"  [{label}] Sigmoïde échouée : {e}")
        return None


def sigmoid_predict(x, params):
    """Applique la sigmoïde avec paramètres pré-calculés."""
    L, k, x0, b = params
    return L / (1 + np.exp(-k * (x - x0))) + b


def r2_oos(y_true, y_pred):
    """R² out-of-sample."""
    ss_res = np.sum((y_true - y_pred) ** 2)
    ss_tot = np.sum((y_true - np.mean(y_true)) ** 2)
    return 1 - ss_res / ss_tot if ss_tot > 0 else float('nan')


# ════════════════════════════════════════════════════════════════
# MAIN
# ════════════════════════════════════════════════════════════════

def main():
    print("=" * 75)
    print("  CR-02 PARTIE A — SPLIT TEMPOREL GCBD")
    print(f"  Split pré-spécifié : {SPLIT_YEAR}")
    print(f"  Seed : {SEED}")
    print("=" * 75)

    csv_path = find_csv()
    df = load_data(csv_path)
    print(f"\n[DATA] {len(df)} observations, {df['year'].min():.0f}-{df['year'].max():.0f}")
    print(f"  {df['country'].nunique()} pays, {df['site_id'].nunique()} sites")

    # ── ÉTAPE 1 : Partition temporelle ────────────────────────
    print(f"\n{'─' * 60}")
    print(f"  ÉTAPE 1 : Partition temporelle (coupure = {SPLIT_YEAR})")
    print(f"{'─' * 60}")

    df_train = df[df['year'] < SPLIT_YEAR].copy()
    df_test = df[df['year'] >= SPLIT_YEAR].copy()

    print(f"  TRAIN (1983-2009) : {len(df_train)} observations")
    print(f"    années : {df_train['year'].min():.0f}-{df_train['year'].max():.0f}")
    print(f"    sites  : {df_train['site_id'].nunique()}")
    print(f"  TEST  (2010-2019) : {len(df_test)} observations")
    print(f"    années : {df_test['year'].min():.0f}-{df_test['year'].max():.0f}")
    print(f"    sites  : {df_test['site_id'].nunique()}")

    # ── ÉTAPE 2 : Dériver la signature sur TRAIN ──────────────
    print(f"\n{'─' * 60}")
    print(f"  ÉTAPE 2 : Signature sur TRAIN uniquement")
    print(f"{'─' * 60}")

    # Classification avec médiane cyclonique de TRAIN
    df_train, cyc_med_train = classify_clean(df_train)
    print(f"  Médiane cyclonique (TRAIN) : {cyc_med_train:.4f}")

    counts_train = df_train['ptype'].value_counts()
    print(f"  Classification TRAIN :")
    for pt in ['baseline', 'input', 'structure']:
        print(f"    {pt:<12s}: {counts_train.get(pt, 0)}")

    stats_train = compute_stats(df_train, 'TRAIN')
    sig_train = fit_sigmoid(df_train, 'TRAIN')

    if stats_train:
        print(f"\n  TRAIN — Résultats :")
        print(f"    Cohen's d     = {stats_train['d']:.4f}")
        print(f"    Ratio S/I     = {stats_train['ratio']:.2f}×")
        print(f"    p (MW)        = {stats_train['p']:.2e}")
        print(f"    Bootstrap CI d= [{stats_train['d_ci'][0]:.4f}, {stats_train['d_ci'][1]:.4f}]")
    if sig_train:
        print(f"    Sigmoïde R²   = {sig_train['r2']:.4f}")
        print(f"    Midpoint DHW  = {sig_train['midpoint']:.2f}")

    # ── ÉTAPE 3 : Tester la prédiction sur TEST ──────────────
    print(f"\n{'─' * 60}")
    print(f"  ÉTAPE 3 : Prédiction sur TEST (seuils de TRAIN)")
    print(f"{'─' * 60}")

    # Appliquer EXACTEMENT les mêmes seuils (médiane cyclonique de TRAIN)
    df_test, _ = classify_clean(df_test, cyc_median_override=cyc_med_train)
    print(f"  Médiane cyclonique appliquée : {cyc_med_train:.4f} (dérivée de TRAIN)")

    counts_test = df_test['ptype'].value_counts()
    print(f"  Classification TEST :")
    for pt in ['baseline', 'input', 'structure']:
        print(f"    {pt:<12s}: {counts_test.get(pt, 0)}")

    stats_test = compute_stats(df_test, 'TEST')

    if stats_test:
        print(f"\n  TEST — Résultats :")
        print(f"    Cohen's d     = {stats_test['d']:.4f}")
        print(f"    Ratio S/I     = {stats_test['ratio']:.2f}×")
        print(f"    p (MW)        = {stats_test['p']:.2e}")
        print(f"    Bootstrap CI d= [{stats_test['d_ci'][0]:.4f}, {stats_test['d_ci'][1]:.4f}]")

    # R² out-of-sample de la sigmoïde
    r2_oos_val = None
    if sig_train:
        v_test = df_test.dropna(subset=['dhw', 'bleaching'])
        v_test = v_test[(v_test['dhw'] >= 0) & (v_test['bleaching'] >= 0)]
        y_pred = sigmoid_predict(v_test['dhw'].values, sig_train['params'])
        r2_oos_val = r2_oos(v_test['bleaching'].values, y_pred)
        print(f"    R² OOS sigmoïde = {r2_oos_val:.4f}")

    # ── Dataset complet (référence) ───────────────────────────
    print(f"\n{'─' * 60}")
    print(f"  RÉFÉRENCE : Dataset complet")
    print(f"{'─' * 60}")

    df_full, cyc_med_full = classify_clean(df)
    counts_full = df_full['ptype'].value_counts()
    print(f"  Médiane cyclonique (full) : {cyc_med_full:.4f}")
    for pt in ['baseline', 'input', 'structure']:
        print(f"    {pt:<12s}: {counts_full.get(pt, 0)}")

    stats_full = compute_stats(df_full, 'FULL')
    sig_full = fit_sigmoid(df_full, 'FULL')

    if stats_full:
        print(f"\n  FULL — Résultats :")
        print(f"    Cohen's d     = {stats_full['d']:.4f}")
        print(f"    Ratio S/I     = {stats_full['ratio']:.2f}×")
        print(f"    p (MW)        = {stats_full['p']:.2e}")
        print(f"    Bootstrap CI d= [{stats_full['d_ci'][0]:.4f}, {stats_full['d_ci'][1]:.4f}]")
    if sig_full:
        print(f"    Midpoint DHW  = {sig_full['midpoint']:.2f}")

    # ── ÉTAPE 4 : Tableau comparatif ─────────────────────────
    print(f"\n{'═' * 75}")
    print(f"  ÉTAPE 4 — TABLEAU COMPARATIF")
    print(f"{'═' * 75}")

    header = f"  {'Métrique':<24s} {'TRAIN (83-09)':>16s} {'TEST (10-19)':>16s} {'Complet':>16s}"
    sep = f"  {'─' * 24} {'─' * 16} {'─' * 16} {'─' * 16}"
    print(header)
    print(sep)

    def fmt(v, f='.4f'):
        if v is None: return '—'
        return f'{v:{f}}'

    rows = [
        ('n input',
         stats_train['n_input'] if stats_train else None,
         stats_test['n_input'] if stats_test else None,
         stats_full['n_input'] if stats_full else None, 'd'),
        ('n structure',
         stats_train['n_structure'] if stats_train else None,
         stats_test['n_structure'] if stats_test else None,
         stats_full['n_structure'] if stats_full else None, 'd'),
        ("Cohen's d",
         stats_train['d'] if stats_train else None,
         stats_test['d'] if stats_test else None,
         stats_full['d'] if stats_full else None, '.4f'),
        ('Ratio S/I',
         stats_train['ratio'] if stats_train else None,
         stats_test['ratio'] if stats_test else None,
         stats_full['ratio'] if stats_full else None, '.2f'),
        ('p (Mann-Whitney)',
         stats_train['p'] if stats_train else None,
         stats_test['p'] if stats_test else None,
         stats_full['p'] if stats_full else None, '.2e'),
        ('Bootstrap CI d',
         stats_train['d_ci'] if stats_train else None,
         stats_test['d_ci'] if stats_test else None,
         stats_full['d_ci'] if stats_full else None, 'ci'),
        ('Midpoint sigmoïde',
         sig_train['midpoint'] if sig_train else None,
         None,
         sig_full['midpoint'] if sig_full else None, '.1f'),
        ('R² sigmoïde',
         sig_train['r2'] if sig_train else None,
         r2_oos_val,
         sig_full['r2'] if sig_full else None, '.4f'),
    ]

    for name, v_tr, v_te, v_fu, f in rows:
        def cell(v):
            if v is None: return '—'
            if f == 'd': return f'{int(v):,}'
            if f == 'ci': return f'[{v[0]:.3f}, {v[1]:.3f}]'
            if f == '.2e': return f'{v:.2e}'
            return f'{v:{f}}'
        print(f"  {name:<24s} {cell(v_tr):>16s} {cell(v_te):>16s} {cell(v_fu):>16s}")

    # ── VERDICT ───────────────────────────────────────────────
    print(f"\n{'═' * 75}")
    print(f"  VERDICT")
    print(f"{'═' * 75}")

    if stats_train and stats_test:
        d_test = stats_test['d']
        ci_train = stats_train['d_ci']
        p_test = stats_test['p']
        ratio_test = stats_test['ratio']

        in_ci = ci_train[0] <= d_test <= ci_train[1]
        p_sig001 = p_test < 0.01
        p_sig005 = p_test < 0.05
        ratio_ok = 1.5 <= ratio_test <= 2.2
        ratio_wide = 1.0 <= ratio_test <= 3.0

        print(f"  d_TEST = {d_test:.4f}")
        print(f"  CI_TRAIN = [{ci_train[0]:.4f}, {ci_train[1]:.4f}]")
        print(f"  d_TEST dans CI_TRAIN ? {'OUI' if in_ci else 'NON'}")
        print(f"  p_TEST < 0.01 ? {'OUI' if p_sig001 else 'NON'} (p = {p_test:.2e})")
        print(f"  Ratio S/I TEST = {ratio_test:.2f}×, dans [1.5, 2.2] ? {'OUI' if ratio_ok else 'NON'}")

        if in_ci and ratio_ok and p_sig001:
            verdict = "SUCCÈS FORT"
            expl = ("d_TEST dans le bootstrap CI de TRAIN, "
                    "ratio S/I dans [1.5, 2.2], p < 0.01")
        elif p_sig005 and ratio_wide:
            verdict = "SUCCÈS MODÉRÉ"
            expl = (f"d_TEST significatif (p < 0.05) mais "
                    f"{'hors CI de TRAIN' if not in_ci else 'dans CI'}, "
                    f"ratio {'dans' if ratio_ok else 'hors'} [1.5, 2.2]")
        else:
            verdict = "ÉCHEC INFORMATIF"
            expl = (f"d_TEST {'non significatif' if not p_sig005 else 'significatif'}, "
                    f"ratio S/I = {ratio_test:.2f}× "
                    f"{'hors [1.0, 3.0]' if not ratio_wide else 'dans [1.0, 3.0]'}")

        print(f"\n  ★ {verdict}")
        print(f"    {expl}")

    # ── DONNÉES BINNÉES (nécessaires pour figure ET pour JSON) ──
    print(f"\n{'─' * 60}")
    print(f"  DONNÉES BINNÉES & COMPARAISON HIGH DHW")
    print(f"{'─' * 60}")

    dhw_bins = np.arange(0, 32, 1)
    train_binned = None
    test_binned = None
    binned_comparison = None

    if sig_train:
        v_test = df_test.dropna(subset=['dhw', 'bleaching'])
        v_test = v_test[(v_test['dhw'] >= 0) & (v_test['bleaching'] >= 0)]
        test_binned = v_test.groupby(pd.cut(v_test['dhw'], dhw_bins)).agg(
            dhw_mid=('dhw', 'mean'),
            bl_mean=('bleaching', 'mean'),
            bl_std=('bleaching', 'std'),
            n=('bleaching', 'count')
        ).dropna()

        v_train = df_train.dropna(subset=['dhw', 'bleaching'])
        v_train = v_train[(v_train['dhw'] >= 0) & (v_train['bleaching'] >= 0)]
        train_binned = v_train.groupby(pd.cut(v_train['dhw'], dhw_bins)).agg(
            dhw_mid=('dhw', 'mean'),
            bl_mean=('bleaching', 'mean'),
            bl_std=('bleaching', 'std'),
            n=('bleaching', 'count')
        ).dropna()

        # Comparaison binnée DHW > 12
        tr_high = train_binned[train_binned['dhw_mid'] > 12]
        te_high = test_binned[test_binned['dhw_mid'] > 12]
        tr_high_valid = tr_high[tr_high['n'] >= 5]
        te_high_valid = te_high[te_high['n'] >= 5]

        if len(tr_high_valid) > 0 and len(te_high_valid) > 0:
            # Weighted mean by n
            tr_wmean = np.average(tr_high_valid['bl_mean'], weights=tr_high_valid['n'])
            te_wmean = np.average(te_high_valid['bl_mean'], weights=te_high_valid['n'])
            direction = "TEST < TRAIN" if te_wmean < tr_wmean else "TEST > TRAIN"
            binned_comparison = {
                'DHW_range': '>12',
                'mean_bleaching_TRAIN_binned': float(round(tr_wmean, 2)),
                'mean_bleaching_TEST_binned': float(round(te_wmean, 2)),
                'n_bins_TRAIN': int(len(tr_high_valid)),
                'n_bins_TEST': int(len(te_high_valid)),
                'n_obs_TRAIN': int(tr_high_valid['n'].sum()),
                'n_obs_TEST': int(te_high_valid['n'].sum()),
                'direction': direction,
            }
            print(f"  DHW > 12 :")
            print(f"    TRAIN binné (moy. pondérée) = {tr_wmean:.2f}%  "
                  f"({len(tr_high_valid)} bins, {int(tr_high_valid['n'].sum())} obs)")
            print(f"    TEST  binné (moy. pondérée) = {te_wmean:.2f}%  "
                  f"({len(te_high_valid)} bins, {int(te_high_valid['n'].sum())} obs)")
            print(f"    Direction : {direction}")
        else:
            print(f"  DHW > 12 : pas assez de données binnées (n ≥ 5) pour comparer.")

    # ── FIGURE MANUSCRIT (2 panneaux) ─────────────────────────
    print(f"\n{'─' * 60}")
    print(f"  FIGURE MANUSCRIT (2 panneaux)")
    print(f"{'─' * 60}")

    C_TRAIN = '#1565C0'
    C_TEST = '#C62828'

    # 180mm ≈ 7.09 inches ; ratio ~2.2:1 pour 2 panneaux horizontaux
    fig, (ax_left, ax_right) = plt.subplots(1, 2, figsize=(7.09, 3.2))
    fig.subplots_adjust(wspace=0.38, left=0.08, right=0.97, top=0.90, bottom=0.15)

    # ── Panneau gauche : Sigmoïde TRAIN + données TEST binnées ──
    ax = ax_left
    if sig_train and train_binned is not None and test_binned is not None:
        # Sigmoïde TRAIN
        x_sig = np.linspace(0, 30, 300)
        y_sig = sigmoid_predict(x_sig, sig_train['params'])
        ax.plot(x_sig, y_sig, color=C_TRAIN, lw=2, label='Sigmoid (TRAIN)', zorder=5)

        # Points TRAIN
        valid_tr = train_binned[train_binned['n'] >= 5]
        ax.errorbar(valid_tr['dhw_mid'], valid_tr['bl_mean'],
                    yerr=valid_tr['bl_std'] / np.sqrt(valid_tr['n']),
                    fmt='o', color=C_TRAIN, alpha=0.5, ms=3, capsize=1.5, lw=0.8,
                    label=f'TRAIN 1983–{SPLIT_YEAR - 1}', zorder=3)

        # Points TEST
        valid_te = test_binned[test_binned['n'] >= 5]
        ax.errorbar(valid_te['dhw_mid'], valid_te['bl_mean'],
                    yerr=valid_te['bl_std'] / np.sqrt(valid_te['n']),
                    fmt='s', color=C_TEST, alpha=0.8, ms=4, capsize=2, lw=0.8,
                    label=f'TEST {SPLIT_YEAR}–2019', zorder=4)

        # Midpoint + seuil
        ax.axvline(sig_train['midpoint'], color=C_TRAIN, ls=':', alpha=0.4, lw=0.8)
        ax.axvline(8, color='gray', ls='--', alpha=0.3, lw=0.8)

        ax.set_xlabel('DHW (Degree Heating Weeks)')
        ax.set_ylabel('Mean bleaching (%)')
        ax.set_title('(a) Dose-response: TRAIN sigmoid vs TEST data', fontsize=10)
        ax.legend(fontsize=7, loc='upper left')
        ax.set_xlim(-0.5, 25)
        ax.set_ylim(-2, None)

    # ── Panneau droit : Asymétrie annuelle ──
    ax = ax_right
    yearly = df_full.groupby('year').apply(lambda g: pd.Series({
        'bl_input': g.loc[g['ptype'] == 'input', 'bleaching'].mean(),
        'bl_struct': g.loc[g['ptype'] == 'structure', 'bleaching'].mean(),
        'n_input': (g['ptype'] == 'input').sum(),
        'n_struct': (g['ptype'] == 'structure').sum(),
    }))
    yearly = yearly[(yearly['n_input'] >= 5) & (yearly['n_struct'] >= 5)]
    ax.plot(yearly.index, yearly['bl_input'], 'o-', color='#2196F3',
            label='Input mean', ms=3, lw=1.2)
    ax.plot(yearly.index, yearly['bl_struct'], 's-', color='#E53935',
            label='Structure mean', ms=3, lw=1.2)
    ax.fill_between(yearly.index, yearly['bl_input'], yearly['bl_struct'],
                    alpha=0.08, color='orange')
    ax.axvline(SPLIT_YEAR, color='black', ls='--', lw=1.5,
               label=f'Split ({SPLIT_YEAR})')
    ax.axvspan(SPLIT_YEAR, yearly.index.max() + 1, alpha=0.04, color='red')
    ax.set_xlabel('Year')
    ax.set_ylabel('Mean bleaching (%)')
    ax.set_title('(b) Annual asymmetry across split', fontsize=10)
    ax.legend(fontsize=7)

    fig_path = OUT_DIR / 'CR02A_reef_manuscript.png'
    plt.savefig(fig_path, dpi=300, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"  Figure manuscrit : {fig_path}")

    # ── EXPORT JSON (enrichi) ─────────────────────────────────
    export = {
        'protocol': 'CR-02A',
        'split_year': SPLIT_YEAR,
        'seed': SEED,
        'n_boot': N_BOOT,
        'cyc_median_train': float(cyc_med_train),
    }
    for key, st in [('train', stats_train), ('test', stats_test), ('full', stats_full)]:
        if st:
            export[key] = {k: v for k, v in st.items()
                          if k not in ('boot_d', 'boot_ratio')}
    for key, sg in [('sigmoid_train', sig_train), ('sigmoid_full', sig_full)]:
        if sg:
            export[key] = {k: v for k, v in sg.items() if k not in ('x', 'y')}
    if r2_oos_val is not None:
        export['r2_oos_sigmoid'] = float(r2_oos_val)
    if stats_train and stats_test:
        export['verdict'] = verdict
    if binned_comparison is not None:
        export['binned_comparison_high_DHW'] = binned_comparison

    def nc(o):
        if isinstance(o, (np.integer,)): return int(o)
        if isinstance(o, (np.floating,)): return float(o)
        if isinstance(o, np.ndarray): return o.tolist()
        if isinstance(o, np.bool_): return bool(o)
        raise TypeError(f"{type(o)}")

    json_path = OUT_DIR / 'CR02A_reef_temporal_split.json'
    with open(json_path, 'w') as f:
        json.dump(export, f, indent=2, default=nc)
    print(f"  JSON : {json_path}")

    # ── ANALYSE EXPLORATOIRE : split 2005 ─────────────────────
    print(f"\n{'─' * 60}")
    print(f"  EXPLORATOIRE : split alternatif (2005)")
    print(f"{'─' * 60}")

    df_tr05 = df[df['year'] < 2005].copy()
    df_te05 = df[df['year'] >= 2005].copy()
    df_tr05, cyc05 = classify_clean(df_tr05)
    df_te05, _ = classify_clean(df_te05, cyc_median_override=cyc05)

    st_tr05 = compute_stats(df_tr05, 'TRAIN-2005')
    st_te05 = compute_stats(df_te05, 'TEST-2005')

    if st_tr05 and st_te05:
        print(f"  TRAIN (< 2005) : d={st_tr05['d']:.4f}, ratio={st_tr05['ratio']:.2f}×, "
              f"p={st_tr05['p']:.2e} (n_i={st_tr05['n_input']}, n_s={st_tr05['n_structure']})")
        print(f"  TEST  (≥ 2005) : d={st_te05['d']:.4f}, ratio={st_te05['ratio']:.2f}×, "
              f"p={st_te05['p']:.2e} (n_i={st_te05['n_input']}, n_s={st_te05['n_structure']})")
        in_ci_05 = st_tr05['d_ci'][0] <= st_te05['d'] <= st_tr05['d_ci'][1]
        print(f"  d_TEST dans CI_TRAIN ? {'OUI' if in_ci_05 else 'NON'}")
        print(f"  ⚠ EXPLORATOIRE — non pré-spécifié")

    print(f"\n{'═' * 75}")
    print(f"  FIN CR-02A")
    print(f"{'═' * 75}")


if __name__ == '__main__':
    main()