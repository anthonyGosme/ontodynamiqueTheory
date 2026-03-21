#!/usr/bin/env python3
"""
=============================================================================
R-XVII RIVAL PARTITION TEST — CORAL REEFS (GCBD)
=============================================================================
Analogue du test GDSC/MDSINE2/levure pour le domaine récifs coralliens.

Ici on partitionne les OBSERVATIONS (site×année) en INPUT vs STRUCTURE
selon des critères environnementaux exogènes. Le bleaching % est
exclusivement la variable réponse.

PARTITIONS:
  (1) ONTODYNAMIQUE  — INPUT: DHW 4-8, STRUCTURE: DHW≥8 or cyclone élevé
  (2) SSTA-BASED     — partition par SSTA au lieu de DHW
  (3) DEPTH/TURBID   — sites vulnérables (shallow) vs protégés (deep)
  (4) CYCLONE-ONLY   — partition uniquement par cyclone_freq
  (5) RANDOM (1000×) — assignation aléatoire parmi sites stressés

Pour chaque partition:
  - Global ratio + d + p
  - CV par océan (analogue du CV par cancer type)
  - Bootstrap CI

Source: van Woesik & Kratochwill 2022, BCO-DMO
        doi:10.26008/1912/bco-dmo.773466.2

Usage:
  python3 07_rival_partitions_reef.py [global_bleaching_environmental.csv]
=============================================================================
"""

import sys, os, time, json, warnings
from pathlib import Path
import numpy as np
import pandas as pd
from scipy import stats
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

warnings.filterwarnings('ignore')

N_RANDOM = 1000
MIN_OBS_PER_REGION = 50
MIN_N_PER_ARM = 30

plt.rcParams.update({
    'font.size': 10, 'axes.titlesize': 12, 'axes.labelsize': 11,
    'figure.dpi': 150, 'savefig.dpi': 300, 'savefig.bbox': 'tight',
})


# ============================================================================
# DATA LOADING (from corail.py)
# ============================================================================

def load_data(path):
    df = pd.read_csv(path)
    rn = {
        'Latitude_Degrees': 'lat', 'Longitude_Degrees': 'lon',
        'Date_Year': 'year', 'Percent_Bleaching': 'bleaching',
        'SSTA_DHW': 'dhw', 'SSTA_DHWMax': 'dhw_max',
        'Temperature_Mean': 'sst_mean', 'Temperature_Maximum': 'sst_max',
        'ClimSST': 'clim_sst', 'SSTA': 'ssta', 'SSTA_Maximum': 'ssta_max',
        'TSA_DHW': 'tsa_dhw', 'TSA_DHWMax': 'tsa_dhw_max',
        'Cyclone_Frequency': 'cyclone_freq', 'Distance_to_Shore': 'dist_shore',
        'Depth_m': 'depth', 'Turbidity': 'turbidity', 'Windspeed': 'windspeed',
        'Country_Name': 'country', 'Ocean_Name': 'ocean',
        'Ecoregion_Name': 'ecoregion', 'Realm_Name': 'realm',
        'Site_ID': 'site_id', 'Reef_ID': 'reef_id',
    }
    df = df.rename(columns=rn)
    for c in ['bleaching', 'dhw', 'dhw_max', 'sst_mean', 'sst_max', 'clim_sst',
              'ssta', 'ssta_max', 'tsa_dhw', 'tsa_dhw_max', 'cyclone_freq',
              'dist_shore', 'depth', 'turbidity', 'lat', 'lon', 'year']:
        if c in df.columns:
            df[c] = pd.to_numeric(df[c], errors='coerce')
    df = df.dropna(subset=['bleaching', 'dhw'])
    return df


# ============================================================================
# PARTITION DEFINITIONS
# ============================================================================

def classify_ontodynamique(df):
    """
    BASELINE: DHW < 4
    INPUT: 4 ≤ DHW < 8, cyclone ≤ median
    STRUCTURE: DHW ≥ 8 OR cyclone > 1.5×median
    """
    dhw = df['dhw'].fillna(0)
    cyc = df['cyclone_freq'].fillna(0)
    cyc_med = cyc[cyc > 0].median() if (cyc > 0).any() else 999

    pt = pd.Series('baseline', index=df.index)
    pt[(dhw >= 4) & (dhw < 8) & (cyc <= cyc_med)] = 'input'
    pt[(dhw >= 8) | (cyc > cyc_med * 1.5)] = 'structure'
    return pt


def classify_ssta(df):
    """
    Partition by SSTA (Sea Surface Temperature Anomaly) instead of DHW.
    SSTA captures instantaneous thermal stress; DHW captures accumulated.
    INPUT: moderate SSTA (1-2°C)
    STRUCTURE: severe SSTA (>2°C)
    """
    ssta = df['ssta_max'].fillna(df['ssta'].fillna(0))
    pt = pd.Series('baseline', index=df.index)
    pt[(ssta >= 1) & (ssta < 2)] = 'input'
    pt[ssta >= 2] = 'structure'
    return pt


def classify_depth(df):
    """
    Partition by site vulnerability (depth).
    Shallow sites are more exposed to thermal + UV + wave damage.
    INPUT: deep sites (>10m, more buffered)
    STRUCTURE: shallow sites (≤5m, more exposed)
    Restricted to stressed observations (DHW ≥ 4).
    """
    depth = df['depth'].fillna(df['depth'].median() if 'depth' in df.columns else 10)
    dhw = df['dhw'].fillna(0)

    pt = pd.Series('baseline', index=df.index)
    stressed = dhw >= 4
    pt[stressed & (depth > 10)] = 'input'
    pt[stressed & (depth <= 5)] = 'structure'
    return pt


def classify_cyclone_only(df):
    """
    Partition by cyclone frequency alone (physical destruction).
    INPUT: low cyclone areas under thermal stress
    STRUCTURE: high cyclone areas under thermal stress
    """
    cyc = df['cyclone_freq'].fillna(0)
    dhw = df['dhw'].fillna(0)
    cyc_med = cyc[cyc > 0].median() if (cyc > 0).any() else 999

    pt = pd.Series('baseline', index=df.index)
    stressed = dhw >= 4
    pt[stressed & (cyc <= cyc_med)] = 'input'
    pt[stressed & (cyc > cyc_med)] = 'structure'
    return pt


PARTITIONS = {
    'Ontodynamique': {
        'func': classify_ontodynamique,
        'motivation': 'R-XVII: sub-lethal thermal (input) vs mortality-level/physical (structure)',
    },
    'SSTA (température)': {
        'func': classify_ssta,
        'motivation': 'Anomalie SST instantanée au lieu du DHW cumulé',
    },
    'Profondeur': {
        'func': classify_depth,
        'motivation': 'Vulnérabilité du site (shallow=exposé vs deep=tamponné)',
    },
    'Cyclone seul': {
        'func': classify_cyclone_only,
        'motivation': 'Destruction physique seule, sans seuil thermique',
    },
}


# ============================================================================
# STATISTICAL ENGINE
# ============================================================================

def compute_ratio_stats(bleach_input, bleach_structure):
    """Compute ratio, d, p from two arrays of bleaching %."""
    inp = bleach_input[np.isfinite(bleach_input)]
    stc = bleach_structure[np.isfinite(bleach_structure)]

    if len(inp) < MIN_N_PER_ARM or len(stc) < MIN_N_PER_ARM:
        return None

    m_inp, m_stc = np.mean(inp), np.mean(stc)

    # Ratio (structure / input)
    ratio = m_stc / max(m_inp, 0.01)

    # Mann-Whitney
    U, p = stats.mannwhitneyu(stc, inp, alternative='greater')

    # Cohen's d
    n1, n2 = len(inp), len(stc)
    pooled = np.sqrt(((n1-1)*np.var(inp, ddof=1) + (n2-1)*np.var(stc, ddof=1)) / (n1+n2-2))
    d = (m_stc - m_inp) / pooled if pooled > 0 else 0

    return {
        'n_input': n1, 'n_structure': n2,
        'mean_input': float(m_inp), 'mean_structure': float(m_stc),
        'ratio': float(ratio),
        'd': float(d), 'abs_d': float(abs(d)),
        'p_MW': float(p),
    }


def compute_cv_by_region(df, ptype_col, region_col='ocean'):
    """Compute ratio per region → CV."""
    ratios = []
    per_region = []

    for reg, grp in df.groupby(region_col):
        if len(grp) < MIN_OBS_PER_REGION:
            continue
        inp = grp.loc[grp[ptype_col] == 'input', 'bleaching'].values
        stc = grp.loc[grp[ptype_col] == 'structure', 'bleaching'].values

        if len(inp) < 10 or len(stc) < 10:
            continue

        m_inp, m_stc = np.mean(inp), np.mean(stc)
        if m_inp > 0.01:
            ratio = m_stc / m_inp
            _, p = stats.mannwhitneyu(stc, inp, alternative='greater')
            ratios.append(ratio)
            per_region.append({
                'region': str(reg), 'ratio': float(ratio),
                'p': float(p), 'n_input': len(inp), 'n_structure': len(stc),
            })

    if len(ratios) < 2:
        return None

    arr = np.array(ratios)
    return {
        'n_regions': len(ratios),
        'mean_ratio': float(np.mean(arr)),
        'median_ratio': float(np.median(arr)),
        'cv_ratio': float(np.std(arr, ddof=1) / np.mean(arr) * 100) if np.mean(arr) > 0 else float('inf'),
        'min_ratio': float(np.min(arr)),
        'max_ratio': float(np.max(arr)),
        'per_region': per_region,
    }


def bootstrap_ratio(df, ptype_col, n_boot=10000):
    """Bootstrap the ratio by resampling observations."""
    inp = df.loc[df[ptype_col] == 'input', 'bleaching'].values
    stc = df.loc[df[ptype_col] == 'structure', 'bleaching'].values

    rng = np.random.RandomState(42)
    boot = []
    for _ in range(n_boot):
        bi = rng.choice(inp, len(inp), replace=True)
        bs = rng.choice(stc, len(stc), replace=True)
        m_inp = np.mean(bi)
        if m_inp > 0.01:
            boot.append(np.mean(bs) / m_inp)

    arr = np.array(boot)
    return {
        'mean': float(np.mean(arr)),
        'ci_95': [float(np.percentile(arr, 2.5)), float(np.percentile(arr, 97.5))],
        'cv': float(np.std(arr, ddof=1) / np.mean(arr) * 100),
    }


# ============================================================================
# MAIN
# ============================================================================

def main():
    t0 = time.time()

    print("=" * 70)
    print("  R-XVII RIVAL PARTITION TEST — CORAL REEFS (GCBD)")
    print("  Partitions alternatives des observations stressées")
    print("=" * 70)

    # Load
    candidates = ['global_bleaching_environmental.csv',
                   '../data/global_bleaching_environmental.csv',
                   'data/global_bleaching_environmental.csv']
    if len(sys.argv) > 1:
        candidates.insert(0, sys.argv[1])

    csv_path = None
    for c in candidates:
        if os.path.exists(c):
            csv_path = c
            break
    if not csv_path:
        print("ERREUR: global_bleaching_environmental.csv introuvable.")
        sys.exit(1)

    df = load_data(csv_path)
    print(f"\n  {len(df):,} observations, {df['year'].min():.0f}-{df['year'].max():.0f}")
    print(f"  {df['ocean'].nunique()} océans, {df['realm'].nunique()} realms")
    print(f"  Bleaching: mean={df['bleaching'].mean():.1f}%, median={df['bleaching'].median():.1f}%")

    # ════════════════════════════════════════════════════════════
    # APPLY ALL PARTITIONS
    # ════════════════════════════════════════════════════════════
    print(f"\n{'=' * 70}")
    print(f"  CONSTRUCTION DES PARTITIONS")
    print(f"{'=' * 70}")

    ptype_cols = {}
    for pname, pdef in PARTITIONS.items():
        col = f'pt_{pname[:8]}'
        df[col] = pdef['func'](df)
        ptype_cols[pname] = col

        counts = df[col].value_counts()
        print(f"\n  {pname}:")
        print(f"    Motivation: {pdef['motivation']}")
        print(f"    baseline={counts.get('baseline', 0):,}, "
              f"input={counts.get('input', 0):,}, "
              f"structure={counts.get('structure', 0):,}")

    # ════════════════════════════════════════════════════════════
    # GLOBAL RESULTS
    # ════════════════════════════════════════════════════════════
    print(f"\n{'=' * 70}")
    print(f"  RÉSULTATS GLOBAUX")
    print(f"{'=' * 70}")

    global_results = {}
    for pname, col in ptype_cols.items():
        inp = df.loc[df[col] == 'input', 'bleaching'].values
        stc = df.loc[df[col] == 'structure', 'bleaching'].values
        r = compute_ratio_stats(inp, stc)
        if r:
            global_results[pname] = r
            eff = "négligeable" if r['abs_d'] < 0.2 else (
                "faible" if r['abs_d'] < 0.5 else (
                    "moyen" if r['abs_d'] < 0.8 else "FORT"))
            print(f"\n  {pname}:")
            print(f"    INPUT (n={r['n_input']:,}): mean={r['mean_input']:.2f}%")
            print(f"    STRUCTURE (n={r['n_structure']:,}): mean={r['mean_structure']:.2f}%")
            print(f"    Ratio = {r['ratio']:.3f}×")
            print(f"    d = {r['d']:.4f} ({eff}), p = {r['p_MW']:.2e}")

            # Bootstrap
            boot = bootstrap_ratio(df, col, n_boot=5000)
            global_results[pname]['bootstrap'] = boot
            print(f"    Bootstrap: {boot['mean']:.3f}× "
                  f"IC95 [{boot['ci_95'][0]:.3f}, {boot['ci_95'][1]:.3f}]")

    # ════════════════════════════════════════════════════════════
    # CV BY OCEAN (the critical test)
    # ════════════════════════════════════════════════════════════
    print(f"\n{'=' * 70}")
    print(f"  CV PAR OCÉAN (analogue du CV par cancer type)")
    print(f"{'=' * 70}")

    cv_results = {}
    for pname, col in ptype_cols.items():
        cv = compute_cv_by_region(df, col, 'ocean')
        if cv:
            cv_results[pname] = cv
            print(f"\n  {pname}:")
            print(f"    N océans: {cv['n_regions']}")
            print(f"    Ratio moyen: {cv['mean_ratio']:.3f}×")
            print(f"    ★ CV = {cv['cv_ratio']:.1f}%")
            print(f"    Range: [{cv['min_ratio']:.3f}, {cv['max_ratio']:.3f}]")
            for pr in sorted(cv['per_region'], key=lambda x: x['ratio']):
                sig = '*' if pr['p'] < 0.05 else ' '
                print(f"      {pr['region']:<30s}: {pr['ratio']:.3f}× "
                      f"p={pr['p']:.2e} (n_i={pr['n_input']}, n_s={pr['n_structure']}) {sig}")

    # Also by realm
    print(f"\n  ── CV par realm ──")
    cv_realm = {}
    for pname, col in ptype_cols.items():
        cv = compute_cv_by_region(df, col, 'realm')
        if cv:
            cv_realm[pname] = cv
            print(f"  {pname}: CV={cv['cv_ratio']:.1f}% "
                  f"({cv['n_regions']} realms, range [{cv['min_ratio']:.3f}, {cv['max_ratio']:.3f}])")

    # ════════════════════════════════════════════════════════════
    # RANDOM PARTITIONS
    # ════════════════════════════════════════════════════════════
    print(f"\n{'=' * 70}")
    print(f"  CONTRÔLE: {N_RANDOM} partitions aléatoires")
    print(f"  (assignation aléatoire input/structure parmi DHW ≥ 4)")
    print(f"{'=' * 70}")

    # Stressed observations only
    stressed = df[df['dhw'] >= 4].copy()
    n_stressed = len(stressed)

    # Get ontodynamic input count as target size
    onto_col = ptype_cols['Ontodynamique']
    n_onto_input = (df[onto_col] == 'input').sum()
    frac_input = n_onto_input / ((df[onto_col] == 'input').sum() + (df[onto_col] == 'structure').sum())

    rng = np.random.RandomState(42)
    random_ratios = []
    random_cvs = []

    for _ in range(N_RANDOM):
        # Random split of stressed observations
        n_input_rand = int(len(stressed) * frac_input)
        perm = rng.permutation(len(stressed))
        rand_labels = np.array(['structure'] * len(stressed))
        rand_labels[perm[:n_input_rand]] = 'input'
        stressed['_rand'] = rand_labels

        inp = stressed.loc[stressed['_rand'] == 'input', 'bleaching'].values
        stc = stressed.loc[stressed['_rand'] == 'structure', 'bleaching'].values

        m_inp = np.mean(inp)
        if m_inp > 0.01:
            ratio = np.mean(stc) / m_inp
            random_ratios.append(ratio)

        # CV by ocean
        region_ratios = []
        for reg, grp in stressed.groupby('ocean'):
            if len(grp) < MIN_OBS_PER_REGION:
                continue
            ri = grp.loc[grp['_rand'] == 'input', 'bleaching'].values
            rs = grp.loc[grp['_rand'] == 'structure', 'bleaching'].values
            if len(ri) >= 10 and len(rs) >= 10 and np.mean(ri) > 0.01:
                region_ratios.append(np.mean(rs) / np.mean(ri))

        if len(region_ratios) >= 2:
            arr = np.array(region_ratios)
            cv = float(np.std(arr, ddof=1) / np.mean(arr) * 100) if np.mean(arr) > 0 else float('inf')
            if np.isfinite(cv):
                random_cvs.append(cv)

    random_ratios = np.array(random_ratios)
    random_cvs = np.array(random_cvs)

    print(f"  Ratio global: médiane = {np.median(random_ratios):.3f}×, "
          f"IQR = [{np.percentile(random_ratios, 25):.3f}, {np.percentile(random_ratios, 75):.3f}]")

    if 'Ontodynamique' in global_results:
        onto_ratio = global_results['Ontodynamique']['ratio']
        pct = float(np.mean(random_ratios >= onto_ratio) * 100)
        print(f"\n  Ratio ontodynamique ({onto_ratio:.3f}×) :")
        print(f"    {int(np.sum(random_ratios >= onto_ratio))}/{N_RANDOM} aléatoires ≥")
        print(f"    → percentile {100-pct:.1f}%")

    if len(random_cvs) > 0:
        print(f"\n  CV aléatoire: médiane = {np.median(random_cvs):.1f}%, "
              f"IQR = [{np.percentile(random_cvs, 25):.1f}%, {np.percentile(random_cvs, 75):.1f}%]")

    # ════════════════════════════════════════════════════════════
    # SUMMARY TABLE
    # ════════════════════════════════════════════════════════════
    print(f"\n{'=' * 70}")
    print(f"  TABLE RÉCAPITULATIVE")
    print(f"{'=' * 70}")

    print(f"\n  {'Partition':<22s} {'Ratio':>7s} {'d':>7s} {'p':>10s} "
          f"{'Boot CI':>18s} {'CV ocean':>9s} {'CV realm':>9s}")
    print(f"  {'─'*22} {'─'*7} {'─'*7} {'─'*10} {'─'*18} {'─'*9} {'─'*9}")

    for pname in PARTITIONS:
        gr = global_results.get(pname)
        cv_o = cv_results.get(pname)
        cv_r = cv_realm.get(pname)
        if gr:
            boot = gr.get('bootstrap', {})
            ci_str = f"[{boot['ci_95'][0]:.2f}, {boot['ci_95'][1]:.2f}]" if boot else "—"
            cv_o_str = f"{cv_o['cv_ratio']:.1f}%" if cv_o else "—"
            cv_r_str = f"{cv_r['cv_ratio']:.1f}%" if cv_r else "—"
            sig = '***' if gr['p_MW'] < 0.001 else ('**' if gr['p_MW'] < 0.01 else (
                '*' if gr['p_MW'] < 0.05 else ' '))
            print(f"  {pname:<22s} {gr['ratio']:>6.3f}× {gr['d']:>7.4f} "
                  f"{gr['p_MW']:>9.2e}{sig} {ci_str:>18s} {cv_o_str:>9s} {cv_r_str:>9s}")

    if len(random_ratios) > 0:
        cv_r_med = f"{np.median(random_cvs):.1f}%" if len(random_cvs) > 0 else "—"
        print(f"  {'Aléatoire (méd.)':<22s} {np.median(random_ratios):>6.3f}× {'—':>7s} "
              f"{'—':>10s} {'—':>18s} {cv_r_med:>9s} {'—':>9s}")

    # ════════════════════════════════════════════════════════════
    # VISUALIZATION
    # ════════════════════════════════════════════════════════════
    print(f"\n{'=' * 70}")
    print(f"  FIGURES")
    print(f"{'=' * 70}")

    colors = {
        'Ontodynamique': '#1565C0',
        'SSTA (température)': '#6A1B9A',
        'Profondeur': '#E65100',
        'Cyclone seul': '#2E7D32',
    }

    fig, axes = plt.subplots(2, 2, figsize=(14, 11))
    fig.suptitle('R-XVII Rival Partition Test — Coral Reefs (GCBD)\n'
                 'van Woesik & Kratochwill 2022, n={:,}'.format(len(df)),
                 fontsize=13, fontweight='bold')

    # Panel 1: Ratio comparison
    ax = axes[0, 0]
    names = [p for p in PARTITIONS if p in global_results]
    vals = [global_results[p]['ratio'] for p in names]
    cols_bar = [colors.get(p, '#9E9E9E') for p in names]
    bars = ax.bar(range(len(names)), vals, color=cols_bar, alpha=0.8, edgecolor='black')
    if len(random_ratios) > 0:
        ax.axhline(np.median(random_ratios), color='gray', ls='--', lw=1.5,
                   label=f'Aléatoire (méd. {np.median(random_ratios):.3f}×)')
    ax.axhline(1.0, color='gray', ls=':', lw=0.5)
    ax.set_xticks(range(len(names)))
    ax.set_xticklabels(names, fontsize=8, rotation=15)
    ax.set_ylabel('Ratio S/I')
    ax.set_title('Ratio par partition')
    ax.legend(fontsize=8)
    for i, v in enumerate(vals):
        ax.text(i, v + 0.02, f'{v:.2f}×', ha='center', fontsize=9, fontweight='bold')

    # Panel 2: CV comparison
    ax = axes[0, 1]
    cv_names = [p for p in PARTITIONS if p in cv_results]
    cv_vals = [cv_results[p]['cv_ratio'] for p in cv_names]
    cv_cols = [colors.get(p, '#9E9E9E') for p in cv_names]
    if len(random_cvs) > 0:
        cv_names.append('Aléatoire\n(méd.)')
        cv_vals.append(float(np.median(random_cvs)))
        cv_cols.append('#9E9E9E')
    if cv_vals:
        bars = ax.bar(range(len(cv_names)), cv_vals, color=cv_cols, alpha=0.8, edgecolor='black')
        ax.set_xticks(range(len(cv_names)))
        ax.set_xticklabels(cv_names, fontsize=8, rotation=15)
        ax.set_ylabel('CV (%)')
        ax.set_title('CV du ratio par océan\n(plus bas = plus stable)')
        for i, v in enumerate(cv_vals):
            ax.text(i, v + 0.5, f'{v:.1f}%', ha='center', fontsize=9, fontweight='bold')

    # Panel 3: Random distribution
    ax = axes[1, 0]
    if len(random_ratios) > 0:
        ax.hist(random_ratios, bins=50, alpha=0.6, color='#9E9E9E', density=True,
                label='Aléatoires')
        for pname in PARTITIONS:
            if pname in global_results:
                ax.axvline(global_results[pname]['ratio'], color=colors.get(pname, 'black'),
                           lw=2.5, label=f"{pname}: {global_results[pname]['ratio']:.2f}×")
        ax.set_xlabel('Ratio S/I')
        ax.set_ylabel('Densité')
        ax.set_title(f'Ratio observé vs {N_RANDOM} aléatoires')
        ax.legend(fontsize=7)

    # Panel 4: Per-ocean ratios
    ax = axes[1, 1]
    if cv_results:
        y_offset = 0
        for pname in ['Ontodynamique', 'SSTA (température)', 'Cyclone seul']:
            if pname not in cv_results:
                continue
            regions = cv_results[pname]['per_region']
            reg_names = [r['region'][:20] for r in regions]
            reg_ratios = [r['ratio'] for r in regions]
            y_pos = np.arange(len(reg_names)) * 1.5 + y_offset
            ax.barh(y_pos, reg_ratios, 0.4, color=colors.get(pname, '#9E9E9E'),
                    alpha=0.7, label=pname)
            y_offset += 0.5

        ax.axvline(1.0, color='gray', ls=':', lw=0.5)
        ax.set_xlabel('Ratio S/I')
        ax.set_title('Ratio par océan et partition')
        ax.legend(fontsize=7)

    plt.tight_layout()
    fig_path = 'rXVII_rival_partitions_reef.png'
    plt.savefig(fig_path, dpi=200, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"  → {fig_path}")

    # ════════════════════════════════════════════════════════════
    # EXPORT JSON
    # ════════════════════════════════════════════════════════════
    export = {
        'protocol': 'R-XVII rival partition test — Coral Reefs (GCBD)',
        'source': 'van Woesik & Kratochwill 2022',
        'n_obs': len(df),
        'n_random': N_RANDOM,
        'global': {},
        'cv_ocean': {},
        'cv_realm': {},
    }
    for pname in PARTITIONS:
        if pname in global_results:
            r = global_results[pname]
            export['global'][pname] = {k: v for k, v in r.items() if k != 'bootstrap'}
            if 'bootstrap' in r:
                export['global'][pname]['bootstrap'] = r['bootstrap']
        if pname in cv_results:
            export['cv_ocean'][pname] = cv_results[pname]
        if pname in cv_realm:
            export['cv_realm'][pname] = cv_realm[pname]

    if len(random_ratios) > 0:
        export['random'] = {
            'ratio_median': float(np.median(random_ratios)),
            'ratio_max': float(np.max(random_ratios)),
            'cv_median': float(np.median(random_cvs)) if len(random_cvs) > 0 else None,
        }

    def nc(o):
        if isinstance(o, (np.integer,)): return int(o)
        if isinstance(o, (np.floating,)): return float(o)
        if isinstance(o, np.ndarray): return o.tolist()
        if isinstance(o, np.bool_): return bool(o)
        raise TypeError(f"{type(o)}")

    json_path = 'rXVII_rival_partitions_reef.json'
    with open(json_path, 'w') as f:
        json.dump(export, f, indent=2, default=nc)
    print(f"  → {json_path}")

    # ════════════════════════════════════════════════════════════
    # VERDICT
    # ════════════════════════════════════════════════════════════
    print(f"\n{'=' * 70}")
    print(f"  VERDICT")
    print(f"{'=' * 70}")

    if 'Ontodynamique' in global_results:
        onto = global_results['Ontodynamique']
        rivals = {p: global_results[p] for p in global_results if p != 'Ontodynamique'}

        print(f"\n  Ontodynamique: ratio={onto['ratio']:.3f}×, d={onto['d']:.4f}, p={onto['p_MW']:.2e}")
        for p, r in rivals.items():
            print(f"  {p}: ratio={r['ratio']:.3f}×, d={r['d']:.4f}, p={r['p_MW']:.2e}")

        onto_best = all(onto['ratio'] > r['ratio'] for r in rivals.values())
        onto_pct = float(np.mean(random_ratios >= onto['ratio']) * 100) if len(random_ratios) > 0 else 50

        onto_cv = cv_results.get('Ontodynamique', {}).get('cv_ratio', float('inf'))
        rival_cvs = {p: cv_results.get(p, {}).get('cv_ratio', float('inf')) for p in rivals}

        print(f"\n  CV océan — Ontodynamique: {onto_cv:.1f}%")
        for p, cv in rival_cvs.items():
            print(f"  CV océan — {p}: {cv:.1f}%")

        if onto_best and onto_pct < 0.1:
            print(f"\n  ★ RÉSULTAT FORT: la partition ontodynamique a le ratio le plus")
            print(f"    élevé, surpasse {100-onto_pct:.1f}% des aléatoires.")
        elif onto_pct < 1:
            print(f"\n  ★ RÉSULTAT MODÉRÉ: percentile {100-onto_pct:.1f}% des aléatoires.")
        else:
            print(f"\n  ★ RÉSULTAT: percentile {100-onto_pct:.1f}% des aléatoires.")

    elapsed = time.time() - t0
    print(f"\n  Temps: {elapsed:.1f}s")


if __name__ == '__main__':
    main()