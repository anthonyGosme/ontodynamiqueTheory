#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════
  ROBUSTNESS — R-XVII YEAST (Yeast Phenome / Hillenmeyer)

  Batterie de tests parallèle à robustness_reef.py :
  1. Transformations multiples (|z|, z², binary, rank)
  2. Analyse par catégorie de drogue (≡ par océan)
  3. Sensitivity sweep (seuil de sévérité)
  4. Bootstrap CI sous chaque transformation
  5. Permutation par catégorie

  Ontodynamique — A. Gosme, 2026
═══════════════════════════════════════════════════════════

Usage:
  python3 robustness_yeast.py \
    --matrix yp_matrix_z_haphom_20221025.txt \
    --screens yp_screens_haphom_20221025.txt \
    --gaf gene_association.sgd.20251124.gaf
"""

import argparse
import json
import os
import warnings
from collections import defaultdict
from datetime import datetime

import numpy as np
import pandas as pd
from scipy import stats

warnings.filterwarnings('ignore')

# ═══════════════════════════════════════════════════════════
# PARTITION (frozen 2026-03-13, identical to RXVII.py)
# ═══════════════════════════════════════════════════════════

STRUCTURE_TERMS = {
    'GO:0006281', 'GO:0043161', 'GO:0006457', 'GO:0030433',
    'GO:0000278', 'GO:0000280', 'GO:0000281', 'GO:0051726', 'GO:0007346',
    'GO:0000082', 'GO:0000086', 'GO:0051301',
    'GO:0006260', 'GO:0006261',
    'GO:0009272', 'GO:0071555',
    'GO:0007005',
    'GO:0042254', 'GO:0042273', 'GO:0042274',
    'GO:0006325', 'GO:0006265', 'GO:0007059',
}

INPUT_TERMS = {
    'GO:0007165', 'GO:0000165', 'GO:0007264', 'GO:0007186',
    'GO:0031929', 'GO:0032008', 'GO:0038202',
    'GO:0006468',
    'GO:0055085', 'GO:0006811', 'GO:0006812', 'GO:0006813', 'GO:0006814',
    'GO:0006826', 'GO:0006865', 'GO:0015078', 'GO:0034220', 'GO:0055072',
    'GO:0006970', 'GO:0009408', 'GO:0034599',
    'GO:0071470', 'GO:0071472', 'GO:0071474',
}

# ═══════════════════════════════════════════════════════════
# DRUG CATEGORIES for Hillenmeyer screens
# (≡ ocean/realm in coral analysis)
# ═══════════════════════════════════════════════════════════

DRUG_CATEGORIES = {
    'DNA damage': [
        'MMS', '4-nitroquinoline', 'BCNU', 'oxaliplatin', 'radiation',
        'streptozotocin', 'K2Cr2O7', 'psoralen', 'thio-tepa', 'teniposide',
        'aclarubicin', '5-fluoro-uracil', 'HU', 'camptothecin',
        'cisplatin', 'streptovitacin', 'mitomycin',
    ],
    'Oxidative stress': [
        'paraquat', 'nitric oxide', 'rotenone', 'hydrogen peroxide',
        'sodium arsenite', 'potassium disulfite', 'MPP+',
    ],
    'Osmotic/salt': [
        'sodium chloride', 'sorbitol', 'NaF', 'zinc chloride',
        'acetic acid', 'pH',
    ],
    'Temperature': [
        'temperature',
    ],
    'Cell wall/membrane': [
        'nystatin', 'nocodazole', 'thiabendazole', 'rhizoxin',
        'papuamide', 'norcantharidin', 'wiskostatin',
    ],
    'Signaling inhibitors': [
        'rapamycin', 'FK506', 'wortmannin', 'staurosporine',
        'tyrphostin', 'AG 957', 'RO 106',
    ],
}


# ═══════════════════════════════════════════════════════════
# LOADING (reused from RXVII.py)
# ═══════════════════════════════════════════════════════════

def load_gaf(gaf_path):
    gene_go = defaultdict(set)
    gene_to_orf = {}
    orf_to_gene = {}
    with open(gaf_path, 'r') as f:
        for line in f:
            if line.startswith('!'):
                continue
            parts = line.strip().split('\t')
            if len(parts) < 15:
                continue
            gene = parts[2]
            qualifier = parts[3]
            go_id = parts[4]
            synonyms = parts[10]
            if 'NOT' in qualifier:
                continue
            gene_go[gene].add(go_id)
            if synonyms:
                for syn in synonyms.split('|'):
                    syn = syn.strip()
                    if syn.startswith('Y') and len(syn) >= 7 and syn[1] in 'ABCDEFGHIJKLMNOP':
                        gene_to_orf[gene] = syn
                        orf_to_gene[syn] = gene
                        break
    return gene_go, gene_to_orf, orf_to_gene


def classify_genes(gene_go):
    struct_genes = set()
    input_genes = set()
    for gene, gos in gene_go.items():
        if gos & STRUCTURE_TERMS:
            struct_genes.add(gene)
        if gos & INPUT_TERMS:
            input_genes.add(gene)
    both = struct_genes & input_genes
    return struct_genes - both, input_genes - both, both


def map_to_matrix(genes, gene_to_orf, matrix_index):
    orfs = set()
    for g in genes:
        orf = gene_to_orf.get(g)
        if orf and orf in matrix_index:
            orfs.add(orf)
        elif g in matrix_index:
            orfs.add(g)
    return sorted(orfs)


def categorize_screen(conditionset):
    """Assign a Hillenmeyer screen to a drug category."""
    cond_lower = conditionset.lower() if isinstance(conditionset, str) else ''
    for cat, keywords in DRUG_CATEGORIES.items():
        for kw in keywords:
            if kw.lower() in cond_lower:
                return cat
    return 'Other'


# ═══════════════════════════════════════════════════════════
# TEST 1: TRANSFORMATIONS MULTIPLES
# (≡ arcsin/log/binary in robustness_reef.py)
# ═══════════════════════════════════════════════════════════

def test_transformations(matrix, screen_ids, s_orfs, i_orfs):
    """Test R-XVII under multiple severity transformations."""
    print("\n" + "=" * 65)
    print("  TEST 1: TRANSFORMATIONS MULTIPLES")
    print("=" * 65)

    cols = [c for c in screen_ids if c in matrix.columns]
    s_data = matrix.loc[matrix.index.isin(s_orfs), cols]
    i_data = matrix.loc[matrix.index.isin(i_orfs), cols]

    transforms = {
        '|z| (original)': lambda x: x.abs().mean(axis=1),
        'z²': lambda x: (x ** 2).mean(axis=1),
        'binary(|z|>2)': lambda x: (x.abs() > 2).mean(axis=1),
        'binary(|z|>3)': lambda x: (x.abs() > 3).mean(axis=1),
        'rank': lambda x: x.abs().mean(axis=1).rank(pct=True),
        'log1p(|z|)': lambda x: np.log1p(x.abs()).mean(axis=1),
    }

    results = {}
    print(f"\n  {'Transform':<20s} {'N_S':>5s} {'N_I':>5s} {'Ratio':>7s} "
          f"{'CI_lo':>7s} {'CI_hi':>7s} {'p':>10s} {'d':>6s}")
    print(f"  {'-' * 20} {'-' * 5} {'-' * 5} {'-' * 7} {'-' * 7} {'-' * 7} {'-' * 10} {'-' * 6}")

    for name, tfn in transforms.items():
        s_sev = tfn(s_data).dropna()
        i_sev = tfn(i_data).dropna()

        if len(s_sev) < 10 or len(i_sev) < 10:
            continue

        is_binary = 'binary' in name

        if is_binary:
            # For binary: use proportion test
            s_mean = s_sev.mean()
            i_mean = i_sev.mean()
            ratio = s_mean / i_mean if i_mean > 0 else np.nan
            # Cohen's h for proportions
            d = 2 * (np.arcsin(np.sqrt(s_mean)) - np.arcsin(np.sqrt(i_mean)))
            # Mann-Whitney still works for comparing proportions
            _, p = stats.mannwhitneyu(s_sev, i_sev, alternative='greater')
        else:
            s_mean = s_sev.mean()
            i_mean = i_sev.mean()
            ratio = s_mean / i_mean if i_mean > 0 else np.nan
            _, p = stats.mannwhitneyu(s_sev, i_sev, alternative='greater')
            pooled = np.sqrt((s_sev.std() ** 2 + i_sev.std() ** 2) / 2)
            d = (s_mean - i_mean) / pooled if pooled > 0 else 0

        # Bootstrap CI on ratio
        rng = np.random.RandomState(42)
        boot = []
        for _ in range(10000):
            sb = rng.choice(s_sev.values, len(s_sev), replace=True)
            ib = rng.choice(i_sev.values, len(i_sev), replace=True)
            if np.mean(ib) > 0:
                boot.append(np.mean(sb) / np.mean(ib))
        boot = np.array(boot)
        ci = np.percentile(boot, [2.5, 97.5])

        results[name] = {
            'ratio': float(ratio), 'p': float(p), 'd': float(d),
            'ci_lo': float(ci[0]), 'ci_hi': float(ci[1]),
            'n_s': len(s_sev), 'n_i': len(i_sev),
            's_mean': float(s_mean), 'i_mean': float(i_mean),
        }

        print(f"  {name:<20s} {len(s_sev):>5d} {len(i_sev):>5d} {ratio:>7.3f} "
              f"{ci[0]:>7.3f} {ci[1]:>7.3f} {p:>10.2e} {d:>6.3f}")

    # Verdict
    n_sig = sum(1 for r in results.values() if r['p'] < 0.05 and r['ratio'] > 1)
    print(f"\n  Verdict: {n_sig}/{len(results)} transformations significatives (p<0.05, ratio>1)")

    return results


# ═══════════════════════════════════════════════════════════
# TEST 2: PAR CATÉGORIE DE DROGUE
# (≡ test_regional dans corail.py)
# ═══════════════════════════════════════════════════════════

def test_by_drug_category(matrix, screens_df, s_orfs, i_orfs):
    """Test R-XVII separately per drug category."""
    print("\n" + "=" * 65)
    print("  TEST 2: PAR CATÉGORIE DE DROGUE (≡ par océan)")
    print("=" * 65)

    # Assign categories to Hillenmeyer screens
    hill_mask = screens_df['paper'].str.contains('Hillenmeyer', case=False, na=False)
    hill_screens = screens_df[hill_mask].copy()
    hill_screens['category'] = hill_screens['conditionset'].apply(categorize_screen)

    cat_counts = hill_screens['category'].value_counts()
    print(f"\n  Catégories de drogues ({len(hill_screens)} screens Hillenmeyer):")
    for cat, n in cat_counts.items():
        print(f"    {cat:<25s}: {n:>3d} screens")

    results = {}
    print(f"\n  {'Catégorie':<25s} {'N_scr':>5s} {'N_S':>5s} {'N_I':>5s} "
          f"{'Ratio':>7s} {'CI_lo':>7s} {'CI_hi':>7s} {'p':>10s} {'d':>6s}")
    print(f"  {'-' * 25} {'-' * 5} {'-' * 5} {'-' * 5} {'-' * 7} {'-' * 7} {'-' * 7} {'-' * 10} {'-' * 6}")

    for cat in cat_counts.index:
        cat_ids = hill_screens.loc[hill_screens['category'] == cat, 'id'].astype(str).tolist()
        cols = [c for c in cat_ids if c in matrix.columns]

        if len(cols) < 3:
            continue

        s_data = matrix.loc[matrix.index.isin(s_orfs), cols]
        i_data = matrix.loc[matrix.index.isin(i_orfs), cols]

        s_sev = s_data.abs().mean(axis=1).dropna()
        i_sev = i_data.abs().mean(axis=1).dropna()

        if len(s_sev) < 10 or len(i_sev) < 10:
            continue

        ratio = s_sev.mean() / i_sev.mean() if i_sev.mean() > 0 else np.nan
        _, p = stats.mannwhitneyu(s_sev, i_sev, alternative='greater')
        pooled = np.sqrt((s_sev.std() ** 2 + i_sev.std() ** 2) / 2)
        d = (s_sev.mean() - i_sev.mean()) / pooled if pooled > 0 else 0

        # Bootstrap CI
        rng = np.random.RandomState(42)
        boot = []
        for _ in range(10000):
            sb = rng.choice(s_sev.values, len(s_sev), replace=True)
            ib = rng.choice(i_sev.values, len(i_sev), replace=True)
            if np.mean(ib) > 0:
                boot.append(np.mean(sb) / np.mean(ib))
        boot = np.array(boot)
        ci = np.percentile(boot, [2.5, 97.5])

        results[cat] = {
            'n_screens': len(cols), 'ratio': float(ratio),
            'p': float(p), 'd': float(d),
            'ci_lo': float(ci[0]), 'ci_hi': float(ci[1]),
            'n_s': len(s_sev), 'n_i': len(i_sev),
        }

        sig = "*" if p < 0.05 else " "
        print(f"  {cat:<25s} {len(cols):>5d} {len(s_sev):>5d} {len(i_sev):>5d} "
              f"{ratio:>7.3f} {ci[0]:>7.3f} {ci[1]:>7.3f} {p:>10.2e} {d:>6.3f} {sig}")

    n_sig = sum(1 for r in results.values() if r['p'] < 0.05 and r['ratio'] > 1)
    n_tot = len(results)
    print(f"\n  Verdict: {n_sig}/{n_tot} catégories avec S/I > 1 et p < 0.05")

    # Cross-category consistency
    if len(results) >= 2:
        ratios = [r['ratio'] for r in results.values() if not np.isnan(r['ratio'])]
        cv = np.std(ratios) / np.mean(ratios) * 100 if np.mean(ratios) > 0 else np.nan
        print(f"  CV inter-catégories: {cv:.1f}%")
        print(f"  Range: [{min(ratios):.3f}, {max(ratios):.3f}]")

    return results


# ═══════════════════════════════════════════════════════════
# TEST 3: SENSITIVITY SWEEP
# (≡ test_sensitivity dans corail.py, seuil DHW → seuil |z|)
# ═══════════════════════════════════════════════════════════

def test_sensitivity_sweep(matrix, screen_ids, s_orfs, i_orfs):
    """Sweep severity threshold and check ratio stability."""
    print("\n" + "=" * 65)
    print("  TEST 3: SENSITIVITY SWEEP (seuil de sévérité)")
    print("=" * 65)

    cols = [c for c in screen_ids if c in matrix.columns]
    s_data = matrix.loc[matrix.index.isin(s_orfs), cols]
    i_data = matrix.loc[matrix.index.isin(i_orfs), cols]

    # Compute per-gene mean |z| across Hillenmeyer screens
    s_sev = s_data.abs().mean(axis=1).dropna()
    i_sev = i_data.abs().mean(axis=1).dropna()

    # Sweep: only include genes above a severity threshold
    all_sev = pd.concat([s_sev, i_sev])

    sweep = []
    for pct in range(0, 91, 5):
        thr = np.percentile(all_sev, pct)
        s_above = s_sev[s_sev >= thr]
        i_above = i_sev[i_sev >= thr]

        if len(s_above) < 20 or len(i_above) < 20:
            continue

        ratio = s_above.mean() / i_above.mean() if i_above.mean() > 0 else np.nan
        _, p = stats.mannwhitneyu(s_above, i_above, alternative='greater')
        pooled = np.sqrt((s_above.std() ** 2 + i_above.std() ** 2) / 2)
        d = (s_above.mean() - i_above.mean()) / pooled if pooled > 0 else 0

        sweep.append({
            'percentile': pct, 'threshold': float(thr),
            'n_s': len(s_above), 'n_i': len(i_above),
            'ratio': float(ratio), 'p': float(p), 'd': float(d),
        })

    print(f"\n  {'Pctl':>5s} {'Thr':>7s} {'N_S':>5s} {'N_I':>5s} "
          f"{'Ratio':>7s} {'p':>10s} {'d':>6s}")
    print(f"  {'-' * 5} {'-' * 7} {'-' * 5} {'-' * 5} {'-' * 7} {'-' * 10} {'-' * 6}")

    for s in sweep:
        sig = "*" if s['p'] < 0.05 else " "
        print(f"  {s['percentile']:>5d} {s['threshold']:>7.3f} {s['n_s']:>5d} {s['n_i']:>5d} "
              f"{s['ratio']:>7.3f} {s['p']:>10.2e} {s['d']:>6.3f} {sig}")

    n_sig = sum(1 for s in sweep if s['p'] < 0.05 and s['ratio'] > 1)
    print(f"\n  Verdict: {n_sig}/{len(sweep)} seuils significatifs (p<0.05, ratio>1)")

    if sweep:
        ratios = [s['ratio'] for s in sweep]
        print(f"  Range ratios: [{min(ratios):.3f}, {max(ratios):.3f}]")
        print(f"  CV: {np.std(ratios) / np.mean(ratios) * 100:.1f}%")

    return sweep


# ═══════════════════════════════════════════════════════════
# TEST 4: BOOTSTRAP CI PAR TRANSFORMATION
# (≡ test_bootstrap dans corail.py)
# ═══════════════════════════════════════════════════════════

def test_bootstrap_detailed(matrix, screen_ids, s_orfs, i_orfs, n_boot=10000):
    """Detailed bootstrap for main metric."""
    print("\n" + "=" * 65)
    print("  TEST 4: BOOTSTRAP CI DÉTAILLÉ (10K)")
    print("=" * 65)

    cols = [c for c in screen_ids if c in matrix.columns]
    s_sev = matrix.loc[matrix.index.isin(s_orfs), cols].abs().mean(axis=1).dropna()
    i_sev = matrix.loc[matrix.index.isin(i_orfs), cols].abs().mean(axis=1).dropna()

    rng = np.random.RandomState(42)
    boot_ratios = []
    boot_ds = []
    for _ in range(n_boot):
        sb = rng.choice(s_sev.values, len(s_sev), replace=True)
        ib = rng.choice(i_sev.values, len(i_sev), replace=True)
        if np.mean(ib) > 0:
            boot_ratios.append(np.mean(sb) / np.mean(ib))
        pooled = np.sqrt((np.std(sb) ** 2 + np.std(ib) ** 2) / 2)
        if pooled > 0:
            boot_ds.append((np.mean(sb) - np.mean(ib)) / pooled)

    boot_ratios = np.array(boot_ratios)
    boot_ds = np.array(boot_ds)

    print(f"\n  Ratio S/I:")
    print(f"    Mean:   {np.mean(boot_ratios):.3f}")
    print(f"    Median: {np.median(boot_ratios):.3f}")
    print(f"    CI 95%: [{np.percentile(boot_ratios, 2.5):.3f}, {np.percentile(boot_ratios, 97.5):.3f}]")
    print(f"    CI 99%: [{np.percentile(boot_ratios, 0.5):.3f}, {np.percentile(boot_ratios, 99.5):.3f}]")
    print(f"    P(ratio < 1): {np.mean(boot_ratios < 1):.6f}")

    print(f"\n  Cohen's d:")
    print(f"    Mean:   {np.mean(boot_ds):.3f}")
    print(f"    CI 95%: [{np.percentile(boot_ds, 2.5):.3f}, {np.percentile(boot_ds, 97.5):.3f}]")

    return {
        'ratio_mean': float(np.mean(boot_ratios)),
        'ratio_median': float(np.median(boot_ratios)),
        'ratio_ci95': [float(np.percentile(boot_ratios, 2.5)), float(np.percentile(boot_ratios, 97.5))],
        'ratio_ci99': [float(np.percentile(boot_ratios, 0.5)), float(np.percentile(boot_ratios, 99.5))],
        'p_below_1': float(np.mean(boot_ratios < 1)),
        'd_mean': float(np.mean(boot_ds)),
        'd_ci95': [float(np.percentile(boot_ds, 2.5)), float(np.percentile(boot_ds, 97.5))],
    }


# ═══════════════════════════════════════════════════════════
# TEST 5: PERMUTATION PAR CATÉGORIE
# (≡ per-region permutation)
# ═══════════════════════════════════════════════════════════

def test_permutation_by_category(matrix, screens_df, s_orfs, i_orfs, n_perms=10000):
    """Permutation test within each drug category."""
    print("\n" + "=" * 65)
    print("  TEST 5: PERMUTATION PAR CATÉGORIE (10K)")
    print("=" * 65)

    hill_mask = screens_df['paper'].str.contains('Hillenmeyer', case=False, na=False)
    hill_screens = screens_df[hill_mask].copy()
    hill_screens['category'] = hill_screens['conditionset'].apply(categorize_screen)

    results = {}

    for cat in hill_screens['category'].unique():
        cat_ids = hill_screens.loc[hill_screens['category'] == cat, 'id'].astype(str).tolist()
        cols = [c for c in cat_ids if c in matrix.columns]
        if len(cols) < 3:
            continue

        all_orfs = list(set(s_orfs) | set(i_orfs))
        sub = matrix.loc[matrix.index.isin(all_orfs), cols]
        severity = sub.abs().mean(axis=1).dropna()

        s_in = [o for o in severity.index if o in set(s_orfs)]
        i_in = [o for o in severity.index if o in set(i_orfs)]

        if len(s_in) < 10 or len(i_in) < 10:
            continue

        obs_ratio = severity[s_in].mean() / severity[i_in].mean() if severity[i_in].mean() > 0 else np.nan

        values = severity.values
        n_s = len(s_in)
        rng = np.random.RandomState(42)
        perm_ratios = []
        for _ in range(n_perms):
            idx = rng.permutation(len(values))
            sp = values[idx[:n_s]].mean()
            ip = values[idx[n_s:]].mean()
            if ip > 0:
                perm_ratios.append(sp / ip)
        perm_ratios = np.array(perm_ratios)
        p_perm = float(np.mean(perm_ratios >= obs_ratio))

        results[cat] = {
            'observed': float(obs_ratio),
            'perm_p': p_perm,
            'n_s': len(s_in), 'n_i': len(i_in),
            'n_screens': len(cols),
        }

        sig = "*" if p_perm < 0.05 else " "
        print(f"  {cat:<25s}: obs={obs_ratio:.3f}×, perm_p={p_perm:.4f} "
              f"(S={len(s_in)}, I={len(i_in)}, {len(cols)} screens) {sig}")

    n_sig = sum(1 for r in results.values() if r['perm_p'] < 0.05)
    print(f"\n  Verdict: {n_sig}/{len(results)} catégories avec perm_p < 0.05")

    return results


# ═══════════════════════════════════════════════════════════
# TEST 6: LEAVE-ONE-CATEGORY-OUT
# ═══════════════════════════════════════════════════════════

def test_leave_one_out(matrix, screens_df, s_orfs, i_orfs):
    """Remove one drug category at a time, check ratio stability."""
    print("\n" + "=" * 65)
    print("  TEST 6: LEAVE-ONE-CATEGORY-OUT")
    print("=" * 65)

    hill_mask = screens_df['paper'].str.contains('Hillenmeyer', case=False, na=False)
    hill_screens = screens_df[hill_mask].copy()
    hill_screens['category'] = hill_screens['conditionset'].apply(categorize_screen)

    all_hill_ids = hill_screens['id'].astype(str).tolist()

    # Baseline (all Hillenmeyer)
    cols_all = [c for c in all_hill_ids if c in matrix.columns]
    s_sev_all = matrix.loc[matrix.index.isin(s_orfs), cols_all].abs().mean(axis=1).dropna()
    i_sev_all = matrix.loc[matrix.index.isin(i_orfs), cols_all].abs().mean(axis=1).dropna()
    baseline_ratio = s_sev_all.mean() / i_sev_all.mean() if i_sev_all.mean() > 0 else np.nan

    print(f"\n  Baseline (all 273 screens): {baseline_ratio:.3f}×")
    print(f"\n  {'Catégorie retirée':<25s} {'N_rem':>5s} {'Ratio':>7s} {'Δ':>7s} {'p':>10s}")
    print(f"  {'-' * 25} {'-' * 5} {'-' * 7} {'-' * 7} {'-' * 10}")

    results = {}
    for cat in hill_screens['category'].unique():
        cat_ids = set(hill_screens.loc[hill_screens['category'] == cat, 'id'].astype(str).tolist())
        remaining_ids = [c for c in all_hill_ids if c not in cat_ids]
        cols = [c for c in remaining_ids if c in matrix.columns]

        if len(cols) < 10:
            continue

        s_sev = matrix.loc[matrix.index.isin(s_orfs), cols].abs().mean(axis=1).dropna()
        i_sev = matrix.loc[matrix.index.isin(i_orfs), cols].abs().mean(axis=1).dropna()

        ratio = s_sev.mean() / i_sev.mean() if i_sev.mean() > 0 else np.nan
        _, p = stats.mannwhitneyu(s_sev, i_sev, alternative='greater')
        delta = ratio - baseline_ratio

        results[cat] = {
            'ratio': float(ratio), 'delta': float(delta),
            'p': float(p), 'n_removed': len(cat_ids),
        }

        print(f"  {cat:<25s} {len(cat_ids):>5d} {ratio:>7.3f} {delta:>+7.3f} {p:>10.2e}")

    if results:
        ratios = [r['ratio'] for r in results.values()]
        print(f"\n  Stabilité: range [{min(ratios):.3f}, {max(ratios):.3f}]")
        print(f"  Max |Δ| = {max(abs(r['delta']) for r in results.values()):.3f}")
        all_sig = all(r['p'] < 0.05 for r in results.values())
        print(f"  Toutes les variantes significatives ? {'OUI' if all_sig else 'NON'}")

    return results


# ═══════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description='R-XVII Yeast Robustness Tests')
    parser.add_argument('--matrix', required=True)
    parser.add_argument('--screens', required=True)
    parser.add_argument('--gaf', required=True)
    args = parser.parse_args()

    print("═" * 65)
    print("  ROBUSTNESS — R-XVII YEAST (Hillenmeyer)")
    print("  Batterie parallèle à robustness_reef.py")
    print("═" * 65)

    # Load
    print("\n[LOAD] GO annotations...")
    gene_go, gene_to_orf, orf_to_gene = load_gaf(args.gaf)
    s_genes, i_genes, both = classify_genes(gene_go)
    print(f"  Partition: S={len(s_genes)}, I={len(i_genes)}, BOTH={len(both)}")

    print("\n[LOAD] Screens metadata...")
    screens_df = pd.read_csv(args.screens, sep='\t')
    hill_mask = screens_df['paper'].str.contains('Hillenmeyer', case=False, na=False)
    hill_ids = screens_df.loc[hill_mask, 'id'].astype(str).tolist()
    print(f"  Hillenmeyer screens: {len(hill_ids)}")

    print("\n[LOAD] Z-score matrix (may take a few minutes)...")
    matrix = pd.read_csv(args.matrix, sep='\t', index_col=0, low_memory=False)
    matrix.columns = matrix.columns.astype(str)
    print(f"  Matrix: {matrix.shape[0]} genes × {matrix.shape[1]} screens")

    # Map genes to ORFs in matrix
    s_orfs = map_to_matrix(s_genes, gene_to_orf, matrix.index)
    i_orfs = map_to_matrix(i_genes, gene_to_orf, matrix.index)
    print(f"  Matched: S={len(s_orfs)}, I={len(i_orfs)}")

    # Run all tests
    r1 = test_transformations(matrix, hill_ids, s_orfs, i_orfs)
    r2 = test_by_drug_category(matrix, screens_df, s_orfs, i_orfs)
    r3 = test_sensitivity_sweep(matrix, hill_ids, s_orfs, i_orfs)
    r4 = test_bootstrap_detailed(matrix, hill_ids, s_orfs, i_orfs)
    r5 = test_permutation_by_category(matrix, screens_df, s_orfs, i_orfs)
    r6 = test_leave_one_out(matrix, screens_df, s_orfs, i_orfs)

    # ═══════════════════════════════════════════════════════
    # SUMMARY
    # ═══════════════════════════════════════════════════════
    print("\n" + "═" * 65)
    print("  RÉSUMÉ ROBUSTESSE — R-XVII LEVURE")
    print("═" * 65)

    n1_sig = sum(1 for r in r1.values() if r['p'] < 0.05 and r['ratio'] > 1)
    n2_sig = sum(1 for r in r2.values() if r['p'] < 0.05 and r['ratio'] > 1)
    n3_sig = sum(1 for s in r3 if s['p'] < 0.05 and s['ratio'] > 1)
    n5_sig = sum(1 for r in r5.values() if r['perm_p'] < 0.05)
    n6_all = all(r['p'] < 0.05 for r in r6.values()) if r6 else False

    print(f"\n  Test 1 — Transformations:     {n1_sig}/{len(r1)} significatives")
    print(f"  Test 2 — Par drogue:          {n2_sig}/{len(r2)} catégories S/I>1, p<0.05")
    print(f"  Test 3 — Sensitivity sweep:   {n3_sig}/{len(r3)} seuils significatifs")
    print(f"  Test 4 — Bootstrap CI 95%:    [{r4['ratio_ci95'][0]:.3f}, {r4['ratio_ci95'][1]:.3f}]")
    print(f"  Test 4 — P(ratio<1):          {r4['p_below_1']:.6f}")
    print(f"  Test 5 — Perm par catégorie:  {n5_sig}/{len(r5)} catégories perm_p<0.05")
    print(f"  Test 6 — Leave-one-out:       {'STABLE' if n6_all else 'INSTABLE'}")

    # Overall verdict
    checks = [
        n1_sig >= len(r1) * 0.8,  # ≥80% transforms significant
        n2_sig >= len(r2) * 0.5,  # ≥50% drug categories
        n3_sig >= len(r3) * 0.8,  # ≥80% thresholds
        r4['ratio_ci95'][0] > 1.0,  # CI doesn't cross 1
        r4['p_below_1'] < 0.001,  # Probability of ratio<1 is negligible
        n5_sig >= len(r5) * 0.5,  # ≥50% categories pass permutation
        n6_all,  # All leave-one-out pass
    ]
    n_pass = sum(checks)

    print(f"\n  Critères passés: {n_pass}/7")
    if n_pass >= 6:
        verdict = "SUCCÈS FORT"
    elif n_pass >= 4:
        verdict = "SUCCÈS MODÉRÉ"
    else:
        verdict = "ÉCHEC INFORMATIF"
    print(f"  VERDICT: {verdict}")
    print("═" * 65)

    # Save
    all_results = {
        'timestamp': datetime.now().isoformat(),
        'verdict': verdict, 'checks_passed': n_pass,
        'transformations': r1,
        'drug_categories': r2,
        'sensitivity_sweep': r3,
        'bootstrap': r4,
        'permutation_by_category': {k: v for k, v in r5.items()},
        'leave_one_out': {k: v for k, v in r6.items()},
    }

    def convert(obj):
        if isinstance(obj, (np.floating, np.float64)): return float(obj)
        if isinstance(obj, (np.integer, np.int64)): return int(obj)
        if isinstance(obj, np.ndarray): return obj.tolist()
        return obj

    out = 'robustness_yeast_results.json'
    with open(out, 'w') as f:
        json.dump(all_results, f, indent=2, default=convert)
    print(f"\n  Saved to {out}")


if __name__ == '__main__':
    main()