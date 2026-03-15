#!/usr/bin/env python3
"""

 python3 RXVII.py --matrix yp_matrix_z_haphom_20221025.txt \
  --screens yp_screens_haphom_20221025.txt \
  --gaf gene_association.sgd.20251124.gaf



═══════════════════════════════════════════════════════════════
  R-XVII YEAST — Yeast Phenome Analysis (LOCAL)
  Run on your Mac with the full matrix files.

  Usage:
    python3 rxvii_yeastphenome_local.py \
      --matrix yp_matrix_z_haphom_20221025.txt \
      --screens yp_screens_haphom_20221025.txt \
      --gaf gene_association_sgd_20251124_gaf

  Output: prints results + saves rxvii_yeastphenome_results.json
═══════════════════════════════════════════════════════════════
"""
import argparse, json, sys, collections
import numpy as np
import pandas as pd
from scipy import stats

# ── PARTITION (frozen, from GAF analysis 2026-03-13) ──
STRUCTURE_TERMS = {
    'GO:0006281', 'GO:0043161', 'GO:0006457', 'GO:0030433',
    'GO:0000278', 'GO:0000280', 'GO:0000281', 'GO:0051726', 'GO:0007346',
    'GO:0000082', 'GO:0000086', 'GO:0051301', 'GO:0006260', 'GO:0006261',
    'GO:0009272', 'GO:0071555', 'GO:0007005',
    'GO:0042254', 'GO:0042273', 'GO:0042274',
    'GO:0006325', 'GO:0006265', 'GO:0007059',
}
INPUT_TERMS = {
    'GO:0007165', 'GO:0000165', 'GO:0007264', 'GO:0007186',
    'GO:0031929', 'GO:0032008', 'GO:0038202', 'GO:0006468',
    'GO:0055085', 'GO:0006811', 'GO:0006812', 'GO:0006813', 'GO:0006814',
    'GO:0006826', 'GO:0006865', 'GO:0015078', 'GO:0034220', 'GO:0055072',
    'GO:0006970', 'GO:0009408', 'GO:0034599',
    'GO:0071470', 'GO:0071472', 'GO:0071474',
}


def load_gaf(path):
    """Load SGD GAF, return ORF -> class mapping."""
    gene_go = collections.defaultdict(set)
    gene_to_orf = {}
    with open(path, 'r') as f:
        for line in f:
            if line.startswith('!'): continue
            p = line.strip().split('\t')
            if len(p) < 15: continue
            gene, qual, go_id, syns = p[2], p[3], p[4], p[10]
            if 'NOT' in qual: continue
            gene_go[gene].add(go_id)
            if syns:
                for s in syns.split('|'):
                    s = s.strip()
                    if s.startswith('Y') and len(s) >= 7 and s[1] in 'ABCDEFGHIJKLMNOP':
                        gene_to_orf[gene] = s
                        break
    orf_class = {}
    for gene, gos in gene_go.items():
        orf = gene_to_orf.get(gene)
        if not orf: continue
        is_s = bool(gos & STRUCTURE_TERMS)
        is_i = bool(gos & INPUT_TERMS)
        if is_s and not is_i:
            orf_class[orf] = 'STRUCTURE'
        elif is_i and not is_s:
            orf_class[orf] = 'INPUT'
    print(f"  Partition: {sum(v == 'STRUCTURE' for v in orf_class.values())} S, "
          f"{sum(v == 'INPUT' for v in orf_class.values())} I")
    return orf_class


def select_chemical_screens(screens_path):
    """Identify chemical stress screens from metadata."""
    df = pd.read_csv(screens_path, sep='\t')
    growth = df[df['phenotype'].str.contains('growth', case=False, na=False)]
    std_kw = ['standard', 'control', 'untreated', 'DMSO']
    chem = growth[~growth['conditionset'].str.lower().str.contains('|'.join(std_kw), na=True)]
    has_conc = chem[chem['conditionset'].str.contains(r'\[.*[uUnNmMg%]', na=False)]

    # Also get Hillenmeyer subset
    hillen = df[df['paper'].str.contains('Hillenmeyer', na=False)]
    hillen_hom = hillen[hillen['collection'].str.contains('hom', na=False)]

    return {
        'all_chemical': set(has_conc['id'].astype(str)),
        'hillenmeyer': set(hillen_hom['id'].astype(str)),
    }


def compute_ratio(s_vals, i_vals, label=""):
    """Compute S/I ratio with full stats."""
    s_def = s_vals
    i_def = i_vals

    # Mean-based ratio
    s_mean, i_mean = np.mean(s_def), np.mean(i_def)
    ratio_mean = s_mean / i_mean if i_mean > 0 else np.nan

    # Mann-Whitney
    stat, p = stats.mannwhitneyu(s_def, i_def, alternative='greater')

    # Cohen's d
    pooled = np.sqrt((np.std(s_def) ** 2 + np.std(i_def) ** 2) / 2)
    d = (s_mean - i_mean) / pooled if pooled > 0 else 0

    # Bootstrap CI
    rng = np.random.RandomState(42)
    boot = []
    for _ in range(10000):
        sb = rng.choice(s_def, len(s_def), replace=True)
        ib = rng.choice(i_def, len(i_def), replace=True)
        if np.mean(ib) > 0:
            boot.append(np.mean(sb) / np.mean(ib))
    ci = np.percentile(boot, [2.5, 97.5]) if boot else [np.nan, np.nan]

    print(f"\n  [{label}]")
    print(f"    N: S={len(s_def)}, I={len(i_def)}")
    print(f"    Mean severity: S={s_mean:.4f}, I={i_mean:.4f}")
    print(f"    Ratio (mean): {ratio_mean:.3f}× CI [{ci[0]:.3f}, {ci[1]:.3f}]")
    print(f"    p={p:.2e}, d={d:.3f}")
    return {'ratio': float(ratio_mean), 'ci': [float(ci[0]), float(ci[1])],
            'p': float(p), 'd': float(d), 'n_s': len(s_def), 'n_i': len(i_def)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--matrix', required=True, help='yp_matrix_z_haphom_20221025.txt')
    parser.add_argument('--screens', required=True, help='yp_screens_haphom_20221025.txt')
    parser.add_argument('--gaf', required=True, help='gene_association_sgd_20251124_gaf')
    parser.add_argument('--raw-matrix', default=None, help='yp_matrix_haphom_20221025.txt (optional)')
    args = parser.parse_args()

    print("═" * 60)
    print("  R-XVII YEAST — Yeast Phenome (under perturbation)")
    print("═" * 60)

    # 1. Load partition
    print("\n[1] Loading GO partition...")
    orf_class = load_gaf(args.gaf)

    # 2. Identify chemical screens
    print("\n[2] Identifying chemical stress screens...")
    screen_sets = select_chemical_screens(args.screens)
    print(f"  All chemical: {len(screen_sets['all_chemical'])} screens")
    print(f"  Hillenmeyer:  {len(screen_sets['hillenmeyer'])} screens")

    # 3. Load matrix (this is the big step — ~600MB)
    print("\n[3] Loading z-score matrix (this may take a few minutes)...")
    mat = pd.read_csv(args.matrix, sep='\t', index_col=0, low_memory=False)
    print(f"  Matrix: {mat.shape[0]} genes × {mat.shape[1]} screens")

    # 4. Match genes to partition
    s_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'STRUCTURE']
    i_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'INPUT']
    print(f"\n[4] Matched to matrix: S={len(s_orfs)}, I={len(i_orfs)}")

    results = {}

    # 5. Analysis on Hillenmeyer screens (under chemical stress)
    print("\n" + "=" * 60)
    print("[5] HILLENMEYER SCREENS (chemical stress)")
    print("=" * 60)
    hillen_cols = [c for c in mat.columns if str(c) in screen_sets['hillenmeyer']]
    print(f"  Matched columns: {len(hillen_cols)}")
    if hillen_cols:
        s_severity = mat.loc[s_orfs, hillen_cols].abs().mean(axis=1).dropna()
        i_severity = mat.loc[i_orfs, hillen_cols].abs().mean(axis=1).dropna()
        results['hillenmeyer'] = compute_ratio(s_severity.values, i_severity.values, "Hillenmeyer")

    # 6. Analysis on ALL chemical screens
    print("\n" + "=" * 60)
    print("[6] ALL CHEMICAL STRESS SCREENS")
    print("=" * 60)
    chem_cols = [c for c in mat.columns if str(c) in screen_sets['all_chemical']]
    print(f"  Matched columns: {len(chem_cols)}")
    if chem_cols:
        s_severity = mat.loc[s_orfs, chem_cols].abs().mean(axis=1).dropna()
        i_severity = mat.loc[i_orfs, chem_cols].abs().mean(axis=1).dropna()
        results['all_chemical'] = compute_ratio(s_severity.values, i_severity.values, "All chemical")

    # ── Fallback: use Hillenmeyer if available, otherwise all_chemical ──
    test_cols = hillen_cols if hillen_cols else chem_cols
    test_label = "Hillenmeyer" if hillen_cols else "All chemical"

    # 7. Permutation test
    print("\n" + "=" * 60)
    print(f"[7] PERMUTATION TEST (100K, on {test_label})")
    print("=" * 60)
    if test_cols:
        all_orfs_list = s_orfs + i_orfs
        all_sev = mat.loc[all_orfs_list, test_cols].abs().mean(axis=1).dropna()
        vals = all_sev.values
        n_s = len(s_orfs)
        obs = np.mean(vals[:n_s]) / np.mean(vals[n_s:]) if np.mean(vals[n_s:]) > 0 else np.nan

        rng = np.random.RandomState(42)
        perm = []
        for _ in range(100000):
            idx = rng.permutation(len(vals))
            sp, ip = vals[idx[:n_s]], vals[idx[n_s:]]
            if np.mean(ip) > 0:
                perm.append(np.mean(sp) / np.mean(ip))
        perm = np.array(perm)
        p_perm = np.mean(perm >= obs)
        print(f"  Observed: {obs:.3f}×")
        print(f"  Perm p: {p_perm:.6f}")
        print(f"  Random ≥ 1.3: {np.sum(perm >= 1.3)}/100000")
        results['perm'] = {'obs': float(obs), 'p': float(p_perm)}

    # 8. Split 50/50
    print("\n" + "=" * 60)
    print(f"[8] SPLIT 50/50 (on {test_label})")
    print("=" * 60)
    if test_cols:
        rng5 = np.random.RandomState(2026)
        s_sev = mat.loc[s_orfs, test_cols].abs().mean(axis=1).dropna()
        i_sev = mat.loc[i_orfs, test_cols].abs().mean(axis=1).dropna()

        s_idx = rng5.permutation(len(s_sev))
        i_idx = rng5.permutation(len(i_sev))
        mid_s, mid_i = len(s_sev) // 2, len(i_sev) // 2

        r_exp = compute_ratio(s_sev.values[s_idx[:mid_s]], i_sev.values[i_idx[:mid_i]], "Exploratoire 50%")
        r_con = compute_ratio(s_sev.values[s_idx[mid_s:]], i_sev.values[i_idx[mid_i:]], "Confirmatif 50%")
        results['split_explore'] = r_exp
        results['split_confirm'] = r_con

    # 9. Summary
    print(f"\n{'═' * 60}")
    print(f"  SUMMARY")
    print(f"{'═' * 60}")
    print(f"  Existing domains: microbiome 1.61×, récifs 1.80×, cancer 1.85×")
    for k, v in results.items():
        if 'ratio' in v:
            print(f"  {k}: {v['ratio']:.3f}× [{v['ci'][0]:.3f}, {v['ci'][1]:.3f}] p={v['p']:.2e}")
    print(f"{'═' * 60}")

    # Save
    with open('rxvii_yeastphenome_results.json', 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\n  Saved to rxvii_yeastphenome_results.json")


if __name__ == '__main__':
    main()