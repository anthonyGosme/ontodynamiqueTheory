#!/usr/bin/env python3
"""
=============================================================================
R-XVII RIVAL PARTITION TEST — YEAST (Yeast Phenome)
=============================================================================
Analogue du test GDSC/MDSINE2 pour le domaine levure.

Ici on partitionne les GÈNES (pas les perturbations). La question:
"les gènes STRUCTURE sont-ils plus sévèrement affectés sous stress que
les gènes INPUT?" — et cette asymétrie est-elle spécifique à la partition
ontodynamique, ou n'importe quelle partition GO raisonnable la capture?

PARTITIONS:
  (1) ONTODYNAMIQUE   — STRUCTURE_TERMS vs INPUT_TERMS (R-XVII)
  (2) METABOLIC       — metabolic enzymes vs regulatory genes
  (3) ANABOLIC        — biosynthesis/assembly vs degradation/catabolism
  (4) HUB PROXY       — many GO annotations (top 25%) vs few (bottom 25%)
  (5) RANDOM (1000×)  — random binary splits of classified genes

Pour chaque partition:
  - Global ratio + d + p
  - CV par catégorie de drogue (DNA damage, oxidative, osmotic, etc.)
  - Bootstrap CI

Usage:
  python3 06_rival_partitions_yeast.py \
    --matrix yp_matrix_z_haphom_20221025.txt \
    --screens yp_screens_haphom_20221025.txt \
    --gaf gene_association.sgd.20251124.gaf

=============================================================================
"""

import argparse, json, sys, time, warnings
from collections import defaultdict
import numpy as np
import pandas as pd
from scipy import stats
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

warnings.filterwarnings('ignore')

# ============================================================================
# PARTITION DEFINITIONS (GO term sets)
# ============================================================================

# (1) ONTODYNAMIQUE — from RXVII.py, frozen 2026-03-13
ONTO_STRUCTURE = {
    'GO:0006281', 'GO:0043161', 'GO:0006457', 'GO:0030433',
    'GO:0000278', 'GO:0000280', 'GO:0000281', 'GO:0051726', 'GO:0007346',
    'GO:0000082', 'GO:0000086', 'GO:0051301', 'GO:0006260', 'GO:0006261',
    'GO:0009272', 'GO:0071555', 'GO:0007005',
    'GO:0042254', 'GO:0042273', 'GO:0042274',
    'GO:0006325', 'GO:0006265', 'GO:0007059',
}
ONTO_INPUT = {
    'GO:0007165', 'GO:0000165', 'GO:0007264', 'GO:0007186',
    'GO:0031929', 'GO:0032008', 'GO:0038202', 'GO:0006468',
    'GO:0055085', 'GO:0006811', 'GO:0006812', 'GO:0006813', 'GO:0006814',
    'GO:0006826', 'GO:0006865', 'GO:0015078', 'GO:0034220', 'GO:0055072',
    'GO:0006970', 'GO:0009408', 'GO:0034599',
    'GO:0071470', 'GO:0071472', 'GO:0071474',
}

# (2) METABOLIC vs REGULATORY
# Metabolic: amino acid, lipid, carbohydrate, nucleotide metabolism
# Regulatory: transcription regulation, signal transduction, protein modification
METAB_CLASS_A = {
    'GO:0006520',  # cellular amino acid metabolic process
    'GO:0006629',  # lipid metabolic process
    'GO:0005975',  # carbohydrate metabolic process
    'GO:0006139',  # nucleobase-containing compound metabolic process
    'GO:0006082',  # organic acid metabolic process
    'GO:0019752',  # carboxylic acid metabolic process
    'GO:0006091',  # generation of precursor metabolites and energy
    'GO:0055114',  # oxidation-reduction process
    'GO:0008152',  # metabolic process (broad)
    'GO:0044281',  # small molecule metabolic process
    'GO:0006766',  # vitamin metabolic process
    'GO:0009117',  # nucleotide metabolic process
}
METAB_CLASS_B = {
    'GO:0006355',  # regulation of transcription, DNA-templated
    'GO:0045944',  # positive regulation of transcription by RNA pol II
    'GO:0000122',  # negative regulation of transcription by RNA pol II
    'GO:0006357',  # regulation of transcription by RNA pol II
    'GO:0016570',  # histone modification
    'GO:0006468',  # protein phosphorylation
    'GO:0007165',  # signal transduction
    'GO:0051726',  # regulation of cell cycle
    'GO:0006351',  # DNA-templated transcription
    'GO:0010468',  # regulation of gene expression
}

# (3) ANABOLIC vs CATABOLIC
ANAB_CLASS_A = {
    'GO:0009058',  # biosynthetic process
    'GO:0044249',  # cellular biosynthetic process
    'GO:0006412',  # translation
    'GO:0042254',  # ribosome biogenesis
    'GO:0006260',  # DNA replication
    'GO:0006396',  # RNA processing
    'GO:0034660',  # ncRNA metabolic process
    'GO:0006364',  # rRNA processing
    'GO:0008033',  # tRNA processing
    'GO:0000462',  # maturation of SSU-rRNA
    'GO:0006457',  # protein folding
}
ANAB_CLASS_B = {
    'GO:0009056',  # catabolic process
    'GO:0044248',  # cellular catabolic process
    'GO:0006511',  # ubiquitin-dependent protein catabolic process
    'GO:0030163',  # protein catabolic process
    'GO:0006914',  # autophagy
    'GO:0016236',  # macroautophagy
    'GO:0006635',  # fatty acid beta-oxidation
    'GO:0043161',  # proteasome-mediated ubiquitin-dependent protein catabolic
    'GO:0030433',  # ubiquitin-dependent ERAD pathway
    'GO:0006099',  # tricarboxylic acid cycle
    'GO:0006119',  # oxidative phosphorylation
}

# Drug categories for CV (from robustness_yeast.py)
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
    'Cell wall/membrane': [
        'nystatin', 'nocodazole', 'thiabendazole', 'rhizoxin',
        'papuamide', 'norcantharidin', 'wiskostatin',
    ],
    'Signaling inhibitors': [
        'rapamycin', 'FK506', 'wortmannin', 'staurosporine',
        'tyrphostin', 'AG 957', 'RO 106',
    ],
}


# ============================================================================
# DATA LOADING (from RXVII.py / robustness_yeast.py)
# ============================================================================

def load_gaf(path):
    """Load GAF, return gene_go dict, gene_to_orf mapping."""
    gene_go = defaultdict(set)
    gene_to_orf = {}
    with open(path, 'r') as f:
        for line in f:
            if line.startswith('!'):
                continue
            p = line.strip().split('\t')
            if len(p) < 15:
                continue
            gene, qual, go_id, syns = p[2], p[3], p[4], p[10]
            if 'NOT' in qual:
                continue
            gene_go[gene].add(go_id)
            if syns:
                for s in syns.split('|'):
                    s = s.strip()
                    if s.startswith('Y') and len(s) >= 7 and s[1] in 'ABCDEFGHIJKLMNOP':
                        gene_to_orf[gene] = s
                        break
    return gene_go, gene_to_orf


def classify_go(gene_go, gene_to_orf, class_a_terms, class_b_terms, matrix_index):
    """
    Classify genes into class A vs class B based on GO terms.
    Exclude genes annotated to both. Map to ORFs in matrix.
    Returns (a_orfs, b_orfs).
    """
    a_genes = set()
    b_genes = set()
    for gene, gos in gene_go.items():
        is_a = bool(gos & class_a_terms)
        is_b = bool(gos & class_b_terms)
        if is_a and not is_b:
            a_genes.add(gene)
        elif is_b and not is_a:
            b_genes.add(gene)

    # Map to ORFs in matrix
    def to_orfs(genes):
        orfs = []
        for g in genes:
            orf = gene_to_orf.get(g)
            if orf and orf in matrix_index:
                orfs.append(orf)
            elif g in matrix_index:
                orfs.append(g)
        return sorted(set(orfs))

    return to_orfs(a_genes), to_orfs(b_genes)


def classify_hub_proxy(gene_go, gene_to_orf, matrix_index, q_lo=25, q_hi=75):
    """
    Partition by GO annotation breadth (proxy for connectivity/essentiality).
    HUB = top quartile of annotation count
    PERIPHERAL = bottom quartile
    """
    # Count annotations per gene that maps to matrix
    gene_counts = {}
    for gene, gos in gene_go.items():
        orf = gene_to_orf.get(gene)
        if orf and orf in matrix_index:
            gene_counts[orf] = len(gos)
        elif gene in matrix_index:
            gene_counts[gene] = len(gos)

    if not gene_counts:
        return [], []

    counts = np.array(list(gene_counts.values()))
    threshold_lo = np.percentile(counts, q_lo)
    threshold_hi = np.percentile(counts, q_hi)

    hub_orfs = sorted([o for o, c in gene_counts.items() if c >= threshold_hi])
    periph_orfs = sorted([o for o, c in gene_counts.items() if c <= threshold_lo])

    return hub_orfs, periph_orfs


def get_hillenmeyer_screens(screens_path):
    """Get Hillenmeyer homozygous screen IDs."""
    df = pd.read_csv(screens_path, sep='\t')
    hill = df[df['paper'].str.contains('Hillenmeyer', case=False, na=False)]
    return df, set(hill['id'].astype(str))


def categorize_screen(conditionset):
    cond_lower = conditionset.lower() if isinstance(conditionset, str) else ''
    for cat, keywords in DRUG_CATEGORIES.items():
        for kw in keywords:
            if kw.lower() in cond_lower:
                return cat
    return 'Other'


# ============================================================================
# STATISTICAL ENGINE
# ============================================================================

def compute_partition_ratio(matrix, screen_cols, a_orfs, b_orfs):
    """
    Compute severity ratio for a gene partition.
    Severity = mean |z-score| across screens.
    Returns stats dict or None.
    """
    cols = [c for c in screen_cols if c in matrix.columns]
    if not cols:
        return None

    a_in = [o for o in a_orfs if o in matrix.index]
    b_in = [o for o in b_orfs if o in matrix.index]

    if len(a_in) < 10 or len(b_in) < 10:
        return None

    a_sev = matrix.loc[a_in, cols].abs().mean(axis=1).dropna()
    b_sev = matrix.loc[b_in, cols].abs().mean(axis=1).dropna()

    if len(a_sev) < 10 or len(b_sev) < 10:
        return None

    a_mean, b_mean = a_sev.mean(), b_sev.mean()

    if a_mean >= b_mean:
        ratio = a_mean / b_mean if b_mean > 0 else float('inf')
        direction = 'A>B'
    else:
        ratio = b_mean / a_mean if a_mean > 0 else float('inf')
        direction = 'B>A'

    U, p = stats.mannwhitneyu(a_sev, b_sev, alternative='two-sided')
    pooled = np.sqrt((a_sev.std()**2 + b_sev.std()**2) / 2)
    d = (a_mean - b_mean) / pooled if pooled > 0 else 0

    return {
        'n_a': len(a_sev), 'n_b': len(b_sev),
        'mean_a': float(a_mean), 'mean_b': float(b_mean),
        'ratio': float(ratio), 'direction': direction,
        'abs_d': float(abs(d)), 'd': float(d),
        'p_MW': float(p),
        'a_vals': a_sev.values, 'b_vals': b_sev.values,
    }


def compute_cv_by_drug_category(matrix, screens_df, a_orfs, b_orfs):
    """
    Compute ratio per drug category → CV.
    Analogous to CV by cancer type in GDSC.
    """
    hill = screens_df[screens_df['paper'].str.contains('Hillenmeyer', case=False, na=False)].copy()
    hill['category'] = hill['conditionset'].apply(categorize_screen)

    ratios = []
    per_cat = []

    for cat, grp in hill.groupby('category'):
        cat_ids = [str(x) for x in grp['id']]
        cols = [c for c in cat_ids if c in matrix.columns]
        if len(cols) < 3:
            continue

        a_in = [o for o in a_orfs if o in matrix.index]
        b_in = [o for o in b_orfs if o in matrix.index]
        if len(a_in) < 10 or len(b_in) < 10:
            continue

        a_sev = matrix.loc[a_in, cols].abs().mean(axis=1).dropna()
        b_sev = matrix.loc[b_in, cols].abs().mean(axis=1).dropna()

        a_mean, b_mean = a_sev.mean(), b_sev.mean()
        if a_mean > 0 and b_mean > 0:
            ratio = max(a_mean, b_mean) / min(a_mean, b_mean)
            _, p = stats.mannwhitneyu(a_sev, b_sev, alternative='two-sided')
            ratios.append(ratio)
            per_cat.append({
                'category': cat,
                'ratio': float(ratio),
                'p': float(p),
                'n_screens': len(cols),
            })

    if len(ratios) < 2:
        return None

    arr = np.array(ratios)
    return {
        'n_categories': len(ratios),
        'mean_ratio': float(np.mean(arr)),
        'median_ratio': float(np.median(arr)),
        'cv_ratio': float(np.std(arr, ddof=1) / np.mean(arr) * 100),
        'min_ratio': float(np.min(arr)),
        'max_ratio': float(np.max(arr)),
        'per_category': per_cat,
    }


def bootstrap_ratio(a_vals, b_vals, n_boot=10000):
    """Bootstrap CI on the ratio."""
    rng = np.random.RandomState(42)
    boot = []
    for _ in range(n_boot):
        sa = rng.choice(a_vals, len(a_vals), replace=True)
        sb = rng.choice(b_vals, len(b_vals), replace=True)
        ma, mb = np.mean(sa), np.mean(sb)
        if ma > 0 and mb > 0:
            boot.append(max(ma, mb) / min(ma, mb))
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
    parser = argparse.ArgumentParser()
    parser.add_argument('--matrix', required=True)
    parser.add_argument('--screens', required=True)
    parser.add_argument('--gaf', required=True)
    args = parser.parse_args()

    t0 = time.time()

    print("=" * 70)
    print("  R-XVII RIVAL PARTITION TEST — YEAST (Yeast Phenome)")
    print("  Partition des gènes: ontodynamique vs rivales GO")
    print("=" * 70)

    # ── Load data ──
    print("\n[LOAD] GO annotations...")
    gene_go, gene_to_orf = load_gaf(args.gaf)
    print(f"  {len(gene_go)} genes with GO annotations")

    print("\n[LOAD] Screens metadata...")
    screens_df, hill_ids = get_hillenmeyer_screens(args.screens)
    print(f"  Hillenmeyer screens: {len(hill_ids)}")

    print("\n[LOAD] Z-score matrix...")
    matrix = pd.read_csv(args.matrix, sep='\t', index_col=0, low_memory=False)
    matrix.columns = matrix.columns.astype(str)
    print(f"  Matrix: {matrix.shape[0]} genes × {matrix.shape[1]} screens")

    hill_cols = [c for c in matrix.columns if c in hill_ids]
    print(f"  Matched Hillenmeyer columns: {len(hill_cols)}")

    matrix_idx = set(matrix.index)

    # ── Build all partitions ──
    print("\n" + "=" * 70)
    print("  CONSTRUCTION DES PARTITIONS")
    print("=" * 70)

    partitions = {}

    # (1) Ontodynamique
    a, b = classify_go(gene_go, gene_to_orf, ONTO_STRUCTURE, ONTO_INPUT, matrix_idx)
    partitions['Ontodynamique'] = {
        'a_orfs': a, 'b_orfs': b,
        'label_a': 'STRUCTURE', 'label_b': 'INPUT',
        'motivation': 'R-XVII: maintenance machinery vs signaling flux',
    }

    # (2) Metabolic vs Regulatory
    a, b = classify_go(gene_go, gene_to_orf, METAB_CLASS_A, METAB_CLASS_B, matrix_idx)
    partitions['Métabolique'] = {
        'a_orfs': a, 'b_orfs': b,
        'label_a': 'METABOLIC', 'label_b': 'REGULATORY',
        'motivation': 'Enzymes métaboliques vs régulateurs transcriptionnels',
    }

    # (3) Anabolic vs Catabolic
    a, b = classify_go(gene_go, gene_to_orf, ANAB_CLASS_A, ANAB_CLASS_B, matrix_idx)
    partitions['Anabolique'] = {
        'a_orfs': a, 'b_orfs': b,
        'label_a': 'ANABOLIC', 'label_b': 'CATABOLIC',
        'motivation': 'Biosynthèse/assemblage vs dégradation/catabolisme',
    }

    # (4) Hub proxy (annotation breadth)
    hub, periph = classify_hub_proxy(gene_go, gene_to_orf, matrix_idx)
    partitions['Hub (GO breadth)'] = {
        'a_orfs': hub, 'b_orfs': periph,
        'label_a': 'HUB (top 25%)', 'label_b': 'PERIPHERAL (bot 25%)',
        'motivation': 'Centralité réseau (proxy: nombre d\'annotations GO)',
    }

    for pname, part in partitions.items():
        print(f"\n  {pname}:")
        print(f"    {part['label_a']}: {len(part['a_orfs'])} gènes")
        print(f"    {part['label_b']}: {len(part['b_orfs'])} gènes")
        print(f"    Motivation: {part['motivation']}")

    # ── Discordance ──
    print(f"\n{'=' * 70}")
    print(f"  DISCORDANCE ENTRE PARTITIONS")
    print(f"{'=' * 70}")

    onto_a = set(partitions['Ontodynamique']['a_orfs'])
    onto_b = set(partitions['Ontodynamique']['b_orfs'])
    for pname in ['Métabolique', 'Anabolique', 'Hub (GO breadth)']:
        rival_a = set(partitions[pname]['a_orfs'])
        rival_b = set(partitions[pname]['b_orfs'])
        # How many ontodynamique-STRUCTURE genes are in rival class A vs B?
        sa = len(onto_a & rival_a)
        sb = len(onto_a & rival_b)
        ia = len(onto_b & rival_a)
        ib = len(onto_b & rival_b)
        total = sa + sb + ia + ib
        discord = (sb + ia) / total * 100 if total > 0 else 0
        print(f"\n  Onto × {pname}:")
        print(f"    {'':12s} {partitions[pname]['label_a']:>15s} {partitions[pname]['label_b']:>15s}")
        print(f"    {'STRUCTURE':12s} {sa:>15d} {sb:>15d}")
        print(f"    {'INPUT':12s} {ia:>15d} {ib:>15d}")
        print(f"    Discordance: {discord:.1f}%")

    # ── Global results ──
    print(f"\n{'=' * 70}")
    print(f"  RÉSULTATS GLOBAUX (Hillenmeyer screens)")
    print(f"{'=' * 70}")

    global_results = {}
    for pname, part in partitions.items():
        r = compute_partition_ratio(matrix, hill_cols, part['a_orfs'], part['b_orfs'])
        if r:
            global_results[pname] = r
            eff = "négligeable" if r['abs_d'] < 0.2 else (
                "faible" if r['abs_d'] < 0.5 else (
                    "moyen" if r['abs_d'] < 0.8 else "FORT"))
            print(f"\n  {pname}:")
            print(f"    {part['label_a']} (n={r['n_a']}): mean_sev={r['mean_a']:.4f}")
            print(f"    {part['label_b']} (n={r['n_b']}): mean_sev={r['mean_b']:.4f}")
            print(f"    Ratio = {r['ratio']:.3f}× ({r['direction']})")
            print(f"    |d| = {r['abs_d']:.4f} ({eff}), p = {r['p_MW']:.2e}")

            # Bootstrap
            boot = bootstrap_ratio(r['a_vals'], r['b_vals'])
            global_results[pname]['bootstrap'] = boot
            print(f"    Bootstrap: {boot['mean']:.3f}× "
                  f"IC95 [{boot['ci_95'][0]:.3f}, {boot['ci_95'][1]:.3f}]")

    # ── CV by drug category ──
    print(f"\n{'=' * 70}")
    print(f"  CV PAR CATÉGORIE DE DROGUE")
    print(f"  (analogue du CV par cancer type dans GDSC)")
    print(f"{'=' * 70}")

    cv_results = {}
    for pname, part in partitions.items():
        cv = compute_cv_by_drug_category(matrix, screens_df, part['a_orfs'], part['b_orfs'])
        if cv:
            cv_results[pname] = cv
            print(f"\n  {pname}:")
            print(f"    N catégories: {cv['n_categories']}")
            print(f"    Ratio moyen: {cv['mean_ratio']:.3f}×")
            print(f"    ★ CV = {cv['cv_ratio']:.1f}%")
            print(f"    Range: [{cv['min_ratio']:.3f}, {cv['max_ratio']:.3f}]")
            for pc in sorted(cv['per_category'], key=lambda x: x['ratio']):
                sig = '*' if pc['p'] < 0.05 else ' '
                print(f"      {pc['category']:<22s}: {pc['ratio']:.3f}× "
                      f"p={pc['p']:.2e} ({pc['n_screens']} screens) {sig}")

    # ── Random partitions ──
    N_RANDOM = 1000
    print(f"\n{'=' * 70}")
    print(f"  CONTRÔLE: {N_RANDOM} partitions aléatoires")
    print(f"{'=' * 70}")

    # Use same gene pool as ontodynamique
    onto_all = partitions['Ontodynamique']['a_orfs'] + partitions['Ontodynamique']['b_orfs']
    n_a_onto = len(partitions['Ontodynamique']['a_orfs'])

    # Pre-compute severity per gene
    all_in = [o for o in onto_all if o in matrix.index]
    sev_all = matrix.loc[all_in, hill_cols].abs().mean(axis=1).dropna()
    sev_vals = sev_all.values
    sev_idx = list(sev_all.index)

    rng = np.random.RandomState(42)
    random_ratios = []
    random_cvs = []

    for _ in range(N_RANDOM):
        perm = rng.permutation(len(sev_vals))
        a_vals = sev_vals[perm[:n_a_onto]]
        b_vals = sev_vals[perm[n_a_onto:]]

        ma, mb = np.mean(a_vals), np.mean(b_vals)
        if ma > 0 and mb > 0:
            ratio = max(ma, mb) / min(ma, mb)
            random_ratios.append(ratio)

        # CV by drug category for this random partition
        a_orfs_rand = [sev_idx[i] for i in perm[:n_a_onto]]
        b_orfs_rand = [sev_idx[i] for i in perm[n_a_onto:]]
        cat_ratios = []

        hill_df = screens_df[screens_df['paper'].str.contains('Hillenmeyer', case=False, na=False)].copy()
        hill_df['category'] = hill_df['conditionset'].apply(categorize_screen)
        for cat, grp in hill_df.groupby('category'):
            cat_ids = [str(x) for x in grp['id']]
            cols = [c for c in cat_ids if c in matrix.columns]
            if len(cols) < 3:
                continue
            a_in = [o for o in a_orfs_rand if o in matrix.index]
            b_in = [o for o in b_orfs_rand if o in matrix.index]
            if len(a_in) < 10 or len(b_in) < 10:
                continue
            a_s = matrix.loc[a_in, cols].abs().mean(axis=1).dropna().mean()
            b_s = matrix.loc[b_in, cols].abs().mean(axis=1).dropna().mean()
            if a_s > 0 and b_s > 0:
                cat_ratios.append(max(a_s, b_s) / min(a_s, b_s))

        if len(cat_ratios) >= 2:
            arr = np.array(cat_ratios)
            cv = float(np.std(arr, ddof=1) / np.mean(arr) * 100)
            if np.isfinite(cv):
                random_cvs.append(cv)

    random_ratios = np.array(random_ratios)
    random_cvs = np.array(random_cvs)

    print(f"  Ratio global: médiane = {np.median(random_ratios):.3f}×, "
          f"IQR = [{np.percentile(random_ratios, 25):.3f}, {np.percentile(random_ratios, 75):.3f}]")
    print(f"  Max ratio aléatoire: {np.max(random_ratios):.3f}×")

    if 'Ontodynamique' in global_results:
        onto_ratio = global_results['Ontodynamique']['ratio']
        pct = float(np.mean(random_ratios >= onto_ratio) * 100)
        print(f"\n  Ratio ontodynamique ({onto_ratio:.3f}×) au percentile {100-pct:.1f}%")
        print(f"  Partitions aléatoires ≥ {onto_ratio:.2f}×: "
              f"{int(np.sum(random_ratios >= onto_ratio))}/{N_RANDOM}")
        if pct < 0.1:
            print(f"  → p < 0.001: SIGNIFICATIVEMENT spécifique")
        elif pct < 1:
            print(f"  → p < 0.01")
        elif pct < 5:
            print(f"  → p < 0.05")
        else:
            print(f"  → non significatif")

    if len(random_cvs) > 0:
        print(f"\n  CV aléatoire: médiane = {np.median(random_cvs):.1f}%, "
              f"IQR = [{np.percentile(random_cvs, 25):.1f}%, {np.percentile(random_cvs, 75):.1f}%]")

    # ── Summary table ──
    print(f"\n{'=' * 70}")
    print(f"  TABLE RÉCAPITULATIVE")
    print(f"{'=' * 70}")

    print(f"\n  {'Partition':<20s} {'Ratio':>7s} {'|d|':>7s} {'p':>10s} "
          f"{'Boot CI':>18s} {'CV%':>7s}")
    print(f"  {'─'*20} {'─'*7} {'─'*7} {'─'*10} {'─'*18} {'─'*7}")

    for pname in partitions:
        gr = global_results.get(pname)
        cv = cv_results.get(pname)
        if gr:
            boot = gr.get('bootstrap', {})
            ci_str = f"[{boot['ci_95'][0]:.3f}, {boot['ci_95'][1]:.3f}]" if boot else "—"
            cv_str = f"{cv['cv_ratio']:.1f}%" if cv else "—"
            sig = '***' if gr['p_MW'] < 0.001 else ('**' if gr['p_MW'] < 0.01 else (
                '*' if gr['p_MW'] < 0.05 else ' '))
            print(f"  {pname:<20s} {gr['ratio']:>6.3f}× {gr['abs_d']:>7.4f} "
                  f"{gr['p_MW']:>9.2e}{sig} {ci_str:>18s} {cv_str:>7s}")

    if len(random_ratios) > 0:
        print(f"  {'Aléatoire (méd.)':<20s} {np.median(random_ratios):>6.3f}× {'—':>7s} "
              f"{'—':>10s} {'—':>18s} "
              f"{np.median(random_cvs):.1f}%" if len(random_cvs) > 0 else "—")

    # ── Visualization ──
    print(f"\n{'=' * 70}")
    print(f"  FIGURES")
    print(f"{'=' * 70}")

    fig, axes = plt.subplots(2, 2, figsize=(14, 11))
    fig.suptitle('R-XVII Rival Partition Test — Yeast (Yeast Phenome)\n'
                 'Partition des gènes: ontodynamique vs rivales GO',
                 fontsize=13, fontweight='bold')

    colors = {
        'Ontodynamique': '#1565C0',
        'Métabolique': '#6A1B9A',
        'Anabolique': '#E65100',
        'Hub (GO breadth)': '#2E7D32',
    }

    # Panel 1: Ratio comparison
    ax = axes[0, 0]
    names = [p for p in partitions if p in global_results]
    vals = [global_results[p]['ratio'] for p in names]
    cols_bar = [colors.get(p, '#9E9E9E') for p in names]
    bars = ax.bar(range(len(names)), vals, color=cols_bar, alpha=0.8, edgecolor='black')
    if len(random_ratios) > 0:
        ax.axhline(np.median(random_ratios), color='gray', ls='--', lw=1.5,
                   label=f'Aléatoire (méd. {np.median(random_ratios):.3f}×)')
    ax.axhline(1.0, color='gray', ls=':', lw=0.5)
    ax.set_xticks(range(len(names)))
    ax.set_xticklabels(names, fontsize=8, rotation=15)
    ax.set_ylabel('Ratio')
    ax.set_title('Ratio par partition')
    ax.legend(fontsize=8)
    for i, v in enumerate(vals):
        ax.text(i, v + 0.01, f'{v:.3f}×', ha='center', fontsize=9, fontweight='bold')

    # Panel 2: CV comparison
    ax = axes[0, 1]
    cv_names = [p for p in partitions if p in cv_results]
    cv_vals = [cv_results[p]['cv_ratio'] for p in cv_names]
    cv_cols = [colors.get(p, '#9E9E9E') for p in cv_names]
    if len(random_cvs) > 0:
        cv_names.append('Aléatoire\n(méd.)')
        cv_vals.append(float(np.median(random_cvs)))
        cv_cols.append('#9E9E9E')
    bars = ax.bar(range(len(cv_names)), cv_vals, color=cv_cols, alpha=0.8, edgecolor='black')
    ax.set_xticks(range(len(cv_names)))
    ax.set_xticklabels(cv_names, fontsize=8, rotation=15)
    ax.set_ylabel('CV (%)')
    ax.set_title('CV du ratio par catégorie de drogue\n(plus bas = plus stable)')
    for i, v in enumerate(cv_vals):
        ax.text(i, v + 0.3, f'{v:.1f}%', ha='center', fontsize=9, fontweight='bold')

    # Panel 3: Random distribution + observed
    ax = axes[1, 0]
    if len(random_ratios) > 0:
        ax.hist(random_ratios, bins=50, alpha=0.6, color='#9E9E9E', density=True,
                label='Aléatoires')
        for pname in partitions:
            if pname in global_results:
                ax.axvline(global_results[pname]['ratio'], color=colors.get(pname, 'black'),
                           lw=2.5, label=f"{pname}: {global_results[pname]['ratio']:.3f}×")
        ax.set_xlabel('Ratio')
        ax.set_ylabel('Densité')
        ax.set_title(f'Ratio observé vs {N_RANDOM} aléatoires')
        ax.legend(fontsize=7)

    # Panel 4: Bootstrap CIs
    ax = axes[1, 1]
    y_pos = 0
    for pname in partitions:
        if pname not in global_results:
            continue
        boot = global_results[pname].get('bootstrap')
        if not boot:
            continue
        ci = boot['ci_95']
        ax.barh(y_pos, boot['mean'], color=colors.get(pname, '#9E9E9E'),
                alpha=0.7, edgecolor='black', height=0.5)
        ax.errorbar(boot['mean'], y_pos,
                    xerr=[[boot['mean'] - ci[0]], [ci[1] - boot['mean']]],
                    color='black', capsize=5, capthick=2, lw=1.5)
        ax.text(ci[1] + 0.02, y_pos,
                f"{boot['mean']:.3f}× [{ci[0]:.3f}, {ci[1]:.3f}]",
                va='center', fontsize=8)
        y_pos += 1
    ax.axvline(1.0, color='gray', ls=':', lw=1)
    ax.set_yticks(range(y_pos))
    ax.set_yticklabels([p for p in partitions if p in global_results], fontsize=9)
    ax.set_xlabel('Ratio (bootstrap IC95)')
    ax.set_title('Bootstrap CI par partition')

    plt.tight_layout()
    fig_path = 'rXVII_rival_partitions_yeast.png'
    plt.savefig(fig_path, dpi=200, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"  → {fig_path}")

    # ── Export JSON ──
    export = {
        'protocol': 'R-XVII rival partition test — Yeast Phenome',
        'n_random': N_RANDOM,
        'global': {},
        'cv': {},
        'random_summary': {},
    }
    for pname in partitions:
        if pname in global_results:
            r = global_results[pname]
            export['global'][pname] = {k: v for k, v in r.items()
                                        if k not in ('a_vals', 'b_vals')}
        if pname in cv_results:
            export['cv'][pname] = cv_results[pname]

    if len(random_ratios) > 0:
        export['random_summary'] = {
            'ratio_median': float(np.median(random_ratios)),
            'ratio_max': float(np.max(random_ratios)),
            'ratio_iqr': [float(np.percentile(random_ratios, 25)),
                          float(np.percentile(random_ratios, 75))],
        }
        if 'Ontodynamique' in global_results:
            export['random_summary']['onto_percentile'] = float(
                100 - np.mean(random_ratios >= global_results['Ontodynamique']['ratio']) * 100)

    def nc(o):
        if isinstance(o, (np.integer,)): return int(o)
        if isinstance(o, (np.floating,)): return float(o)
        if isinstance(o, np.ndarray): return o.tolist()
        if isinstance(o, np.bool_): return bool(o)
        raise TypeError(f"{type(o)}")

    json_path = 'rXVII_rival_partitions_yeast.json'
    with open(json_path, 'w') as f:
        json.dump(export, f, indent=2, default=nc)
    print(f"  → {json_path}")

    # ── Verdict ──
    print(f"\n{'=' * 70}")
    print(f"  VERDICT")
    print(f"{'=' * 70}")

    if 'Ontodynamique' in global_results:
        onto = global_results['Ontodynamique']
        rivals = {p: global_results[p] for p in global_results if p != 'Ontodynamique'}

        print(f"\n  Ontodynamique: ratio={onto['ratio']:.3f}×, "
              f"|d|={onto['abs_d']:.4f}, p={onto['p_MW']:.2e}")
        for p, r in rivals.items():
            print(f"  {p}: ratio={r['ratio']:.3f}×, "
                  f"|d|={r['abs_d']:.4f}, p={r['p_MW']:.2e}")

        onto_best_ratio = all(onto['ratio'] > r['ratio'] for r in rivals.values())
        onto_pct = float(np.mean(random_ratios >= onto['ratio']) * 100) if len(random_ratios) > 0 else 50

        if onto_best_ratio and onto_pct < 0.1:
            print(f"\n  ★ RÉSULTAT FORT: la partition ontodynamique a le ratio")
            print(f"    le plus élevé parmi toutes les rivales nommées,")
            print(f"    et surpasse {100-onto_pct:.1f}% des partitions aléatoires.")
        elif onto_pct < 1:
            print(f"\n  ★ RÉSULTAT MODÉRÉ: ontodynamique au percentile {100-onto_pct:.1f}%")
            print(f"    des aléatoires, mais pas la meilleure rivale nommée.")
        else:
            print(f"\n  ★ RÉSULTAT: ontodynamique au percentile {100-onto_pct:.1f}%")

    elapsed = time.time() - t0
    print(f"\n  Temps: {elapsed:.1f}s")


if __name__ == '__main__':
    main()