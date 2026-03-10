#!/usr/bin/env python3
"""
=============================================================================
SENSITIVITY BATTERY FOR R-XVII RATIO ρ
=============================================================================

4 tests executed in dependency order:  T4 → T2 → T1 → T3

  TEST 4 — Metrological audit: 4 definitions of ρ × 3 domains
  TEST 2 — Null pipeline: permutation nulls + intensity simulation
  TEST 1 — Multi-operationalization: 4 partitions on GDSC
  TEST 3 — Hierarchical Bayesian: cross-domain τ estimation

Requires:
  - sanger-dose-response.csv  (GDSC, from cancerrxgene.org)
  - global_bleaching_environmental.csv  (GCBD, BCO-DMO)
  - MDSINE2 data OR pre-exported microbiome CSV (see --micro-csv)

Usage:
  python sensitivity_battery.py

Auto-detects data files in standard relative paths:
  - sanger-dose-response.csv  (GDSC)   ../ScriptGDSC/ or ./
  - global_bleaching_environmental.csv  (GCBD)  ../ScriptCorail/ or ./
  - MDSINE2_Paper/  (microbiome)        ../ or ./
  - microbiome_bc_distances.csv         ./data/ or ./

If a file is not found, the corresponding test is skipped
(microbiome falls back to summary-stat simulation).

Seeds: all fixed (20240601) for reproducibility.
=============================================================================
"""

import json
import os
import sys
import time
import warnings
from pathlib import Path

import numpy as np
import pandas as pd
from scipy import stats, spatial
from scipy.optimize import curve_fit
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec

warnings.filterwarnings('ignore')
plt.rcParams.update({
    'font.size': 10, 'axes.titlesize': 12, 'axes.labelsize': 11,
    'figure.dpi': 150, 'savefig.dpi': 300, 'savefig.bbox': 'tight',
})

SEED = 20240601
RNG = np.random.RandomState(SEED)

# ═══════════════════════════════════════════════════════════════════════════
# CONFIGURATION — zero arguments, auto-detection
# ═══════════════════════════════════════════════════════════════════════════

_GDSC_CANDIDATES = [
    '../ScriptGDSC/sanger-dose-response.csv',
    'sanger-dose-response.csv',
    '../data/sanger-dose-response.csv',
    'data/sanger-dose-response.csv',
]

_REEF_CANDIDATES = [
    '../ScriptCorail/global_bleaching_environmental.csv',
    'global_bleaching_environmental.csv',
    '../data/global_bleaching_environmental.csv',
    'data/global_bleaching_environmental.csv',
]

_MICRO_CSV_CANDIDATES = [
    # Same directory (extract_microbiome.py run from here)
    'microbiome_bc_distances.csv',
    # Common output dirs
    'output/microbiome_bc_distances.csv',
    '../output/microbiome_bc_distances.csv',
    # Sibling script directories (user's layout)
    '../ScriptMDSINE2/microbiome_bc_distances.csv',
    '../ScriptMDSINE2/output/microbiome_bc_distances.csv',
    '../ScriptMicrobiome/output/microbiome_bc_distances.csv',
    # Data dirs
    '../data/microbiome_bc_distances.csv',
    'data/microbiome_bc_distances.csv',
    '../../output/microbiome_bc_distances.csv',
]

_MDSINE2_CANDIDATES = [
    'MDSINE2_Paper',
    '../MDSINE2_Paper',
    '../../MDSINE2_Paper',
]

N_PERM = 10_000
N_BOOT = 10_000
OUTPUT_DIR = 'output_sensitivity'


def _find_file(candidates, label):
    for c in candidates:
        if c and os.path.exists(c):
            print(f"  [{label}] Found: {c}")
            return c
    return None


class _Args:
    """Drop-in replacement for argparse namespace."""
    n_perm = N_PERM
    n_boot = N_BOOT
    skip = []


# ═══════════════════════════════════════════════════════════════════════════
# DRUG CLASSIFICATION (GDSC)
# ═══════════════════════════════════════════════════════════════════════════

# --- Partition A (baseline): mechanism of action ---
_struct_drugs_A = {
    'Genome integrity': [
        'OLAPARIB', 'TALAZOPARIB', 'RUCAPARIB', 'NIRAPARIB', 'VELIPARIB',
        'MIRIN', 'KU-55933', 'KU-60019', 'KU-57788', 'NU-7441',
        'AZD6738', 'VE-821', 'VE-822', 'AZD7762', 'CHIR-124', 'MK-8776',
        'BLEOMYCIN', 'CISPLATIN', 'CARBOPLATIN', 'OXALIPLATIN',
        'CARMUSTINE', 'LOMUSTINE', 'TEMOZOLOMIDE', 'MITOMYCIN-C',
        'ETOPOSIDE', 'CAMPTOTHECIN', 'SN-38', 'IRINOTECAN', 'TOPOTECAN',
        'DOXORUBICIN', 'DACTINOMYCIN', 'EPIRUBICIN', 'MITOXANTRONE',
    ],
    'DNA replication': [
        'GEMCITABINE', 'CYTARABINE', '5-FLUOROURACIL', 'METHOTREXATE',
        'FLUDARABINE', 'CLOFARABINE', 'HYDROXYUREA', 'PEMETREXED', 'CLADRIBINE',
    ],
    'Cell cycle': [
        'PALBOCICLIB', 'RIBOCICLIB', 'ABEMACICLIB', 'RO-3306',
        'ALVOCIDIB', 'DINACICLIB', 'CGP-60474',
        'NUTLIN-3A (-)', 'NUTLIN-3A', 'APR-246', 'RG7388', 'IDASANUTLIN', '681640',
    ],
    'Mitosis': [
        'PACLITAXEL', 'DOCETAXEL', 'VINBLASTINE', 'VINCRISTINE', 'VINORELBINE',
        'EPOTHILONE-B', 'ALISERTIB', 'ZM-447439', 'BARASERTIB', 'TOZASERTIB',
        'BI-2536', 'VOLASERTIB', 'GSK461364',
        'S-TRITYL-L-CYSTEINE', 'ISPINESIB', 'MPS1-IN-1',
    ],
    'Protein stability and degradation': [
        'BORTEZOMIB', 'CARFILZOMIB', 'MG-132', 'PEVONEDISTAT',
        '17-AAG', 'TANESPIMYCIN', 'AUY922', 'GANETESPIB', 'LUMINESPIB', 'SNX-2112',
    ],
    'Apoptosis regulation': [
        'NAVITOCLAX', 'ABT-737', 'VENETOCLAX', 'ABT-199',
        'AZD5582', 'BIRINAPANT', 'EMBELIN', 'LCL-161', 'YM-155', 'OBATOCLAX',
    ],
    'Chromatin': [
        'VORINOSTAT', 'BELINOSTAT', 'PANOBINOSTAT', 'ENTINOSTAT',
        'AR-42', 'CAY10603', 'ACY-1215', 'TUBASTATIN A', 'TRICHOSTATIN A',
        'JQ1', 'I-BET-762', 'OTX015', 'APABETALONE',
        'EPZ-5676', 'PINOMETOSTAT', 'GSK343', 'EPZ004777', 'EI1',
        'UNC0638', 'CHAETOCIN', 'DECITABINE', 'AZACYTIDINE', 'PFI-3',
    ],
}
_input_drugs_A = {
    'ERK MAPK signaling': [
        'PD-0325901', 'TRAMETINIB', 'SELUMETINIB', 'BINIMETINIB', 'COBIMETINIB',
        'REFAMETINIB', 'CI-1040', 'PIMASERTIB',
        'PLX-4720', 'DABRAFENIB', 'VEMURAFENIB', 'ENCORAFENIB',
        'SORAFENIB', 'AZ-628', 'SB-590885', 'TAK-632',
        'SCH772984', 'BVD-523', 'ULIXERTINIB', 'VX-11E',
    ],
    'PI3K/MTOR signaling': [
        'GDC-0941', 'ALPELISIB', 'BUPARLISIB', 'PICTILISIB',
        'IDELALISIB', 'COPANLISIB', 'APITOLISIB', 'AMG-319', 'TASELISIB',
        'NVP-BEZ235', 'DACTOLISIB',
        'AZD8055', 'VISTUSERTIB', 'SAPANISERTIB', 'OSI-027',
        'SIROLIMUS', 'EVEROLIMUS', 'TEMSIROLIMUS', 'RAPAMYCIN',
        'MK-2206', 'AZD5363', 'IPATASERTIB', 'CAPIVASERTIB', 'UPROSERTIB',
        'AT13148', 'AZD6482', 'BX-795',
    ],
    'EGFR signaling': [
        'ERLOTINIB', 'GEFITINIB', 'LAPATINIB', 'NERATINIB',
        'AFATINIB', 'OSIMERTINIB', 'AZD3759',
        'AZD8931', 'CANERTINIB', 'SAPITINIB', 'AST-1306', 'CETUXIMAB',
    ],
    'RTK signaling': [
        'SUNITINIB', 'AXITINIB', 'PAZOPANIB', 'LENVATINIB',
        'CABOZANTINIB', 'REGORAFENIB', 'TIVOZANIB',
        'IMATINIB', 'NILOTINIB', 'DASATINIB', 'PONATINIB', 'BOSUTINIB',
        'CRIZOTINIB', 'ALECTINIB', 'CERITINIB',
        'NVP-TAE684', 'PHA-665752',
        'BRIVANIB', 'PD-173074', 'AZD4547', 'BGJ398',
        'BMS-536924', 'BMS-754807', 'LINSITINIB',
        'AMUVATINIB', 'GNF-2', 'SARACATINIB', 'MASITINIB', 'DOVITINIB',
        'SB 505124', 'SB-505124', 'AVAGACESTAT',
        'GSK1904529A', 'FORETINIB', 'GSK269962A',
        'GW 441756', 'LESTAURTINIB', 'MIDOSTAURIN', 'SAVOLITINIB',
    ],
    'Hormone-related': [
        'TAMOXIFEN', 'BICALUTAMIDE', 'FULVESTRANT', 'DEXAMETHASONE', 'BEXAROTENE',
    ],
    'WNT signaling': [
        'XAV-939', 'IWP-2', 'LGK-974', 'WNTC59',
        'CYCLOPAMINE', 'VISMODEGIB', 'SONIDEGIB', 'SB-216763', 'CHIR-99021',
    ],
    'JNK and p38 signaling': [
        'DORAMAPIMOD', 'AS601245', '(5Z)-7-OXOZEAENOL', 'JNK INHIBITOR VIII',
    ],
    'Metabolism': [
        'AICAR', 'METFORMIN', 'AGI-5198', 'AGI-6780',
        'APO866', 'APO866, FK866', 'CAY10566', 'C-75', 'AR-12', 'PHENFORMIN',
        'PF-4708671',
    ],
    'Immune response': [
        'LENALIDOMIDE', 'THALIDOMIDE', 'POMALIDOMIDE',
        'RUXOLITINIB', 'TOFACITINIB', 'IBRUTINIB', 'BMS-345541',
    ],
}

STRUCT_PW_A = set(_struct_drugs_A.keys())
INPUT_PW_A = set(_input_drugs_A.keys())

# Build flat drug→pathway dict for partition A
DRUG_PW_A = {}
for pw, drugs in _struct_drugs_A.items():
    for d in drugs:
        DRUG_PW_A[d] = pw
for pw, drugs in _input_drugs_A.items():
    for d in drugs:
        DRUG_PW_A[d] = pw


def map_drug_A(name):
    """Map drug name to pathway (Partition A). Returns None if unmapped."""
    if pd.isna(name):
        return None
    n = str(name).strip().upper()
    if n in DRUG_PW_A:
        return DRUG_PW_A[n]
    # fuzzy fallback
    for key in DRUG_PW_A:
        if key in n or n in key:
            return DRUG_PW_A[key]
    return None


def ptype_A(pw):
    """Return 'STRUCTURE', 'INPUT', or None for Partition A."""
    if pw in STRUCT_PW_A:
        return 'STRUCTURE'
    if pw in INPUT_PW_A:
        return 'INPUT'
    return None


# ═══════════════════════════════════════════════════════════════════════════
# PARTITION B (resserrée): apoptosis + chromatin → INPUT
# ═══════════════════════════════════════════════════════════════════════════

# Moved from STRUCTURE to INPUT
_B_moved_to_input = {'Apoptosis regulation', 'Chromatin'}

def ptype_B(pw):
    if pw is None:
        return None
    if pw in _B_moved_to_input:
        return 'INPUT'
    if pw in STRUCT_PW_A:
        return 'STRUCTURE'
    if pw in INPUT_PW_A:
        return 'INPUT'
    return None


# ═══════════════════════════════════════════════════════════════════════════
# PARTITION C (élargie): add cytoskeleton/membrane targets to STRUCTURE,
#   surface receptor / TF modulators to INPUT
# ═══════════════════════════════════════════════════════════════════════════

# Extra drugs assigned to STRUCTURE (cytoskeletal/membrane/genome stability
# agents not already captured by Partition A)
_C_extra_struct = {
    # Cytoskeleton disruptors already in Mitosis; add borderline cases
    'LATRUNCULIN A', 'LATRUNCULIN B', 'CYTOCHALASIN D', 'JASPLAKINOLIDE',
    'COLCHICINE', 'NOCODAZOLE',
}
# Extra drugs assigned to INPUT (surface receptors / TFs not in A)
_C_extra_input = {
    'THAPSIGARGIN', 'TUNICAMYCIN',  # ER stress → signal modulation
    'NUTLIN-3A (-)', 'NUTLIN-3A',    # moved from cell cycle to INPUT (TF modulator)
}

def ptype_C(pw, drug_name):
    """Partition C: enlarged. pw from Partition A mapping."""
    n = str(drug_name).strip().upper() if drug_name else ''
    if n in _C_extra_struct:
        return 'STRUCTURE'
    if n in _C_extra_input:
        return 'INPUT'
    # Nutlin stays STRUCTURE in C unless explicitly moved
    if pw in STRUCT_PW_A:
        return 'STRUCTURE'
    if pw in INPUT_PW_A:
        return 'INPUT'
    return None


# ═══════════════════════════════════════════════════════════════════════════
# PARTITION D (ATC-based): ATC Level 2 mapping
# ═══════════════════════════════════════════════════════════════════════════
# L01B antimetabolites → STRUCTURE (DNA/RNA synthesis disruption)
# L01C plant alkaloids  → STRUCTURE (mitotic spindle)
# L01D cytotoxic antibiotics → STRUCTURE (DNA intercalation)
# L01E protein kinase inhibitors → INPUT (signal modulation)
# L01X other → depends on mechanism; kinase-target → INPUT

_ATC_struct = {
    # L01B — antimetabolites
    'GEMCITABINE', 'CYTARABINE', '5-FLUOROURACIL', 'METHOTREXATE',
    'FLUDARABINE', 'CLOFARABINE', 'HYDROXYUREA', 'PEMETREXED', 'CLADRIBINE',
    'DECITABINE', 'AZACYTIDINE',
    # L01C — plant alkaloids / taxanes
    'PACLITAXEL', 'DOCETAXEL', 'VINBLASTINE', 'VINCRISTINE', 'VINORELBINE',
    'EPOTHILONE-B',
    # L01D — cytotoxic antibiotics
    'DOXORUBICIN', 'DACTINOMYCIN', 'EPIRUBICIN', 'MITOXANTRONE',
    'BLEOMYCIN', 'MITOMYCIN-C',
    # L01A — alkylating agents (added for completeness)
    'CISPLATIN', 'CARBOPLATIN', 'OXALIPLATIN',
    'CARMUSTINE', 'LOMUSTINE', 'TEMOZOLOMIDE',
    # L01CB — topoisomerase inhibitors
    'ETOPOSIDE', 'CAMPTOTHECIN', 'SN-38', 'IRINOTECAN', 'TOPOTECAN',
}

_ATC_input = {
    # L01E — protein kinase inhibitors (tyrosine/serine-threonine kinases)
    'PD-0325901', 'TRAMETINIB', 'SELUMETINIB', 'BINIMETINIB', 'COBIMETINIB',
    'REFAMETINIB', 'CI-1040', 'PIMASERTIB',
    'PLX-4720', 'DABRAFENIB', 'VEMURAFENIB', 'ENCORAFENIB',
    'SORAFENIB', 'AZ-628', 'SB-590885', 'TAK-632',
    'SCH772984', 'BVD-523', 'ULIXERTINIB', 'VX-11E',
    'GDC-0941', 'ALPELISIB', 'BUPARLISIB', 'PICTILISIB',
    'IDELALISIB', 'COPANLISIB', 'APITOLISIB', 'AMG-319', 'TASELISIB',
    'NVP-BEZ235', 'DACTOLISIB',
    'AZD8055', 'VISTUSERTIB', 'SAPANISERTIB', 'OSI-027',
    'SIROLIMUS', 'EVEROLIMUS', 'TEMSIROLIMUS', 'RAPAMYCIN',
    'MK-2206', 'AZD5363', 'IPATASERTIB', 'CAPIVASERTIB', 'UPROSERTIB',
    'AT13148', 'AZD6482', 'BX-795',
    'ERLOTINIB', 'GEFITINIB', 'LAPATINIB', 'NERATINIB',
    'AFATINIB', 'OSIMERTINIB', 'AZD3759',
    'AZD8931', 'CANERTINIB', 'SAPITINIB', 'AST-1306',
    'SUNITINIB', 'AXITINIB', 'PAZOPANIB', 'LENVATINIB',
    'CABOZANTINIB', 'REGORAFENIB', 'TIVOZANIB',
    'IMATINIB', 'NILOTINIB', 'DASATINIB', 'PONATINIB', 'BOSUTINIB',
    'CRIZOTINIB', 'ALECTINIB', 'CERITINIB',
    'NVP-TAE684', 'PHA-665752',
    'BRIVANIB', 'PD-173074', 'AZD4547', 'BGJ398',
    'BMS-536924', 'BMS-754807', 'LINSITINIB',
    'RUXOLITINIB', 'TOFACITINIB', 'IBRUTINIB',
    'PALBOCICLIB', 'RIBOCICLIB', 'ABEMACICLIB',  # CDK = kinases → INPUT in ATC
}

def ptype_D(drug_name):
    """Partition D: ATC-based. Returns STRUCTURE/INPUT/None."""
    if pd.isna(drug_name):
        return None
    n = str(drug_name).strip().upper()
    if n in _ATC_struct:
        return 'STRUCTURE'
    if n in _ATC_input:
        return 'INPUT'
    return None


# ═══════════════════════════════════════════════════════════════════════════
# SHARED STATISTICAL ENGINE
# ═══════════════════════════════════════════════════════════════════════════

def compute_rho_full(y_input, y_structure, label='', n_perm=10_000,
                     n_boot=10_000, rng=None):
    """
    Full statistical battery for two groups.

    Returns dict with:
      - ratio (mean), ratio_median, ratio_exp_d, ratio_logit
      - Cohen's d, Mann-Whitney p, permutation p
      - bootstrap 95% CI on ratio
      - n_input, n_structure
    """
    if rng is None:
        rng = RNG

    yi = y_input[np.isfinite(y_input)].copy()
    ys = y_structure[np.isfinite(y_structure)].copy()

    if len(yi) < 10 or len(ys) < 10:
        print(f"  ⚠ {label}: n too small (INPUT={len(yi)}, STRUCT={len(ys)})")
        return None

    res = {'label': label, 'n_input': len(yi), 'n_structure': len(ys)}

    # --- Means & medians ---
    res['mean_input'] = np.mean(yi)
    res['mean_struct'] = np.mean(ys)
    res['median_input'] = np.median(yi)
    res['median_struct'] = np.median(ys)

    # --- ρ_moyennes ---
    if res['mean_input'] != 0:
        res['rho_means'] = res['mean_struct'] / res['mean_input']
    else:
        res['rho_means'] = np.inf

    # --- ρ_médianes ---
    if res['median_input'] != 0:
        res['rho_medians'] = res['median_struct'] / res['median_input']
    else:
        res['rho_medians'] = np.inf

    # --- Cohen's d ---
    n1, n2 = len(yi), len(ys)
    sp = np.sqrt(((n1 - 1) * np.var(yi, ddof=1) + (n2 - 1) * np.var(ys, ddof=1))
                 / (n1 + n2 - 2))
    d = (np.mean(ys) - np.mean(yi)) / sp if sp > 0 else 0.0
    res['d'] = d
    res['abs_d'] = abs(d)

    # --- ρ_exp_d ---
    res['rho_exp_d'] = np.exp(d)

    # --- ρ_logit (odds ratio above global median) ---
    combined = np.concatenate([yi, ys])
    threshold = np.median(combined)
    p_s = np.mean(ys > threshold)
    p_i = np.mean(yi > threshold)
    eps = 1e-8
    odds_s = (p_s + eps) / (1 - p_s + eps)
    odds_i = (p_i + eps) / (1 - p_i + eps)
    res['rho_logit'] = odds_s / odds_i

    # --- Mann-Whitney ---
    U, p_mw = stats.mannwhitneyu(yi, ys, alternative='two-sided')
    res['U'] = U
    res['p_MW'] = p_mw

    # --- Permutation test ---
    obs_diff = np.mean(ys) - np.mean(yi)
    MAX_COMB = 50_000
    if len(combined) > MAX_COMB:
        idx_i = rng.choice(len(yi), MAX_COMB // 2, replace=False)
        idx_s = rng.choice(len(ys), MAX_COMB // 2, replace=False)
        comb_sub = np.concatenate([yi[idx_i], ys[idx_s]])
        n_in_sub = len(idx_i)
    else:
        comb_sub = combined.copy()
        n_in_sub = n1

    perm_diffs = np.empty(n_perm)
    for i in range(n_perm):
        rng.shuffle(comb_sub)
        perm_diffs[i] = np.mean(comb_sub[n_in_sub:]) - np.mean(comb_sub[:n_in_sub])
    res['p_perm'] = float(np.mean(np.abs(perm_diffs) >= np.abs(obs_diff)))

    # --- Bootstrap CI on ρ_means ---
    boot_ratios = np.empty(n_boot)
    for b in range(n_boot):
        bi = rng.choice(yi, len(yi), replace=True)
        bs = rng.choice(ys, len(ys), replace=True)
        mi = np.mean(bi)
        ms = np.mean(bs)
        boot_ratios[b] = ms / mi if abs(mi) > 1e-12 else np.nan
    boot_ratios = boot_ratios[np.isfinite(boot_ratios)]
    res['rho_means_ci_lo'] = np.percentile(boot_ratios, 2.5)
    res['rho_means_ci_hi'] = np.percentile(boot_ratios, 97.5)

    # --- Bootstrap CI on Cohen's d ---
    boot_ds = np.empty(n_boot)
    for b in range(n_boot):
        bi = rng.choice(yi, len(yi), replace=True)
        bs = rng.choice(ys, len(ys), replace=True)
        sp_b = np.sqrt(((len(bi)-1)*np.var(bi, ddof=1) + (len(bs)-1)*np.var(bs, ddof=1))
                       / (len(bi)+len(bs)-2))
        boot_ds[b] = (np.mean(bs) - np.mean(bi)) / sp_b if sp_b > 0 else 0
    res['d_ci_lo'] = np.percentile(boot_ds, 2.5)
    res['d_ci_hi'] = np.percentile(boot_ds, 97.5)

    return res


def print_result(res, indent=2):
    """Pretty-print a result dict."""
    if not res:
        return
    pfx = ' ' * indent
    d = res['abs_d']
    eff = ("negligible" if d < 0.2 else
           "small" if d < 0.5 else
           "medium" if d < 0.8 else "LARGE")
    print(f"{pfx}N: INPUT={res['n_input']:,}  STRUCTURE={res['n_structure']:,}")
    print(f"{pfx}MW p = {res['p_MW']:.2e}   Perm p = {res['p_perm']:.4f}")
    print(f"{pfx}Cohen's d = {res['d']:+.4f} [{res['d_ci_lo']:+.3f}, {res['d_ci_hi']:+.3f}] ({eff})")
    print(f"{pfx}ρ_means   = {res['rho_means']:.4f} [{res['rho_means_ci_lo']:.3f}, {res['rho_means_ci_hi']:.3f}]")
    print(f"{pfx}ρ_medians = {res['rho_medians']:.4f}")
    print(f"{pfx}ρ_exp_d   = {res['rho_exp_d']:.4f}")
    print(f"{pfx}ρ_logit   = {res['rho_logit']:.4f}")


# ═══════════════════════════════════════════════════════════════════════════
# DATA LOADERS
# ═══════════════════════════════════════════════════════════════════════════

def load_gdsc(path):
    """Load GDSC data, map Partition A, return DataFrame."""
    if not os.path.exists(path):
        print(f"ERREUR: {path} introuvable")
        return None
    df = pd.read_csv(path)
    auc_col = 'AUC_PUBLISHED' if 'AUC_PUBLISHED' in df.columns else 'AUC'
    df['_auc'] = pd.to_numeric(df[auc_col], errors='coerce')
    df['PATHWAY_A'] = df['DRUG_NAME'].apply(map_drug_A)
    df['PTYPE_A'] = df['PATHWAY_A'].apply(ptype_A)
    mapped = df['PTYPE_A'].notna().sum()
    print(f"[GDSC] {len(df):,} obs, {df['DRUG_NAME'].nunique()} drugs, "
          f"{mapped:,} mapped ({100*mapped/len(df):.1f}%)")
    return df


def load_reef(path):
    """Load GCBD reef data."""
    if not os.path.exists(path):
        print(f"ERREUR: {path} introuvable")
        return None
    df = pd.read_csv(path)
    rn = {'Percent_Bleaching': 'bleaching', 'SSTA_DHW': 'dhw',
          'Cyclone_Frequency': 'cyclone_freq', 'Date_Year': 'year'}
    df = df.rename(columns=rn)
    for c in ['bleaching', 'dhw', 'cyclone_freq', 'year']:
        if c in df.columns:
            df[c] = pd.to_numeric(df[c], errors='coerce')
    df = df.dropna(subset=['bleaching', 'dhw'])
    print(f"[REEF] {len(df):,} observations")
    return df


def reef_classify(df):
    """Classify reef observations: baseline / input / structure."""
    dhw = df['dhw'].fillna(0)
    cyc = df['cyclone_freq'].fillna(0)
    cyc_med = cyc[cyc > 0].median() if (cyc > 0).any() else 999
    pt = pd.Series('baseline', index=df.index)
    pt[(dhw >= 4) & (dhw < 8) & (cyc <= cyc_med)] = 'input'
    pt[(dhw >= 8) | (cyc > cyc_med * 1.5)] = 'structure'
    df['ptype'] = pt
    return df


def load_microbiome(csv_path=None, mdsine2_dir=None):
    """
    Load microbiome BC distances. Returns (input_bc, structure_bc) arrays.

    Priority:
      1. Pre-exported CSV (columns: pert_type, bc_distance)
      2. MDSINE2_Paper data
      3. Simulation from published summary stats
    """
    # Option 1: pre-exported CSV from 02_phase2_corrected.py
    if csv_path and os.path.exists(csv_path):
        df = pd.read_csv(csv_path)

        # Detect format: Phase 2 export vs simple format
        if 'bc_from_baseline' in df.columns:
            # Phase 2 export: has cohort, time_since_pert, bc_from_baseline
            # Filter: dysbiotic cohort, late recovery only (time_since_pert >= 4)
            if 'cohort' in df.columns:
                df = df[df['cohort'] == 'dysbiotic']
            if 'time_since_pert' in df.columns:
                df = df[df['time_since_pert'] >= 4]
            inp = df.loc[df['pert_type'] == 'input', 'bc_from_baseline'].values
            stc = df.loc[df['pert_type'] == 'hardware', 'bc_from_baseline'].values
        else:
            # Simple format: pert_type, bc_distance
            inp = df.loc[df['pert_type'] == 'input', 'bc_distance'].values
            stc = df.loc[df['pert_type'].isin(['hardware', 'structure']), 'bc_distance'].values

        print(f"[MICRO] Loaded from CSV ({csv_path}):")
        print(f"  input: n={len(inp)}, mean={inp.mean():.3f}")
        print(f"  hardware: n={len(stc)}, mean={stc.mean():.3f}")
        print(f"  ratio: {stc.mean()/inp.mean():.3f}")
        return inp, stc

    # Option 2: MDSINE2
    if mdsine2_dir is None:
        # auto-detect
        for candidate in ['MDSINE2_Paper', '../MDSINE2_Paper', '../../MDSINE2_Paper']:
            if os.path.isdir(candidate):
                mdsine2_dir = candidate
                break

    if mdsine2_dir and os.path.isdir(mdsine2_dir):
        try:
            return _load_mdsine2_direct(mdsine2_dir)
        except Exception as e:
            print(f"  [MICRO] MDSINE2 loading failed: {e}")

    # Option 3: simulation from published stats
    print("  [MICRO] Using simulated data from published summary statistics")
    return _simulate_microbiome()


def _patch_llvmlite_numba():
    """
    Inject llvmlite/numba stubs so mdsine2 can be imported even when
    the native C library is broken (common on macOS).

    Proven approach from 04_robustness_metrics.py — mdsine2 only needs
    the Python module structure for pickle deserialization, not numba JIT.
    """
    import types as _types

    try:
        import llvmlite.binding
        return  # native works, nothing to do
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
            m = _types.ModuleType(mod_name)
            m.__path__ = []
            sys.modules[mod_name] = m

    for mod_name in [
        'numba', 'numba.core', 'numba.core.config', 'numba.core.types',
        'numba.core.typing', 'numba.core.errors', 'numba.core.decorators',
        'numba.np', 'numba.np.ufunc', 'numba.typed', 'numba.typed.typedlist',
        'numba.typed.typeddict', 'numba.experimental',
    ]:
        if mod_name not in sys.modules:
            m = _types.ModuleType(mod_name)
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
    print("  [MICRO] Patched llvmlite/numba stubs")


def _load_mdsine2_direct(mdsine2_dir):
    """Extract BC distances from MDSINE2 data (dysbiotic cohort only)."""
    _patch_llvmlite_numba()
    import mdsine2 as md2

    base = Path(mdsine2_dir) / 'datasets' / 'gibson'
    pkl_path = base / 'uc' / 'preprocessed' / 'gibson_uc_agg_filtered.pkl'
    if not pkl_path.exists():
        raise FileNotFoundError(f"Pickle not found: {pkl_path}")

    study_u = md2.Study.load(str(pkl_path))

    phases = {
        'equilibration': (0, 21.5), 'HFD': (21.5, 28.5),
        'recovery_1': (28.5, 35.5), 'vancomycin': (35.5, 42.5),
        'recovery_2': (42.5, 50.5), 'gentamicin': (50.5, 57.5),
        'recovery_3': (57.5, 65.0),
    }

    def get_phase(t):
        for name, (s, e) in phases.items():
            if s <= t < e:
                return name
        return 'post'

    input_bcs, struct_bcs = [], []

    for subj in study_u:
        M = subj.matrix()
        rel = M['rel']
        times = subj.times

        # Global baseline: late equilibration (t=15..21.5)
        base_idx = [i for i, t in enumerate(times) if 15 <= t < 21.5]
        if len(base_idx) < 3:
            continue
        baseline = np.mean(rel[:, base_idx], axis=1)
        baseline = baseline / (baseline.sum() + 1e-15)

        recovery_map = {
            'recovery_1': 'input',     # HFD
            'recovery_2': 'hardware',  # vancomycin
            'recovery_3': 'hardware',  # gentamicin
        }
        pert_ends = {'recovery_1': 28.5, 'recovery_2': 42.5, 'recovery_3': 57.5}

        for i, t in enumerate(times):
            ph = get_phase(t)
            if ph not in recovery_map:
                continue
            if t - pert_ends[ph] < 4:  # late recovery only
                continue
            profile = rel[:, i]
            profile = profile / (profile.sum() + 1e-15)
            bc = spatial.distance.braycurtis(baseline, profile)
            if recovery_map[ph] == 'input':
                input_bcs.append(bc)
            else:
                struct_bcs.append(bc)

    inp = np.array(input_bcs)
    stc = np.array(struct_bcs)
    print(f"[MICRO] MDSINE2 real data: input={len(inp)} (mean={inp.mean():.3f}), "
          f"structure={len(stc)} (mean={stc.mean():.3f}), "
          f"ratio={stc.mean()/inp.mean():.3f}")
    return inp, stc


def _simulate_microbiome(n_input=15, n_hw=30):
    """
    Simulate BC distances from published Phase 2 summary stats.
    Dysbiotic cohort: input_bc ~ 0.28 ± 0.10, hw_bc ~ 0.52 ± 0.15

    Uses Beta distribution (bounded [0,1], appropriate for Bray-Curtis).
    Same approach as crossDomainCheck.py & SpecifityCheck.py.
    """
    from scipy.stats import beta as beta_dist

    def _beta_params(mu, sigma):
        """Convert mean/std to Beta(a, b) parameters."""
        mu = np.clip(mu, 0.01, 0.99)
        sigma = min(sigma, np.sqrt(mu * (1 - mu)) - 0.001)
        v = sigma ** 2
        a = mu * (mu * (1 - mu) / v - 1)
        b = (1 - mu) * (mu * (1 - mu) / v - 1)
        return max(a, 0.5), max(b, 0.5)

    rng_m = np.random.RandomState(SEED + 99)

    a_inp, b_inp = _beta_params(0.28, 0.10)
    a_hw, b_hw = _beta_params(0.52, 0.15)

    inp = beta_dist.rvs(a_inp, b_inp, size=n_input, random_state=rng_m)
    stc = beta_dist.rvs(a_hw, b_hw, size=n_hw, random_state=rng_m)

    print(f"[MICRO] Simulated from Phase 2 published stats (Beta): "
          f"input={len(inp)} (mean={inp.mean():.3f}), "
          f"structure={len(stc)} (mean={stc.mean():.3f})")
    return inp, stc


# ═══════════════════════════════════════════════════════════════════════════
#  TEST 4 — METROLOGICAL AUDIT
# ═══════════════════════════════════════════════════════════════════════════

def test4_metrological_audit(gdsc, reef, micro_in, micro_st, out_dir, args):
    """
    Compute ρ via 4 definitions × 3 domains.
    Returns results dict used downstream by Test 3.
    """
    print("\n" + "=" * 75)
    print("  TEST 4 — METROLOGICAL AUDIT: 4 definitions of ρ × 3 domains")
    print("=" * 75)

    results = {}

    # --- GDSC ---
    if gdsc is not None:
        dfc = gdsc.dropna(subset=['PTYPE_A', '_auc'])
        # Use MAGNITUDE = 1 - AUC as response variable, so that
        # higher value = stronger effect (consistent with reef/microbiome)
        yi = 1.0 - dfc.loc[dfc['PTYPE_A'] == 'INPUT', '_auc'].values
        ys = 1.0 - dfc.loc[dfc['PTYPE_A'] == 'STRUCTURE', '_auc'].values
        # Clip to avoid negatives from AUC > 1 edge cases
        yi = np.clip(yi, 0.001, None)
        ys = np.clip(ys, 0.001, None)
        res_gdsc = compute_rho_full(yi, ys, label='GDSC', n_perm=args.n_perm,
                                     n_boot=args.n_boot)
        if res_gdsc:
            results['GDSC'] = res_gdsc
            print("\n  GDSC (magnitude = 1−AUC):")
            print_result(res_gdsc, indent=4)

    # --- REEF ---
    if reef is not None:
        reef = reef_classify(reef)
        yi_r = reef.loc[reef['ptype'] == 'input', 'bleaching'].values
        ys_r = reef.loc[reef['ptype'] == 'structure', 'bleaching'].values
        res_reef = compute_rho_full(yi_r, ys_r, label='GCBD', n_perm=args.n_perm,
                                     n_boot=args.n_boot)
        if res_reef:
            results['GCBD'] = res_reef
            print("\n  GCBD (% bleaching):")
            print_result(res_reef, indent=4)

    # --- MICROBIOME ---
    if len(micro_in) > 0 and len(micro_st) > 0:
        res_micro = compute_rho_full(micro_in, micro_st, label='MDSINE2',
                                      n_perm=min(args.n_perm, 5000),
                                      n_boot=args.n_boot)
        if res_micro:
            results['MDSINE2'] = res_micro
            print("\n  MDSINE2 (Bray-Curtis distance):")
            print_result(res_micro, indent=4)

    # --- Summary table ---
    print("\n  ┌─────────────────────────────────────────────────────────────────┐")
    print("  │  DOMAIN     │ ρ_means │ ρ_medians │ ρ_exp_d │ ρ_logit │ CV_intra│")
    print("  ├─────────────┼─────────┼───────────┼─────────┼─────────┼─────────┤")

    table_rows = []
    for domain in ['GDSC', 'GCBD', 'MDSINE2']:
        r = results.get(domain)
        if r is None:
            continue
        rhos = [r['rho_means'], r['rho_medians'], r['rho_exp_d'], r['rho_logit']]
        cv = np.std(rhos) / np.mean(rhos) * 100 if np.mean(rhos) > 0 else np.nan
        print(f"  │  {domain:<11s}│ {r['rho_means']:7.4f} │ {r['rho_medians']:9.4f} │ "
              f"{r['rho_exp_d']:7.4f} │ {r['rho_logit']:7.4f} │ {cv:6.1f}% │")
        table_rows.append({
            'domain': domain, 'rho_means': r['rho_means'],
            'rho_medians': r['rho_medians'], 'rho_exp_d': r['rho_exp_d'],
            'rho_logit': r['rho_logit'], 'CV_intra_pct': cv,
            'd': r['d'], 'p_MW': r['p_MW'],
            'n_input': r['n_input'], 'n_structure': r['n_structure'],
        })

    print("  └─────────────────────────────────────────────────────────────────┘")

    # Inter-domain CV per definition
    if len(table_rows) >= 2:
        print("\n  CV inter-domaines par définition:")
        for col in ['rho_means', 'rho_medians', 'rho_exp_d', 'rho_logit']:
            vals = [row[col] for row in table_rows if np.isfinite(row[col])]
            if len(vals) >= 2:
                cv = np.std(vals) / np.mean(vals) * 100
                print(f"    {col:<14s}: {cv:6.2f}%  (vals: {[f'{v:.3f}' for v in vals]})")

    # Save CSV
    if table_rows:
        pd.DataFrame(table_rows).to_csv(out_dir / 'T4_metrological_audit.csv', index=False)

    # --- Figure ---
    if len(table_rows) >= 2:
        fig, axes = plt.subplots(1, 2, figsize=(14, 5))

        # Panel A: grouped bar chart
        ax = axes[0]
        domains = [r['domain'] for r in table_rows]
        x = np.arange(len(domains))
        defs = ['rho_means', 'rho_medians', 'rho_exp_d', 'rho_logit']
        labels = ['ρ_means', 'ρ_medians', 'ρ_exp(d)', 'ρ_logit']
        colors = ['#2196F3', '#4CAF50', '#FF9800', '#9C27B0']
        w = 0.18
        for i, (d_name, lbl, c) in enumerate(zip(defs, labels, colors)):
            vals = [r[d_name] for r in table_rows]
            ax.bar(x + i * w - 1.5 * w, vals, w, label=lbl, color=c, alpha=0.8)
        ax.set_xticks(x)
        ax.set_xticklabels(domains)
        ax.axhline(1.0, color='gray', ls='-', lw=0.5)
        ax.set_ylabel('ρ')
        ax.set_title('A. Four definitions of ρ per domain')
        ax.legend(fontsize=8)

        # Panel B: CV intra-domain
        ax = axes[1]
        cvs = [r['CV_intra_pct'] for r in table_rows]
        bars = ax.bar(domains, cvs, color=['#1565C0', '#2E7D32', '#E65100'], alpha=0.7)
        ax.set_ylabel('CV intra-domain (%)')
        ax.set_title('B. Robustness: intra-domain CV across definitions')
        for bar, cv in zip(bars, cvs):
            ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.5,
                    f'{cv:.1f}%', ha='center', fontsize=10)

        plt.tight_layout()
        plt.savefig(out_dir / 'T4_metrological_audit.png', dpi=150, bbox_inches='tight')
        plt.close()
        print(f"\n  → {out_dir / 'T4_metrological_audit.png'}")

    return results


# ═══════════════════════════════════════════════════════════════════════════
#  TEST 2 — NULL PIPELINE
# ═══════════════════════════════════════════════════════════════════════════

def test2_null_pipeline(gdsc, reef, out_dir, args):
    """
    Étape A: permute labels on GDSC, compute ρ_null (10k times)
    Étape B: synthetic log-normal with intensity shifts
    Étape C: permute labels on GCBD
    """
    print("\n" + "=" * 75)
    print("  TEST 2 — NULL PIPELINE")
    print("=" * 75)

    rng = np.random.RandomState(SEED + 2)
    results = {}

    # ── Étape A: GDSC null (label permutation) ──
    if gdsc is not None:
        print("\n  --- Étape A: GDSC label permutation ---")
        dfc = gdsc.dropna(subset=['PTYPE_A', '_auc']).copy()
        yi = dfc.loc[dfc['PTYPE_A'] == 'INPUT', '_auc'].values
        ys = dfc.loc[dfc['PTYPE_A'] == 'STRUCTURE', '_auc'].values
        n_in, n_st = len(yi), len(ys)

        # Observed ratio (magnitude)
        mag_in = 1.0 - np.mean(yi)
        mag_st = 1.0 - np.mean(ys)
        rho_obs = mag_st / mag_in if mag_in > 0.001 else np.inf

        combined = np.concatenate([yi, ys])
        rho_nulls_A = np.empty(args.n_perm)
        for i in range(args.n_perm):
            rng.shuffle(combined)
            m_in = 1.0 - np.mean(combined[:n_in])
            m_st = 1.0 - np.mean(combined[n_in:])
            rho_nulls_A[i] = m_st / m_in if m_in > 0.001 else np.nan

        rho_nulls_A = rho_nulls_A[np.isfinite(rho_nulls_A)]
        p_emp = np.mean(rho_nulls_A >= rho_obs)
        print(f"    ρ_obs = {rho_obs:.4f}")
        print(f"    ρ_null: mean={np.mean(rho_nulls_A):.4f} ± {np.std(rho_nulls_A):.4f}")
        print(f"    P(ρ_null ≥ {rho_obs:.2f}) = {p_emp:.6f}")
        results['A_gdsc'] = {
            'rho_obs': rho_obs, 'rho_null_mean': float(np.mean(rho_nulls_A)),
            'rho_null_std': float(np.std(rho_nulls_A)), 'p_empirical': float(p_emp),
            'nulls': rho_nulls_A,
        }

    # ── Étape B: Synthetic intensity simulation ──
    print("\n  --- Étape B: Synthetic intensity shifts ---")
    if gdsc is not None:
        dfc = gdsc.dropna(subset=['_auc'])
        real_mean = dfc['_auc'].mean()
        real_std = dfc['_auc'].std()
    else:
        real_mean, real_std = 0.82, 0.18  # typical GDSC values

    N_synth = 200_000
    shifts = [0.0, 0.1, 0.2, 0.3, 0.5, 0.8, 1.0]
    n_rep = 1000
    shift_results = []

    for shift in shifts:
        rho_vals = np.empty(n_rep)
        for r_i in range(n_rep):
            # Log-normal calibrated on GDSC AUC
            base = rng.normal(real_mean, real_std, N_synth)
            base = np.clip(base, 0.01, 0.99)
            n_a = N_synth // 2
            # Group B (would-be STRUCTURE) shifted by `shift` SDs
            base[n_a:] -= shift * real_std
            base = np.clip(base, 0.01, 0.99)
            m_a = 1.0 - np.mean(base[:n_a])
            m_b = 1.0 - np.mean(base[n_a:])
            rho_vals[r_i] = m_b / m_a if m_a > 0.001 else np.nan

        rho_vals = rho_vals[np.isfinite(rho_vals)]
        mean_rho = np.mean(rho_vals)
        print(f"    shift={shift:.1f} SD → ρ_null = {mean_rho:.4f} ± {np.std(rho_vals):.4f}")
        shift_results.append({
            'shift_sd': shift, 'rho_mean': float(mean_rho),
            'rho_std': float(np.std(rho_vals)),
        })

    results['B_synthetic'] = shift_results

    # ── Étape C: GCBD null (label permutation) ──
    if reef is not None:
        print("\n  --- Étape C: GCBD label permutation ---")
        reef_c = reef_classify(reef.copy())
        yi_r = reef_c.loc[reef_c['ptype'] == 'input', 'bleaching'].values
        ys_r = reef_c.loc[reef_c['ptype'] == 'structure', 'bleaching'].values
        n_in_r, n_st_r = len(yi_r), len(ys_r)

        rho_obs_r = np.mean(ys_r) / np.mean(yi_r) if np.mean(yi_r) > 0.001 else np.inf
        combined_r = np.concatenate([yi_r, ys_r])
        rho_nulls_C = np.empty(args.n_perm)
        for i in range(args.n_perm):
            rng.shuffle(combined_r)
            m_i = np.mean(combined_r[:n_in_r])
            m_s = np.mean(combined_r[n_in_r:])
            rho_nulls_C[i] = m_s / m_i if m_i > 0.001 else np.nan

        rho_nulls_C = rho_nulls_C[np.isfinite(rho_nulls_C)]
        p_emp_r = np.mean(rho_nulls_C >= rho_obs_r)
        print(f"    ρ_obs = {rho_obs_r:.4f}")
        print(f"    ρ_null: mean={np.mean(rho_nulls_C):.4f} ± {np.std(rho_nulls_C):.4f}")
        print(f"    P(ρ_null ≥ {rho_obs_r:.2f}) = {p_emp_r:.6f}")
        results['C_reef'] = {
            'rho_obs': float(rho_obs_r),
            'rho_null_mean': float(np.mean(rho_nulls_C)),
            'rho_null_std': float(np.std(rho_nulls_C)),
            'p_empirical': float(p_emp_r),
            'nulls': rho_nulls_C,
        }

    # ── Figure ──
    n_panels = sum([
        'A_gdsc' in results,
        len(shift_results) > 0,
        'C_reef' in results,
    ])
    if n_panels > 0:
        fig, axes = plt.subplots(1, max(n_panels, 1), figsize=(6 * max(n_panels, 1), 5))
        if n_panels == 1:
            axes = [axes]
        idx = 0

        if 'A_gdsc' in results:
            ax = axes[idx]; idx += 1
            ax.hist(results['A_gdsc']['nulls'], bins=80, alpha=0.7,
                    color='#9E9E9E', density=True, label='Null')
            ax.axvline(results['A_gdsc']['rho_obs'], color='#E53935', lw=2.5,
                       label=f"Observed: {results['A_gdsc']['rho_obs']:.3f}")
            ax.set_xlabel('ρ_null')
            ax.set_ylabel('Density')
            ax.set_title(f"A. GDSC null (p={results['A_gdsc']['p_empirical']:.4f})")
            ax.legend()

        if shift_results:
            ax = axes[idx]; idx += 1
            xs = [r['shift_sd'] for r in shift_results]
            ys_m = [r['rho_mean'] for r in shift_results]
            ys_e = [r['rho_std'] for r in shift_results]
            ax.errorbar(xs, ys_m, yerr=ys_e, marker='o', capsize=3, color='#1565C0')
            if 'A_gdsc' in results:
                ax.axhline(results['A_gdsc']['rho_obs'], color='#E53935', ls='--',
                           label=f"Observed ρ = {results['A_gdsc']['rho_obs']:.2f}")
            ax.axhline(1.8, color='black', ls=':', lw=1, label='Target ≈ 1.8')
            ax.set_xlabel('Intensity shift (SD)')
            ax.set_ylabel('ρ_null')
            ax.set_title('B. Intensity simulation')
            ax.legend(fontsize=8)

        if 'C_reef' in results:
            ax = axes[idx]; idx += 1
            ax.hist(results['C_reef']['nulls'], bins=80, alpha=0.7,
                    color='#9E9E9E', density=True, label='Null')
            ax.axvline(results['C_reef']['rho_obs'], color='#2E7D32', lw=2.5,
                       label=f"Observed: {results['C_reef']['rho_obs']:.3f}")
            ax.set_xlabel('ρ_null')
            ax.set_ylabel('Density')
            ax.set_title(f"C. GCBD null (p={results['C_reef']['p_empirical']:.4f})")
            ax.legend()

        plt.tight_layout()
        plt.savefig(out_dir / 'T2_null_pipeline.png', dpi=150, bbox_inches='tight')
        plt.close()
        print(f"\n  → {out_dir / 'T2_null_pipeline.png'}")

    # Save CSV
    csv_rows = []
    for key in ['A_gdsc', 'C_reef']:
        if key in results:
            row = {k: v for k, v in results[key].items() if k != 'nulls'}
            row['test'] = key
            csv_rows.append(row)
    for r in shift_results:
        r['test'] = 'B_synthetic'
        csv_rows.append(r)
    if csv_rows:
        pd.DataFrame(csv_rows).to_csv(out_dir / 'T2_null_pipeline.csv', index=False)

    return results


# ═══════════════════════════════════════════════════════════════════════════
#  TEST 1 — MULTI-OPERATIONALIZATION (GDSC only)
# ═══════════════════════════════════════════════════════════════════════════

def test1_operationalization(gdsc, out_dir, args):
    """
    4 partitions (A, B, C, D) of the same GDSC drugs.
    For each: ρ, d, MW p, bootstrap CI.
    """
    print("\n" + "=" * 75)
    print("  TEST 1 — MULTI-OPERATIONALIZATION (4 partitions, GDSC)")
    print("=" * 75)

    if gdsc is None:
        print("  ⚠ GDSC data not available — skipping Test 1")
        return None

    dfc = gdsc.dropna(subset=['_auc']).copy()
    auc = dfc['_auc'].values
    drug_names = dfc['DRUG_NAME'].values

    partitions = {}

    # --- Partition A (baseline) ---
    dfc['PTYPE_A'] = dfc['PATHWAY_A'].apply(ptype_A)
    mask_a = dfc['PTYPE_A'].notna()
    yi_a = 1.0 - dfc.loc[mask_a & (dfc['PTYPE_A'] == 'INPUT'), '_auc'].values
    ys_a = 1.0 - dfc.loc[mask_a & (dfc['PTYPE_A'] == 'STRUCTURE'), '_auc'].values
    yi_a = np.clip(yi_a, 0.001, None)
    ys_a = np.clip(ys_a, 0.001, None)
    partitions['A_baseline'] = (yi_a, ys_a)

    # --- Partition B (resserrée) ---
    dfc['PTYPE_B'] = dfc['PATHWAY_A'].apply(ptype_B)
    mask_b = dfc['PTYPE_B'].notna()
    yi_b = 1.0 - dfc.loc[mask_b & (dfc['PTYPE_B'] == 'INPUT'), '_auc'].values
    ys_b = 1.0 - dfc.loc[mask_b & (dfc['PTYPE_B'] == 'STRUCTURE'), '_auc'].values
    yi_b = np.clip(yi_b, 0.001, None)
    ys_b = np.clip(ys_b, 0.001, None)
    partitions['B_tight'] = (yi_b, ys_b)

    # --- Partition C (élargie) ---
    dfc['PTYPE_C'] = dfc.apply(
        lambda row: ptype_C(row.get('PATHWAY_A'), row.get('DRUG_NAME')), axis=1)
    mask_c = dfc['PTYPE_C'].notna()
    yi_c = 1.0 - dfc.loc[mask_c & (dfc['PTYPE_C'] == 'INPUT'), '_auc'].values
    ys_c = 1.0 - dfc.loc[mask_c & (dfc['PTYPE_C'] == 'STRUCTURE'), '_auc'].values
    yi_c = np.clip(yi_c, 0.001, None)
    ys_c = np.clip(ys_c, 0.001, None)
    partitions['C_wide'] = (yi_c, ys_c)

    # --- Partition D (ATC) ---
    dfc['PTYPE_D'] = dfc['DRUG_NAME'].apply(ptype_D)
    mask_d = dfc['PTYPE_D'].notna()
    yi_d = 1.0 - dfc.loc[mask_d & (dfc['PTYPE_D'] == 'INPUT'), '_auc'].values
    ys_d = 1.0 - dfc.loc[mask_d & (dfc['PTYPE_D'] == 'STRUCTURE'), '_auc'].values
    yi_d = np.clip(yi_d, 0.001, None)
    ys_d = np.clip(ys_d, 0.001, None)
    partitions['D_atc'] = (yi_d, ys_d)

    # Run tests
    results = {}
    table_rows = []
    for name, (yi, ys) in partitions.items():
        print(f"\n  --- Partition {name} ---")
        res = compute_rho_full(yi, ys, label=name, n_perm=args.n_perm,
                                n_boot=args.n_boot)
        if res:
            results[name] = res
            print_result(res, indent=4)
            table_rows.append({
                'partition': name,
                'n_input': res['n_input'], 'n_structure': res['n_structure'],
                'rho_means': res['rho_means'],
                'd': res['d'], 'abs_d': res['abs_d'],
                'd_ci_lo': res['d_ci_lo'], 'd_ci_hi': res['d_ci_hi'],
                'p_MW': res['p_MW'], 'p_perm': res['p_perm'],
                'rho_means_ci_lo': res['rho_means_ci_lo'],
                'rho_means_ci_hi': res['rho_means_ci_hi'],
            })

    # Verdict
    if table_rows:
        rhos = [r['rho_means'] for r in table_rows if np.isfinite(r['rho_means'])]
        if len(rhos) >= 2:
            cv = np.std(rhos) / np.mean(rhos) * 100
            print(f"\n  VERDICT: ρ_means (magnitude) across 4 partitions: "
                  f"mean={np.mean(rhos):.3f}, range=[{min(rhos):.3f}, {max(rhos):.3f}], "
                  f"CV={cv:.1f}%")
            if cv < 15:
                print(f"    → CV < 15%: robust to operationalization")
            else:
                print(f"    → CV ≥ 15%: sensitive to operationalization")

    # Save
    if table_rows:
        pd.DataFrame(table_rows).to_csv(out_dir / 'T1_operationalization.csv', index=False)

    # Figure
    if len(table_rows) >= 2:
        fig, axes = plt.subplots(1, 2, figsize=(14, 5))

        # Panel A: ρ_means with CI
        ax = axes[0]
        names = [r['partition'] for r in table_rows]
        rhos = [r['rho_means'] for r in table_rows]
        x = np.arange(len(names))
        ax.bar(x, rhos, color=['#1565C0', '#2E7D32', '#E65100', '#6A1B9A'], alpha=0.7)
        ax.axhline(1.8, color='black', ls=':', lw=1.5, label='Target ≈ 1.8×')
        ax.axhline(1.0, color='gray', ls='-', lw=0.5)
        ax.set_xticks(x)
        ax.set_xticklabels(names, rotation=15)
        ax.set_ylabel('ρ (magnitude = 1−AUC)')
        ax.set_title('A. ρ across 4 operationalizations')
        ax.legend()

        # Panel B: Cohen's d with CI
        ax = axes[1]
        ds = [r['abs_d'] for r in table_rows]
        ci_lo = [r['abs_d'] - abs(r['d_ci_lo']) for r in table_rows]
        ci_hi = [abs(r['d_ci_hi']) - r['abs_d'] for r in table_rows]
        ax.bar(x, ds, color=['#1565C0', '#2E7D32', '#E65100', '#6A1B9A'],
               alpha=0.7, yerr=[ci_lo, ci_hi], capsize=4)
        ax.axhline(0.5, color='gray', ls=':', lw=1, label='|d|=0.5 (medium)')
        ax.set_xticks(x)
        ax.set_xticklabels(names, rotation=15)
        ax.set_ylabel("|Cohen's d|")
        ax.set_title("B. Effect size across operationalizations")
        ax.legend()

        plt.tight_layout()
        plt.savefig(out_dir / 'T1_operationalization.png', dpi=150, bbox_inches='tight')
        plt.close()
        print(f"\n  → {out_dir / 'T1_operationalization.png'}")

    return results


# ═══════════════════════════════════════════════════════════════════════════
#  TEST 3 — HIERARCHICAL BAYESIAN MODEL
# ═══════════════════════════════════════════════════════════════════════════

def test3_hierarchical(t4_results, out_dir, args):
    """
    Hierarchical normal model on ρ_means across domains.
    Grid-based posterior (no PyMC dependency).
    Optionally uses PyMC if available.
    """
    print("\n" + "=" * 75)
    print("  TEST 3 — HIERARCHICAL BAYESIAN: cross-domain convergence")
    print("=" * 75)

    # Extract observed ρ and SE from Test 4
    obs = []
    for domain, r in t4_results.items():
        rho = r['rho_means']
        ci_lo = r['rho_means_ci_lo']
        ci_hi = r['rho_means_ci_hi']
        se = (ci_hi - ci_lo) / (2 * 1.96)
        obs.append({'domain': domain, 'rho': rho, 'se': se})
        print(f"  {domain}: ρ = {rho:.4f}, SE = {se:.4f}")

    if len(obs) < 2:
        print("  ⚠ Need at least 2 domains — skipping Test 3")
        return None

    rho_obs = np.array([o['rho'] for o in obs])
    se_obs = np.array([o['se'] for o in obs])

    # --- Grid-based posterior ---
    # Model: rho_k ~ N(mu, tau^2 + se_k^2)
    # Prior: mu ~ N(1.5, 1.0), tau ~ HalfNormal(0.5)

    n_grid = 500
    mu_grid = np.linspace(0.5, 3.0, n_grid)
    tau_grid = np.linspace(0.001, 1.5, n_grid)
    MU, TAU = np.meshgrid(mu_grid, tau_grid)

    # Log prior
    log_prior_mu = -0.5 * ((MU - 1.5) / 1.0) ** 2
    log_prior_tau = -0.5 * (TAU / 0.5) ** 2  # HalfNormal(0.5)
    log_prior_tau[TAU < 0] = -np.inf
    log_prior = log_prior_mu + log_prior_tau

    # Log likelihood
    log_lik = np.zeros_like(MU)
    for k in range(len(obs)):
        sigma_k = np.sqrt(TAU ** 2 + se_obs[k] ** 2)
        log_lik += -0.5 * ((rho_obs[k] - MU) / sigma_k) ** 2 - np.log(sigma_k)

    log_posterior = log_prior + log_lik
    log_posterior -= log_posterior.max()  # numerical stability
    posterior = np.exp(log_posterior)
    posterior /= posterior.sum()

    # Marginal posteriors
    p_mu = posterior.sum(axis=0)
    p_mu /= p_mu.sum()
    p_tau = posterior.sum(axis=1)
    p_tau /= p_tau.sum()

    # Summary stats
    mu_mean = np.sum(mu_grid * p_mu)
    mu_std = np.sqrt(np.sum(mu_grid ** 2 * p_mu) - mu_mean ** 2)
    mu_cdf = np.cumsum(p_mu)
    mu_lo = mu_grid[np.searchsorted(mu_cdf, 0.025)]
    mu_hi = mu_grid[np.searchsorted(mu_cdf, 0.975)]

    tau_mean = np.sum(tau_grid * p_tau)
    tau_std = np.sqrt(np.sum(tau_grid ** 2 * p_tau) - tau_mean ** 2)
    tau_cdf = np.cumsum(p_tau)
    tau_lo = tau_grid[np.searchsorted(tau_cdf, 0.025)]
    tau_hi = tau_grid[np.searchsorted(tau_cdf, 0.975)]
    p_tau_lt_01 = float(np.sum(p_tau[tau_grid < 0.1]))
    p_tau_lt_03 = float(np.sum(p_tau[tau_grid < 0.3]))

    # Posterior predictive for a new domain
    pp_samples = []
    for _ in range(50_000):
        # Sample mu, tau from grid
        flat_idx = RNG.choice(len(posterior.ravel()), p=posterior.ravel())
        i_tau, i_mu = np.unravel_index(flat_idx, posterior.shape)
        mu_s = mu_grid[i_mu]
        tau_s = tau_grid[i_tau]
        rho_new = RNG.normal(mu_s, tau_s + 0.001)  # +eps to avoid zero
        pp_samples.append(rho_new)
    pp_samples = np.array(pp_samples)
    pp_lo, pp_hi = np.percentile(pp_samples, [2.5, 97.5])

    print(f"\n  μ (mean ρ across domains): {mu_mean:.3f} [{mu_lo:.3f}, {mu_hi:.3f}]")
    print(f"  τ (SD across domains):     {tau_mean:.3f} [{tau_lo:.3f}, {tau_hi:.3f}]")
    print(f"  P(τ < 0.1) = {p_tau_lt_01:.4f}")
    print(f"  P(τ < 0.3) = {p_tau_lt_03:.4f}")
    print(f"  Posterior predictive (new domain): [{pp_lo:.3f}, {pp_hi:.3f}]")

    if tau_mean < 0.1:
        print(f"\n  → τ petit: convergence serrée, compatible avec mécanisme commun")
    elif tau_mean < 0.3:
        print(f"\n  → τ modéré: convergence plausible mais incertaine (n=3)")
    else:
        print(f"\n  → τ grand: convergence numérique probablement accidentelle")

    # Save
    res = {
        'mu_mean': mu_mean, 'mu_std': mu_std,
        'mu_95_lo': float(mu_lo), 'mu_95_hi': float(mu_hi),
        'tau_mean': tau_mean, 'tau_std': tau_std,
        'tau_95_lo': float(tau_lo), 'tau_95_hi': float(tau_hi),
        'P_tau_lt_01': p_tau_lt_01, 'P_tau_lt_03': p_tau_lt_03,
        'pp_95_lo': float(pp_lo), 'pp_95_hi': float(pp_hi),
        'n_domains': len(obs),
    }
    with open(out_dir / 'T3_hierarchical.json', 'w') as f:
        json.dump(res, f, indent=2)

    # Figure
    fig, axes = plt.subplots(1, 3, figsize=(18, 5))

    # Panel A: marginal posterior of μ
    ax = axes[0]
    ax.fill_between(mu_grid, p_mu, alpha=0.4, color='#1565C0')
    ax.axvline(mu_mean, color='#1565C0', lw=2, label=f'μ = {mu_mean:.3f}')
    ax.axvspan(mu_lo, mu_hi, alpha=0.15, color='#1565C0', label='95% HDI')
    for o in obs:
        ax.axvline(o['rho'], color='#E53935', ls=':', lw=1, alpha=0.7)
    ax.set_xlabel('μ (mean ρ)')
    ax.set_ylabel('Density')
    ax.set_title('A. Posterior of μ')
    ax.legend(fontsize=8)

    # Panel B: marginal posterior of τ
    ax = axes[1]
    ax.fill_between(tau_grid, p_tau, alpha=0.4, color='#2E7D32')
    ax.axvline(tau_mean, color='#2E7D32', lw=2, label=f'τ = {tau_mean:.3f}')
    ax.axvspan(tau_lo, tau_hi, alpha=0.15, color='#2E7D32', label='95% HDI')
    ax.axvline(0.1, color='red', ls=':', lw=1, label='τ = 0.1')
    ax.axvline(0.3, color='orange', ls=':', lw=1, label='τ = 0.3')
    ax.set_xlabel('τ (SD across domains)')
    ax.set_ylabel('Density')
    ax.set_title(f'B. Posterior of τ  [P(τ<0.1)={p_tau_lt_01:.3f}]')
    ax.legend(fontsize=8)

    # Panel C: posterior predictive
    ax = axes[2]
    ax.hist(pp_samples, bins=100, alpha=0.5, density=True, color='#9C27B0',
            label='Posterior predictive')
    for o in obs:
        ax.axvline(o['rho'], color='#E53935', ls='-', lw=1.5, alpha=0.8)
    ax.axvspan(pp_lo, pp_hi, alpha=0.15, color='#9C27B0',
               label=f'95% PI [{pp_lo:.2f}, {pp_hi:.2f}]')
    ax.set_xlabel('ρ (new domain)')
    ax.set_ylabel('Density')
    ax.set_title('C. Posterior predictive for 5th domain')
    ax.legend(fontsize=8)

    plt.tight_layout()
    plt.savefig(out_dir / 'T3_hierarchical.png', dpi=150, bbox_inches='tight')
    plt.close()
    print(f"\n  → {out_dir / 'T3_hierarchical.png'}")

    return res


# ═══════════════════════════════════════════════════════════════════════════
#  MAIN ORCHESTRATOR
# ═══════════════════════════════════════════════════════════════════════════

def main():
    t0 = time.time()
    args = _Args()
    out_dir = Path(OUTPUT_DIR)
    out_dir.mkdir(parents=True, exist_ok=True)

    print("=" * 75)
    print("  R-XVII SENSITIVITY BATTERY")
    print(f"  Output: {out_dir}")
    print(f"  Seed: {SEED}   Perms: {args.n_perm}   Bootstrap: {args.n_boot}")
    print("=" * 75)

    # --- Auto-detect data files ---
    print("\n--- LOADING DATA ---")
    gdsc_path = _find_file(_GDSC_CANDIDATES, 'GDSC')
    reef_path = _find_file(_REEF_CANDIDATES, 'REEF')
    micro_csv = _find_file(_MICRO_CSV_CANDIDATES, 'MICRO')
    mdsine2_dir = _find_file(_MDSINE2_CANDIDATES, 'MDSINE2')

    gdsc = load_gdsc(gdsc_path) if gdsc_path else None
    reef = load_reef(reef_path) if reef_path else None
    micro_in, micro_st = load_microbiome(micro_csv, mdsine2_dir)

    # --- Execute tests in dependency order ---

    # T4 first (prerequisite)
    t4_results = {}
    if 't4' not in args.skip:
        t4_results = test4_metrological_audit(gdsc, reef, micro_in, micro_st,
                                               out_dir, args)
    else:
        print("\n  [SKIPPED] Test 4")

    # T2 second
    t2_results = {}
    if 't2' not in args.skip:
        t2_results = test2_null_pipeline(gdsc, reef, out_dir, args)
    else:
        print("\n  [SKIPPED] Test 2")

    # T1 third
    t1_results = {}
    if 't1' not in args.skip:
        t1_results = test1_operationalization(gdsc, out_dir, args)
    else:
        print("\n  [SKIPPED] Test 1")

    # T3 fourth (uses T4 results)
    t3_results = {}
    if 't3' not in args.skip:
        if t4_results:
            t3_results = test3_hierarchical(t4_results, out_dir, args)
        else:
            print("\n  ⚠ Test 3 requires Test 4 results — skipping")
    else:
        print("\n  [SKIPPED] Test 3")

    # --- Final summary ---
    elapsed = time.time() - t0
    print("\n" + "=" * 75)
    print(f"  BATTERY COMPLETE — {elapsed:.1f}s")
    print("=" * 75)

    outputs = list(out_dir.glob('*'))
    for f in sorted(outputs):
        print(f"  → {f}")

    # Global summary JSON
    summary = {
        'seed': SEED,
        'n_perm': args.n_perm,
        'n_boot': args.n_boot,
        'elapsed_seconds': elapsed,
        'tests_run': [t for t in ['t4', 't2', 't1', 't3'] if t not in args.skip],
        'files': [str(f.name) for f in sorted(outputs)],
    }
    if t4_results:
        summary['t4_cv_intra'] = {}
        for domain, r in t4_results.items():
            rhos = [r['rho_means'], r['rho_medians'], r['rho_exp_d'], r['rho_logit']]
            summary['t4_cv_intra'][domain] = float(np.std(rhos)/np.mean(rhos)*100)
    if t1_results:
        rhos = [r['rho_means'] for r in t1_results.values()
                if r and np.isfinite(r.get('rho_means', np.nan))]
        if rhos:
            summary['t1_rho_range'] = [float(min(rhos)), float(max(rhos))]
            summary['t1_cv'] = float(np.std(rhos)/np.mean(rhos)*100)
    if t3_results:
        summary['t3_tau_mean'] = t3_results.get('tau_mean')
        summary['t3_mu_mean'] = t3_results.get('mu_mean')
        summary['t3_pp_interval'] = [t3_results.get('pp_95_lo'),
                                      t3_results.get('pp_95_hi')]

    with open(out_dir / 'summary.json', 'w') as f:
        json.dump(summary, f, indent=2)
    print(f"\n  → {out_dir / 'summary.json'}")


if __name__ == '__main__':
    main()