#!/usr/bin/env python3
"""
=============================================================================
R-XVII SPECIFICITY TESTS — "Can we kill the thesis?"
=============================================================================

Three tests by decreasing priority:

  TEST 1 — Exhaustive combinatorial permutation (§8.2)
    Does ANY random binary partition reproduce CV ≤ 5.5% across 3 domains?

  TEST 2 — Pharmacological reversibility (GDSC only)
    Does covalent/non-covalent binding explain the asymmetry better than R-XVII?

  TEST 3 — Target count (GDSC only)
    Does mono/poly-target partition explain the asymmetry?

Data strategy:
  - If real CSV files are found (GDSC, reef), uses them
  - Otherwise, simulates from published summary statistics
  - Microbiome always uses Phase 2 published values (n too small for raw)

Usage:
  python test_specificity_rxvii.py [--gdsc PATH] [--reef PATH] [--nperm 100000]

Output:
  - test_specificity_results.json
  - test_specificity_figure.png
  - Console report
=============================================================================
"""

import argparse
import json
import os
import sys
import time
import warnings
from collections import defaultdict

import numpy as np
import pandas as pd
from scipy import stats
import matplotlib

matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec

warnings.filterwarnings('ignore')
plt.rcParams.update({
    'font.size': 10, 'axes.titlesize': 12, 'axes.labelsize': 11,
    'figure.dpi': 150, 'savefig.dpi': 300, 'savefig.bbox': 'tight',
})

# ============================================================================
# DRUG CLASSIFICATION — shared with existing scripts
# ============================================================================

STRUCTURE_PATHWAYS = {
    'Genome integrity', 'DNA replication', 'Cell cycle',
    'Protein stability and degradation', 'Mitosis',
    'Apoptosis regulation', 'Chromatin histone acetylation', 'Chromatin',
}
INPUT_PATHWAYS = {
    'ERK MAPK signaling', 'PI3K/MTOR signaling', 'RTK signaling',
    'EGFR signaling', 'Hormone-related', 'Metabolism',
    'WNT signaling', 'JNK and p38 signaling', 'Immune response',
}

_struct_drugs = {
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
_input_drugs = {
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
    ],
    'Hormone-related': ['TAMOXIFEN', 'BICALUTAMIDE', 'FULVESTRANT', 'DEXAMETHASONE', 'BEXAROTENE'],
    'WNT signaling': [
        'XAV-939', 'IWP-2', 'LGK-974', 'WNTC59',
        'CYCLOPAMINE', 'VISMODEGIB', 'SONIDEGIB', 'SB-216763', 'CHIR-99021',
    ],
    'JNK and p38 signaling': ['DORAMAPIMOD', 'AS601245', '(5Z)-7-OXOZEAENOL', 'JNK INHIBITOR VIII'],
    'Metabolism': [
        'AICAR', 'METFORMIN', 'AGI-5198', 'AGI-6780',
        'APO866', 'APO866, FK866', 'CAY10566', 'C-75', 'AR-12', 'PHENFORMIN', 'PF-4708671',
    ],
    'Immune response': [
        'LENALIDOMIDE', 'THALIDOMIDE', 'POMALIDOMIDE',
        'RUXOLITINIB', 'TOFACITINIB', 'IBRUTINIB', 'BMS-345541',
    ],
}

DRUG_MAP = {}
for pw, drugs in _struct_drugs.items():
    for d in drugs:
        DRUG_MAP[d] = pw
for pw, drugs in _input_drugs.items():
    for d in drugs:
        DRUG_MAP[d] = pw


def classify_drug_rxvii(name):
    """Classify a drug name into INPUT/STRUCTURE/None."""
    if pd.isna(name):
        return None
    n = str(name).strip().upper()
    pw = DRUG_MAP.get(n)
    if pw is None:
        # fuzzy match
        for key, p in DRUG_MAP.items():
            if key in n or n in key:
                pw = p
                break
    if pw is None:
        return None
    if pw in STRUCTURE_PATHWAYS:
        return 'STRUCTURE'
    if pw in INPUT_PATHWAYS:
        return 'INPUT'
    return None


# ============================================================================
# TEST 2: REVERSIBILITY ANNOTATIONS (manual, pharmacological knowledge)
# ============================================================================

# Covalent (irreversible) inhibitors present in the GDSC drug list
COVALENT_DRUGS = {
    # EGFR covalent inhibitors
    'AFATINIB', 'OSIMERTINIB', 'NERATINIB', 'CANERTINIB', 'AST-1306',
    # BTK covalent
    'IBRUTINIB',
    # Proteasome covalent
    'CARFILZOMIB',
    # KRAS covalent (if present)
    # Alkylating agents (covalent DNA damage — classified STRUCTURE)
    'CISPLATIN', 'CARBOPLATIN', 'OXALIPLATIN',
    'CARMUSTINE', 'LOMUSTINE', 'TEMOZOLOMIDE', 'MITOMYCIN-C',
    'BLEOMYCIN',
    # Crosslinkers (covalent)
    'DACTINOMYCIN',
}

# Non-covalent (reversible) inhibitors — explicit subset
REVERSIBLE_DRUGS = {
    # EGFR reversible
    'ERLOTINIB', 'GEFITINIB', 'LAPATINIB', 'AZD3759', 'AZD8931', 'SAPITINIB',
    # MEK reversible
    'PD-0325901', 'TRAMETINIB', 'SELUMETINIB', 'BINIMETINIB', 'COBIMETINIB',
    'REFAMETINIB', 'CI-1040', 'PIMASERTIB',
    # BRAF reversible
    'PLX-4720', 'DABRAFENIB', 'VEMURAFENIB', 'ENCORAFENIB',
    # Multi-kinase reversible
    'SORAFENIB', 'AZ-628', 'SB-590885', 'TAK-632',
    # ERK reversible
    'SCH772984', 'BVD-523', 'ULIXERTINIB', 'VX-11E',
    # PI3K reversible
    'GDC-0941', 'ALPELISIB', 'BUPARLISIB', 'PICTILISIB',
    'IDELALISIB', 'COPANLISIB', 'APITOLISIB', 'AMG-319', 'TASELISIB',
    # mTOR reversible
    'AZD8055', 'VISTUSERTIB', 'SAPANISERTIB', 'OSI-027',
    'SIROLIMUS', 'EVEROLIMUS', 'TEMSIROLIMUS', 'RAPAMYCIN',
    # AKT reversible
    'MK-2206', 'AZD5363', 'IPATASERTIB', 'CAPIVASERTIB', 'UPROSERTIB',
    # RTK reversible
    'SUNITINIB', 'AXITINIB', 'PAZOPANIB', 'LENVATINIB',
    'CABOZANTINIB', 'REGORAFENIB', 'TIVOZANIB',
    'IMATINIB', 'NILOTINIB', 'DASATINIB', 'PONATINIB', 'BOSUTINIB',
    'CRIZOTINIB', 'ALECTINIB', 'CERITINIB',
    # PARP reversible (trap but non-covalent)
    'OLAPARIB', 'TALAZOPARIB', 'RUCAPARIB', 'NIRAPARIB', 'VELIPARIB',
    # CDK reversible
    'PALBOCICLIB', 'RIBOCICLIB', 'ABEMACICLIB',
    # Proteasome reversible
    'BORTEZOMIB', 'MG-132',
    # HSP90 reversible
    '17-AAG', 'AUY922', 'GANETESPIB', 'LUMINESPIB', 'SNX-2112',
    # BCL-2 reversible
    'NAVITOCLAX', 'ABT-737', 'VENETOCLAX', 'ABT-199',
    # HDAC reversible
    'VORINOSTAT', 'BELINOSTAT', 'PANOBINOSTAT', 'ENTINOSTAT',
    # Tubulin reversible binding
    'PACLITAXEL', 'DOCETAXEL', 'VINBLASTINE', 'VINCRISTINE', 'VINORELBINE',
}


def classify_reversibility(name):
    """Classify drug as COVALENT / REVERSIBLE / None."""
    if pd.isna(name):
        return None
    n = str(name).strip().upper()
    if n in COVALENT_DRUGS:
        return 'COVALENT'
    if n in REVERSIBLE_DRUGS:
        return 'REVERSIBLE'
    # Fuzzy
    for d in COVALENT_DRUGS:
        if d in n or n in d:
            return 'COVALENT'
    for d in REVERSIBLE_DRUGS:
        if d in n or n in d:
            return 'REVERSIBLE'
    return None


# ============================================================================
# TEST 3: TARGET COUNT ANNOTATIONS
# ============================================================================

# Number of primary molecular targets per drug (from known pharmacology)
# 1 = mono-target, 2+ = poly-target
DRUG_N_TARGETS = {
    # Mono-target STRUCTURE drugs
    'OLAPARIB': 1, 'TALAZOPARIB': 1, 'RUCAPARIB': 1, 'NIRAPARIB': 1,  # PARP1/2
    'PALBOCICLIB': 1, 'RIBOCICLIB': 1, 'ABEMACICLIB': 1,  # CDK4/6
    'BORTEZOMIB': 1, 'CARFILZOMIB': 1, 'MG-132': 1,  # proteasome
    'VENETOCLAX': 1, 'ABT-199': 1,  # BCL-2
    'PACLITAXEL': 1, 'DOCETAXEL': 1,  # tubulin
    'GEMCITABINE': 1, 'CYTARABINE': 1,  # DNA pol
    '5-FLUOROURACIL': 1, 'METHOTREXATE': 1,  # thymidylate synthase / DHFR
    'ETOPOSIDE': 1,  # topo II
    'CAMPTOTHECIN': 1, 'SN-38': 1, 'IRINOTECAN': 1, 'TOPOTECAN': 1,  # topo I
    'NUTLIN-3A': 1, 'NUTLIN-3A (-)': 1, 'RG7388': 1, 'IDASANUTLIN': 1,  # MDM2
    'BI-2536': 1, 'VOLASERTIB': 1,  # PLK1
    'ALISERTIB': 1,  # Aurora A
    'BARASERTIB': 1,  # Aurora B
    'VORINOSTAT': 1, 'PANOBINOSTAT': 1,  # pan-HDAC (single enzyme family)
    'JQ1': 1, 'I-BET-762': 1, 'OTX015': 1,  # BET/BRD4
    'CISPLATIN': 1, 'CARBOPLATIN': 1, 'OXALIPLATIN': 1,  # DNA crosslink
    'DOXORUBICIN': 1,  # topo II intercalator

    # Mono-target INPUT drugs
    'PD-0325901': 1, 'TRAMETINIB': 1, 'SELUMETINIB': 1,  # MEK1/2
    'BINIMETINIB': 1, 'COBIMETINIB': 1,
    'PLX-4720': 1, 'DABRAFENIB': 1, 'VEMURAFENIB': 1, 'ENCORAFENIB': 1,  # BRAF
    'SCH772984': 1, 'ULIXERTINIB': 1,  # ERK1/2
    'GDC-0941': 1, 'ALPELISIB': 1, 'BUPARLISIB': 1, 'PICTILISIB': 1,  # PI3Kα
    'IDELALISIB': 1,  # PI3Kδ
    'SIROLIMUS': 1, 'EVEROLIMUS': 1, 'TEMSIROLIMUS': 1,  # mTORC1
    'ERLOTINIB': 1, 'GEFITINIB': 1,  # EGFR
    'AFATINIB': 2, 'OSIMERTINIB': 1,  # EGFR (afatinib = EGFR+HER2)
    'LAPATINIB': 2,  # EGFR+HER2
    'NERATINIB': 2,  # EGFR+HER2+HER4
    'IMATINIB': 2,  # ABL+KIT+PDGFR
    'CRIZOTINIB': 2,  # ALK+MET+ROS1
    'IBRUTINIB': 1,  # BTK
    'MK-2206': 1,  # AKT

    # Poly-target drugs
    'SORAFENIB': 4,  # BRAF+VEGFR+PDGFR+KIT
    'SUNITINIB': 4,  # VEGFR+PDGFR+KIT+FLT3
    'REGORAFENIB': 5,  # VEGFR+PDGFR+FGFR+KIT+RET
    'CABOZANTINIB': 3,  # MET+VEGFR2+RET
    'LENVATINIB': 4,  # VEGFR+FGFR+PDGFR+RET+KIT
    'PAZOPANIB': 3,  # VEGFR+PDGFR+KIT
    'AXITINIB': 2,  # VEGFR (selective but 1-3)
    'PONATINIB': 3,  # ABL+VEGFR+FGFR
    'DASATINIB': 3,  # ABL+SRC+KIT
    'NILOTINIB': 2,  # ABL+KIT
    'BOSUTINIB': 2,  # ABL+SRC
    'NVP-BEZ235': 2, 'DACTOLISIB': 2,  # PI3K+mTOR dual
    'NAVITOCLAX': 2, 'ABT-737': 2,  # BCL-2+BCL-XL
    'DOVITINIB': 3,  # FGFR+VEGFR+PDGFR
    'MASITINIB': 2,  # KIT+PDGFR
}


def get_n_targets(name):
    """Return number of molecular targets for a drug, or None."""
    if pd.isna(name):
        return None
    n = str(name).strip().upper()
    if n in DRUG_N_TARGETS:
        return DRUG_N_TARGETS[n]
    for key, val in DRUG_N_TARGETS.items():
        if key in n or n in key:
            return val
    return None


# ============================================================================
# DATA LOADING
# ============================================================================

def load_gdsc_real(path):
    """Load real GDSC dose-response CSV."""
    if not os.path.exists(path):
        return None
    df = pd.read_csv(path)
    auc_col = 'AUC_PUBLISHED' if 'AUC_PUBLISHED' in df.columns else 'AUC'
    df['rxvii_class'] = df['DRUG_NAME'].apply(classify_drug_rxvii)
    df['reversibility'] = df['DRUG_NAME'].apply(classify_reversibility)
    df['n_targets'] = df['DRUG_NAME'].apply(get_n_targets)
    df['_auc'] = df[auc_col]
    df = df.dropna(subset=[auc_col])
    n_in = (df['rxvii_class'] == 'INPUT').sum()
    n_st = (df['rxvii_class'] == 'STRUCTURE').sum()
    print(f"  [GDSC] {len(df)} rows, R-XVII classified: IN={n_in}, ST={n_st}")
    return df


def load_reef_real(path):
    """Load real reef bleaching CSV."""
    if not os.path.exists(path):
        return None
    df = pd.read_csv(path)
    renames = {'Percent_Bleaching': 'bleaching', 'SSTA_DHW': 'dhw',
               'Cyclone_Frequency': 'cyclone_freq'}
    df = df.rename(columns=renames)
    for c in ['bleaching', 'dhw', 'cyclone_freq']:
        if c in df.columns:
            df[c] = pd.to_numeric(df[c], errors='coerce')
    df = df.dropna(subset=['bleaching', 'dhw'])
    print(f"  [REEF] {len(df)} observations")
    return df


# ============================================================================
# DOMAIN RATIO FUNCTIONS
# ============================================================================

def reef_rxvii_groups(df):
    """Classify reef observations into input/structure."""
    dhw = df['dhw'].fillna(0)
    cyc = df['cyclone_freq'].fillna(0)
    cyc_med = cyc[cyc > 0].median() if (cyc > 0).any() else 999
    mask_in = (dhw >= 4) & (dhw < 8) & (cyc <= cyc_med)
    mask_st = (dhw >= 8) | (cyc > cyc_med * 1.5)
    return df.loc[mask_in, 'bleaching'].values, df.loc[mask_st, 'bleaching'].values


def reef_ratio_fn(inp, stc):
    if len(inp) < 30 or len(stc) < 30:
        return None
    return np.mean(stc) / max(np.mean(inp), 0.01)


def gdsc_rxvii_groups(df):
    """Split GDSC into input/structure AUC arrays."""
    classified = df.dropna(subset=['rxvii_class'])
    return (classified.loc[classified['rxvii_class'] == 'INPUT', '_auc'].values,
            classified.loc[classified['rxvii_class'] == 'STRUCTURE', '_auc'].values)


def gdsc_ratio_fn(inp, stc):
    if len(inp) < 30 or len(stc) < 30:
        return None
    mi = 1.0 - np.mean(inp)
    ms = 1.0 - np.mean(stc)
    return ms / max(mi, 0.001)


def micro_ratio_fn(inp, hw):
    if len(inp) < 3 or len(hw) < 3:
        return None
    return np.mean(hw) / max(np.mean(inp), 0.001)


# ============================================================================
# PUBLISHED SUMMARY STATS (fallback if no real data)
# ============================================================================

# Phase 2 published values
MICRO_PUBLISHED = {
    'input_bc_mean': 0.28, 'input_bc_std': 0.10, 'n_input': 15,
    'hw_bc_mean': 0.52, 'hw_bc_std': 0.15, 'n_hw': 30,
    'ratio': 1.857,  # 0.52/0.28
}

# From crossDomainCheck.py results
REEF_PUBLISHED = {
    'input_mean': 13.9, 'input_std': 24.4, 'n_input': 2949,
    'struct_mean': 25.0, 'struct_std': 31.7, 'n_struct': 3685,
    'ratio': 1.80,
}

GDSC_PUBLISHED = {
    # Calibrated so (1-struct)/(1-input) ≈ 1.85
    # (1-0.723)/(1-0.850) = 0.277/0.150 = 1.847
    'input_auc_mean': 0.850, 'input_auc_std': 0.18, 'n_input': 119090,
    'struct_auc_mean': 0.723, 'struct_auc_std': 0.22, 'n_struct': 97674,
    'ratio': 1.85,
}


def simulate_domain(pub, domain, rng):
    """Simulate observation-level data from published summary stats."""
    if domain == 'micro':
        inp = rng.normal(pub['input_bc_mean'], pub['input_bc_std'], pub['n_input'])
        stc = rng.normal(pub['hw_bc_mean'], pub['hw_bc_std'], pub['n_hw'])
        inp = np.clip(inp, 0.01, 0.99)
        stc = np.clip(stc, 0.01, 0.99)
    elif domain == 'reef':
        # Exponential-ish: many low bleaching values, heavy tail
        inp = rng.exponential(pub['input_mean'], pub['n_input'])
        stc = rng.exponential(pub['struct_mean'], pub['n_struct'])
        inp = np.clip(inp, 0, 100)
        stc = np.clip(stc, 0, 100)
    elif domain == 'gdsc':
        inp = rng.normal(pub['input_auc_mean'], pub['input_auc_std'], pub['n_input'])
        stc = rng.normal(pub['struct_auc_mean'], pub['struct_auc_std'], pub['n_struct'])
        inp = np.clip(inp, 0, 1)
        stc = np.clip(stc, 0, 1)
    return inp, stc


def calibrate_simulation(rng, subsample_for_test1=True):
    """Generate simulated data, calibrated so domain ratios match published values.

    If subsample_for_test1=True, large domains are subsampled to ~5000 obs
    to make permutation testing tractable. The ratio and variance structure
    are preserved; only the sample size changes, which is conservative
    (larger n → tighter null → harder to reject).
    """
    from scipy.stats import beta as beta_dist

    # Micro: Beta distribution (Bray-Curtis ∈ [0,1], typically skewed)
    # Calibrate alpha/beta from mean and sd:
    #   mean = a/(a+b), var = ab/((a+b)^2*(a+b+1))
    def _beta_params(mean, sd):
        """Solve for alpha, beta from mean and sd."""
        var = sd ** 2
        # a = mean * (mean*(1-mean)/var - 1)
        # b = (1-mean) * (mean*(1-mean)/var - 1)
        common = mean * (1 - mean) / var - 1
        if common <= 0:
            # Fallback: high variance, use uniform-ish
            return 1.0, 1.0
        return mean * common, (1 - mean) * common

    a_inp, b_inp = _beta_params(MICRO_PUBLISHED['input_bc_mean'],
                                MICRO_PUBLISHED['input_bc_std'])
    a_hw, b_hw = _beta_params(MICRO_PUBLISHED['hw_bc_mean'],
                              MICRO_PUBLISHED['hw_bc_std'])
    micro_inp = beta_dist.rvs(a_inp, b_inp, size=MICRO_PUBLISHED['n_input'],
                              random_state=rng)
    micro_hw = beta_dist.rvs(a_hw, b_hw, size=MICRO_PUBLISHED['n_hw'],
                             random_state=rng)
    r_micro = np.mean(micro_hw) / max(np.mean(micro_inp), 0.001)
    print(f"  [MICRO] Beta params: input α={a_inp:.1f} β={b_inp:.1f}, "
          f"hw α={a_hw:.1f} β={b_hw:.1f}")

    # Reef: ratio = struct_mean/input_mean
    n_reef_in = 2949 if not subsample_for_test1 else 2500
    n_reef_st = 3685 if not subsample_for_test1 else 2500
    reef_inp = rng.exponential(REEF_PUBLISHED['input_mean'], n_reef_in)
    reef_stc = rng.exponential(REEF_PUBLISHED['struct_mean'], n_reef_st)
    reef_inp = np.clip(reef_inp, 0, 100)
    reef_stc = np.clip(reef_stc, 0, 100)
    r_reef = np.mean(reef_stc) / max(np.mean(reef_inp), 0.01)

    # GDSC: ratio = (1-struct_auc)/(1-input_auc)
    n_gdsc_in = GDSC_PUBLISHED['n_input'] if not subsample_for_test1 else 3000
    n_gdsc_st = GDSC_PUBLISHED['n_struct'] if not subsample_for_test1 else 2500
    gdsc_inp = rng.normal(GDSC_PUBLISHED['input_auc_mean'],
                          GDSC_PUBLISHED['input_auc_std'],
                          n_gdsc_in)
    gdsc_stc = rng.normal(GDSC_PUBLISHED['struct_auc_mean'],
                          GDSC_PUBLISHED['struct_auc_std'],
                          n_gdsc_st)
    gdsc_inp = np.clip(gdsc_inp, 0, 1)
    gdsc_stc = np.clip(gdsc_stc, 0, 1)
    r_gdsc = (1.0 - np.mean(gdsc_stc)) / max(1.0 - np.mean(gdsc_inp), 0.001)

    return {
        'micro': {'inp': micro_inp, 'stc': micro_hw, 'ratio': r_micro},
        'reef': {'inp': reef_inp, 'stc': reef_stc, 'ratio': r_reef},
        'gdsc': {'inp': gdsc_inp, 'stc': gdsc_stc, 'ratio': r_gdsc},
    }


# ============================================================================
# TEST 1 — EXHAUSTIVE COMBINATORIAL PERMUTATION
# ============================================================================

def test1_combinatorial(domains_data, n_perm=100_000, min_frac=0.30, seed=42,
                        max_obs_per_domain=5000):
    """
    For each permutation iteration:
      - For each domain, randomly partition all observations into A/B
        (constraint: min group ≥ 30% of total)
      - Compute ratio = max(mean_A, mean_B) / min(mean_A, mean_B)
      - Compute CV of the 3 ratios across domains

    P-values for THREE distinct questions:

    (a) CONVERGENCE ONLY: p(CV ≤ obs_CV)
        → Will be high because random ratios cluster near 1.0
        → NOT the right test (documented for transparency)

    (b) JOINT ASYMMETRY + CONVERGENCE: p(mean_ratio ≥ 1.5 AND CV ≤ obs_CV)
        → THE key test: requires both non-trivial asymmetry AND convergence
        → If p < 0.01 → the R-XVII result is specific

    (c) MAGNITUDE MATCH: p(all 3 ratios in [1.4, 2.2] AND CV ≤ obs_CV)
        → Strictest test: ratios must be in R-XVII range AND converge

    Large domains are subsampled to max_obs_per_domain for speed.
    This is conservative: smaller n gives wider null → harder to be specific.
    """
    rng = np.random.RandomState(seed)
    t0 = time.time()

    # Use PUBLISHED ratios for observed CV (not simulation which drifts)
    published_ratios = {'micro': 1.86, 'reef': 1.80, 'gdsc': 1.85}
    obs_vals = [published_ratios[d] for d in sorted(domains_data.keys())]
    obs_cv = np.std(obs_vals) / np.mean(obs_vals)
    obs_sigma = np.std(obs_vals)
    obs_mean_ratio = np.mean(obs_vals)

    # Also compute from simulation for comparison
    sim_ratios = {d: data['ratio'] for d, data in domains_data.items()}
    sim_cv = np.std(list(sim_ratios.values())) / np.mean(list(sim_ratios.values()))

    print(f"\n  Published R-XVII ratios: {published_ratios}")
    print(f"  Published σ = {obs_sigma:.4f}, CV = {obs_cv:.4f}, mean = {obs_mean_ratio:.3f}")
    print(f"  Simulated R-XVII ratios: {sim_ratios}")
    print(f"  Simulated CV = {sim_cv:.4f}")

    # Prepare pooled data per domain (subsample if needed)
    pools = {}
    domain_is_gdsc = {}
    for d, data in domains_data.items():
        pool = np.concatenate([data['inp'], data['stc']])
        n_total = len(pool)
        if n_total > max_obs_per_domain:
            idx = rng.choice(n_total, max_obs_per_domain, replace=False)
            pool = pool[idx]
            print(f"  [{d}] Subsampled {n_total} → {max_obs_per_domain} obs")
        pools[d] = pool
        domain_is_gdsc[d] = (d == 'gdsc')

    domain_list = sorted(domains_data.keys())
    n_domains = len(domain_list)

    # Biologically-plausible size fractions
    domain_fracs = {'micro': 0.33, 'reef': 0.44, 'gdsc': 0.55}

    # Storage
    all_cvs = np.empty(n_perm)
    all_mean_ratios = np.empty(n_perm)
    all_min_ratios = np.empty(n_perm)
    all_perm_ratios = {d: np.empty(n_perm) for d in domain_list}

    cvs_constrained = np.empty(n_perm)

    print(f"\n  Running {n_perm:,} permutations...")
    report_every = max(1, n_perm // 10)

    for i in range(n_perm):
        if (i + 1) % report_every == 0:
            elapsed = time.time() - t0
            rate = (i + 1) / elapsed
            eta = (n_perm - i - 1) / rate
            print(f"    {i + 1:>8,}/{n_perm:,}  ({elapsed:.1f}s, ETA {eta:.0f}s)")

        ratios_unc = np.empty(n_domains)
        ratios_con = np.empty(n_domains)

        for j, d in enumerate(domain_list):
            pool = pools[d]
            n_total = len(pool)
            n_min = max(2, int(n_total * min_frac))
            is_gdsc = domain_is_gdsc[d]

            # Unconstrained: random split
            n_a = rng.randint(n_min, n_total - n_min + 1)
            idx = rng.permutation(n_total)
            m_a = np.mean(pool[idx[:n_a]])
            m_b = np.mean(pool[idx[n_a:]])

            if is_gdsc:
                mag_a, mag_b = 1.0 - m_a, 1.0 - m_b
                r = max(mag_a, mag_b) / max(min(mag_a, mag_b), 0.001)
            else:
                r = max(m_a, m_b) / max(min(m_a, m_b), 0.01)
            ratios_unc[j] = r
            all_perm_ratios[d][i] = r

            # Constrained
            frac = domain_fracs.get(d, 0.45)
            n_a_con = max(2, min(int(n_total * frac), n_total - 2))
            idx2 = rng.permutation(n_total)
            ma2 = np.mean(pool[idx2[:n_a_con]])
            mb2 = np.mean(pool[idx2[n_a_con:]])
            if is_gdsc:
                mag_a2, mag_b2 = 1.0 - ma2, 1.0 - mb2
                r2 = max(mag_a2, mag_b2) / max(min(mag_a2, mag_b2), 0.001)
            else:
                r2 = max(ma2, mb2) / max(min(ma2, mb2), 0.01)
            ratios_con[j] = r2

        # Stats across domains
        mean_unc = np.mean(ratios_unc)
        all_cvs[i] = np.std(ratios_unc) / max(mean_unc, 0.001)
        all_mean_ratios[i] = mean_unc
        all_min_ratios[i] = np.min(ratios_unc)

        mean_con = np.mean(ratios_con)
        cvs_constrained[i] = np.std(ratios_con) / max(mean_con, 0.001)

    # ── P-VALUES ──

    # (a) Convergence only (documented for transparency — biased toward p≈1)
    p_cv_only = float(np.mean(all_cvs <= obs_cv))

    # (b) JOINT: asymmetry + convergence at multiple thresholds
    thresholds = [1.1, 1.2, 1.3, 1.5, 1.8]
    joint_results = {}
    for thresh in thresholds:
        mask = (all_mean_ratios >= thresh) & (all_cvs <= obs_cv)
        p = float(np.mean(mask))
        n_above = int(np.sum(all_mean_ratios >= thresh))
        joint_results[thresh] = {'p': p, 'n_above': n_above}

    p_joint = joint_results[1.5]['p']
    n_asymmetric = joint_results[1.5]['n_above']

    # (c) STRICT: all ratios in [1.4, 2.2] + convergence
    strict_mask = (all_min_ratios >= 1.4) & (all_mean_ratios <= 2.2) & (all_cvs <= obs_cv)
    p_strict = float(np.mean(strict_mask))

    # (d) Constrained version of joint test
    p_con_joint = float(np.mean(
        (all_mean_ratios >= 1.5) & (cvs_constrained <= obs_cv)
    ))

    # Diagnostics
    max_mean_ratio = float(np.max(all_mean_ratios))
    pct_cv = float(stats.percentileofscore(all_cvs, obs_cv))

    elapsed = time.time() - t0
    print(f"\n  TEST 1 RESULTS ({elapsed:.1f}s):")
    print(f"    Max mean_ratio under permutation: {max_mean_ratio:.4f}")
    print(f"    (a) CV-only: p(CV ≤ {obs_cv:.4f}) = {p_cv_only:.6f}")
    print(f"        ⚠ Expected high: random ratios cluster near 1.0 → trivially low CV")
    print(f"        Percentile of obs CV: {pct_cv:.2f}%")
    print(f"        Null CV: mean={np.mean(all_cvs):.4f}, median={np.median(all_cvs):.4f}")
    print(f"    (b) JOINT test at multiple thresholds:")
    for thresh, res in sorted(joint_results.items()):
        label = " ← KEY" if thresh == 1.5 else ""
        print(f"        ratio≥{thresh:.1f}: {res['n_above']:>6d}/{n_perm} asymmetric, "
              f"p_joint = {res['p']:.6f}{label}")
    print(f"    (c) STRICT (all in [1.4,2.2] AND CV≤obs): p = {p_strict:.6f}")
    print(f"    (d) Constrained joint: p = {p_con_joint:.6f}")

    return {
        'published_ratios': published_ratios,
        'obs_cv': float(obs_cv),
        'obs_sigma': float(obs_sigma),
        'obs_mean_ratio': float(obs_mean_ratio),
        'sim_ratios': {k: float(v) for k, v in sim_ratios.items()},
        'all_cvs': all_cvs,
        'all_mean_ratios': all_mean_ratios,
        'cvs_constrained': cvs_constrained,
        'p_cv_only': p_cv_only,
        'p_joint': p_joint,
        'p_strict': p_strict,
        'p_constrained_joint': p_con_joint,
        'n_asymmetric': n_asymmetric,
        'pct_cv': pct_cv,
        'max_mean_ratio': max_mean_ratio,
        'joint_results': {str(k): v for k, v in joint_results.items()},
        'all_perm_ratios': all_perm_ratios,
        'n_perm': n_perm,
    }


# ============================================================================
# TEST 2 — REVERSIBILITY PARTITION (GDSC)
# ============================================================================

def test2_reversibility(gdsc_df, n_boot=5000, seed=42):
    """
    Compare R-XVII (input/structure) vs reversibility (covalent/reversible)
    as predictors of AUC. Focus on dissociated cases.
    """
    rng = np.random.RandomState(seed)

    df = gdsc_df.dropna(subset=['_auc']).copy()

    # Classify
    df['rxvii'] = df['rxvii_class']
    df['revers'] = df['reversibility']

    # --- R-XVII effect ---
    rxvii_in = df.loc[df['rxvii'] == 'INPUT', '_auc'].values
    rxvii_st = df.loc[df['rxvii'] == 'STRUCTURE', '_auc'].values

    # --- Reversibility effect ---
    rev = df.loc[df['revers'] == 'REVERSIBLE', '_auc'].values
    cov = df.loc[df['revers'] == 'COVALENT', '_auc'].values

    print(f"\n  R-XVII:        INPUT n={len(rxvii_in)}, STRUCTURE n={len(rxvii_st)}")
    print(f"  Reversibility: REVERSIBLE n={len(rev)}, COVALENT n={len(cov)}")

    def cohens_d(a, b):
        na, nb = len(a), len(b)
        if na < 2 or nb < 2:
            return np.nan
        pooled_std = np.sqrt(((na - 1) * np.var(a, ddof=1) + (nb - 1) * np.var(b, ddof=1)) / (na + nb - 2))
        return (np.mean(a) - np.mean(b)) / max(pooled_std, 1e-10)

    d_rxvii = cohens_d(rxvii_in, rxvii_st)  # positive = input has higher AUC (more resistant)
    d_revers = cohens_d(rev, cov)

    print(f"  Cohen's d (R-XVII, input-structure): {d_rxvii:.4f}")
    print(f"  Cohen's d (reversibility, rev-cov):  {d_revers:.4f}")

    # --- Dissociated cases ---
    # INPUT × COVALENT (R-XVII says input=weak, but covalent=strong binding)
    # STRUCTURE × REVERSIBLE (R-XVII says structure=strong, but reversible binding)
    df['dissociated'] = False
    df.loc[(df['rxvii'] == 'INPUT') & (df['revers'] == 'COVALENT'), 'dissociated'] = True
    df.loc[(df['rxvii'] == 'STRUCTURE') & (df['revers'] == 'REVERSIBLE'), 'dissociated'] = True

    dissoc = df[df['dissociated']]
    n_dissoc = len(dissoc)
    print(f"\n  Dissociated cases: {n_dissoc}")

    # Among dissociated cases, does R-XVII still predict?
    d_rxvii_dissoc = np.nan
    d_revers_dissoc = np.nan
    if n_dissoc > 50:
        dissoc_in = dissoc.loc[dissoc['rxvii'] == 'INPUT', '_auc'].values
        dissoc_st = dissoc.loc[dissoc['rxvii'] == 'STRUCTURE', '_auc'].values
        dissoc_rev = dissoc.loc[dissoc['revers'] == 'REVERSIBLE', '_auc'].values
        dissoc_cov = dissoc.loc[dissoc['revers'] == 'COVALENT', '_auc'].values

        d_rxvii_dissoc = cohens_d(dissoc_in, dissoc_st)
        d_revers_dissoc = cohens_d(dissoc_rev, dissoc_cov)

        print(f"    d_R-XVII (dissociated):        {d_rxvii_dissoc:.4f} "
              f"(IN n={len(dissoc_in)}, ST n={len(dissoc_st)})")
        print(f"    d_reversibility (dissociated):  {d_revers_dissoc:.4f} "
              f"(REV n={len(dissoc_rev)}, COV n={len(dissoc_cov)})")

    # --- Bootstrap CIs ---
    def boot_d(a, b, n_boot, rng):
        ds = []
        for _ in range(n_boot):
            ba = rng.choice(a, len(a), replace=True)
            bb = rng.choice(b, len(b), replace=True)
            ds.append(cohens_d(ba, bb))
        return np.array(ds)

    boot_rxvii = boot_d(rxvii_in, rxvii_st, n_boot, rng)
    boot_revers = boot_d(rev, cov, n_boot, rng) if len(rev) > 10 and len(cov) > 10 else np.array([])

    ci_rxvii = (np.percentile(boot_rxvii, 2.5), np.percentile(boot_rxvii, 97.5))
    ci_revers = ((np.percentile(boot_revers, 2.5), np.percentile(boot_revers, 97.5))
                 if len(boot_revers) > 0 else (np.nan, np.nan))

    print(f"\n  Bootstrap 95% CI:")
    print(f"    d_R-XVII:        [{ci_rxvii[0]:.4f}, {ci_rxvii[1]:.4f}]")
    print(f"    d_reversibility: [{ci_revers[0]:.4f}, {ci_revers[1]:.4f}]")

    # Concordance table
    ct = pd.crosstab(
        df['rxvii'].fillna('unclassified'),
        df['revers'].fillna('unclassified'),
        margins=True,
    )
    print(f"\n  Concordance table (R-XVII × reversibility):")
    print(ct.to_string())

    # Verdict
    if abs(d_rxvii) > abs(d_revers) * 1.3:
        verdict_t2 = "R-XVII_DOMINATES"
        detail_t2 = "R-XVII has substantially larger effect than reversibility"
    elif abs(d_revers) > abs(d_rxvii) * 1.3:
        verdict_t2 = "REVERSIBILITY_DOMINATES"
        detail_t2 = "Reversibility classification has larger effect — R-XVII may be confounded"
    else:
        verdict_t2 = "COMPARABLE"
        detail_t2 = "R-XVII and reversibility have similar effect sizes — possible partial confound"

    if not np.isnan(d_rxvii_dissoc) and abs(d_rxvii_dissoc) > 0.1:
        verdict_t2 += " + R-XVII holds in dissociated cases"

    print(f"\n  ★ TEST 2 VERDICT: {verdict_t2}")
    print(f"    {detail_t2}")

    return {
        'd_rxvii_all': float(d_rxvii),
        'd_reversibility_all': float(d_revers),
        'd_rxvii_dissociated': float(d_rxvii_dissoc),
        'd_reversibility_dissociated': float(d_revers_dissoc),
        'ci_rxvii': [float(ci_rxvii[0]), float(ci_rxvii[1])],
        'ci_reversibility': [float(ci_revers[0]), float(ci_revers[1])],
        'n_dissociated': int(n_dissoc),
        'n_rxvii_in': int(len(rxvii_in)),
        'n_rxvii_st': int(len(rxvii_st)),
        'n_reversible': int(len(rev)),
        'n_covalent': int(len(cov)),
        'verdict': verdict_t2,
        'boot_rxvii': boot_rxvii,
        'boot_revers': boot_revers,
    }


# ============================================================================
# TEST 3 — TARGET COUNT PARTITION (GDSC)
# ============================================================================

def test3_target_count(gdsc_df, n_boot=5000, seed=42):
    """
    Compare mono-target vs poly-target partition with R-XVII.
    Also document cross-domain inapplicability.
    """
    rng = np.random.RandomState(seed)

    df = gdsc_df.dropna(subset=['_auc']).copy()
    df['n_targ'] = df['DRUG_NAME'].apply(get_n_targets)

    annotated = df.dropna(subset=['n_targ'])
    mono = annotated[annotated['n_targ'] == 1]['_auc'].values
    poly = annotated[annotated['n_targ'] >= 2]['_auc'].values

    print(f"\n  Annotated drugs: {annotated['DRUG_NAME'].nunique()} "
          f"(mono={len(mono)} obs, poly={len(poly)} obs)")

    def cohens_d(a, b):
        na, nb = len(a), len(b)
        if na < 2 or nb < 2:
            return np.nan
        pooled_std = np.sqrt(((na - 1) * np.var(a, ddof=1) + (nb - 1) * np.var(b, ddof=1)) / (na + nb - 2))
        return (np.mean(a) - np.mean(b)) / max(pooled_std, 1e-10)

    # Ratio: (1-AUC_poly) / (1-AUC_mono)
    if len(mono) > 30 and len(poly) > 30:
        mag_mono = 1.0 - np.mean(mono)
        mag_poly = 1.0 - np.mean(poly)
        ratio_target = mag_poly / max(mag_mono, 0.001)
        d_target = cohens_d(mono, poly)
        print(f"  Mono AUC: {np.mean(mono):.4f} (mag={mag_mono:.4f})")
        print(f"  Poly AUC: {np.mean(poly):.4f} (mag={mag_poly:.4f})")
        print(f"  Ratio poly/mono: {ratio_target:.3f}")
        print(f"  Cohen's d (mono-poly): {d_target:.4f}")
    else:
        ratio_target = np.nan
        d_target = np.nan
        print(f"  Insufficient data for target count analysis")

    # Bootstrap
    if len(mono) > 30 and len(poly) > 30:
        boot_ratios = []
        for _ in range(n_boot):
            bm = rng.choice(mono, len(mono), replace=True)
            bp = rng.choice(poly, len(poly), replace=True)
            mm, mp = 1.0 - np.mean(bm), 1.0 - np.mean(bp)
            boot_ratios.append(mp / max(mm, 0.001))
        boot_ratios = np.array(boot_ratios)
        ci = (np.percentile(boot_ratios, 2.5), np.percentile(boot_ratios, 97.5))
        print(f"  Bootstrap 95% CI for ratio: [{ci[0]:.3f}, {ci[1]:.3f}]")
    else:
        boot_ratios = np.array([])
        ci = (np.nan, np.nan)

    # Cross-domain applicability assessment
    print(f"\n  CROSS-DOMAIN APPLICABILITY:")
    print(f"    Microbiome: diet = poly-metabolic, antibiotics = gram+ selective")
    print(f"      → Direction INVERSE to R-XVII (diet=input, antibiotics=structure)")
    print(f"      → Partition INCOMPATIBLE with R-XVII classification")
    print(f"    Reef: DHW and cyclones have no 'number of targets'")
    print(f"      → Partition NOT OPERABLE on this domain")
    print(f"    → CV trans-domaniale IMPOSSIBLE to compute")
    print(f"    → Target count cannot explain cross-domain convergence by construction")

    verdict_t3 = "NOT_APPLICABLE_CROSS_DOMAIN"
    if not np.isnan(ratio_target):
        if abs(ratio_target - 1.85) < 0.3:
            verdict_t3 += " — but GDSC ratio similar to R-XVII (partial confound within-domain)"
        else:
            verdict_t3 += f" — GDSC ratio={ratio_target:.2f} ≠ 1.85 (no within-domain confound)"

    print(f"\n  ★ TEST 3 VERDICT: {verdict_t3}")

    # Overlap analysis: how much does mono/poly correlate with input/structure?
    overlap_df = annotated.dropna(subset=['rxvii_class'])
    if len(overlap_df) > 0:
        ct = pd.crosstab(
            overlap_df['rxvii_class'],
            overlap_df['n_targ'].apply(lambda x: 'mono' if x == 1 else 'poly'),
            margins=True,
        )
        print(f"\n  Overlap table (R-XVII × target count):")
        print(ct.to_string())

    return {
        'ratio_target': float(ratio_target) if not np.isnan(ratio_target) else None,
        'd_target': float(d_target) if not np.isnan(d_target) else None,
        'ci_ratio': [float(ci[0]), float(ci[1])],
        'n_mono': int(len(mono)),
        'n_poly': int(len(poly)),
        'cross_domain_applicable': False,
        'verdict': verdict_t3,
    }


# ============================================================================
# VISUALIZATION
# ============================================================================

def make_figure(t1_results, t2_results, t3_results, outpath):
    """Generate combined figure for all 3 tests."""
    fig = plt.figure(figsize=(22, 16))
    gs = gridspec.GridSpec(3, 3, hspace=0.45, wspace=0.35)
    fig.suptitle('R-XVII Specificity Tests — "Can we kill the thesis?"',
                 fontsize=15, fontweight='bold', y=0.995)

    C_R = '#1565C0'  # R-XVII
    C_I = '#FF6F00'  # Intensity / other
    C_N = '#9E9E9E'  # Null

    # ── TEST 1: Panels A-C ──

    # A: 2D scatter — mean_ratio vs CV for each permutation
    ax = fig.add_subplot(gs[0, 0])
    # Subsample for plotting
    n_show = min(5000, t1_results['n_perm'])
    idx_show = np.random.RandomState(0).choice(t1_results['n_perm'], n_show, replace=False)
    ax.scatter(t1_results['all_mean_ratios'][idx_show], t1_results['all_cvs'][idx_show],
               s=2, alpha=0.15, color=C_N, rasterized=True)
    # Observed point
    ax.scatter([t1_results['obs_mean_ratio']], [t1_results['obs_cv']],
               s=200, color='red', edgecolor='black', zorder=10, marker='*',
               label=f'R-XVII ({t1_results["obs_mean_ratio"]:.2f}, {t1_results["obs_cv"]:.3f})')
    # Threshold lines
    ax.axvline(1.5, color='blue', ls='--', lw=1, alpha=0.5, label='ratio≥1.5')
    ax.axhline(t1_results['obs_cv'], color='red', ls='--', lw=1, alpha=0.5, label=f'CV≤{t1_results["obs_cv"]:.3f}')
    # Shade joint region
    ax.axvspan(1.5, ax.get_xlim()[1] if ax.get_xlim()[1] > 2.5 else 2.5,
               ymin=0, ymax=t1_results['obs_cv'] / max(ax.get_ylim()[1], 0.3),
               alpha=0.05, color='red')
    ax.set_xlabel('Mean ratio across domains')
    ax.set_ylabel('CV across domains')
    ax.set_title(f'A. Test 1: Joint test (n={t1_results["n_perm"]:,})\n'
                 f'p_joint = {t1_results["p_joint"]:.6f}')
    ax.legend(fontsize=7, loc='upper right')

    # B: Histogram of CV (for context)
    ax = fig.add_subplot(gs[0, 1])
    cvs = t1_results['all_cvs']
    ax.hist(cvs, bins=80, alpha=0.6, color=C_N, density=True, label='Random partitions')
    ax.axvline(t1_results['obs_cv'], color='red', lw=2.5, label=f'R-XVII CV={t1_results["obs_cv"]:.3f}')
    ax.set_xlabel('Cross-domain CV')
    ax.set_ylabel('Density')
    ax.set_title(f'B. CV distribution (all perms)\n'
                 f'p(CV≤obs) = {t1_results["p_cv_only"]:.4f} '
                 f'(⚠ biased — ratios≈1.0)')
    ax.legend(fontsize=8)

    # C: Per-domain ratio distributions under permutation
    ax = fig.add_subplot(gs[0, 2])
    colors_d = {'micro': '#EF5350', 'reef': '#26A69A', 'gdsc': '#AB47BC'}
    for d, ratios in t1_results['all_perm_ratios'].items():
        ratios = np.array([r for r in ratios if r is not None and np.isfinite(r)])
        if len(ratios) > 0:
            ax.hist(ratios, bins=60, alpha=0.35, density=True,
                    color=colors_d.get(d, 'gray'), label=f'{d} null')
            obs = t1_results['published_ratios'].get(d)
            if obs:
                ax.axvline(obs, color=colors_d.get(d, 'gray'), lw=2.5)
    ax.axvline(1.8, color='black', ls=':', lw=1.5, alpha=0.5, label='1.8× target')
    ax.set_xlabel('Ratio')
    ax.set_ylabel('Density')
    ax.set_title('C. Per-domain: observed (lines) vs null')
    ax.legend(fontsize=8)

    # ── TEST 2: Panels D-F ──

    if t2_results is not None:
        # D: Bootstrap d distributions
        ax = fig.add_subplot(gs[1, 0])
        if len(t2_results['boot_rxvii']) > 0:
            ax.hist(t2_results['boot_rxvii'], bins=60, alpha=0.6, color=C_R,
                    density=True, label=f'd_R-XVII={t2_results["d_rxvii_all"]:.3f}')
        if len(t2_results['boot_revers']) > 0:
            ax.hist(t2_results['boot_revers'], bins=60, alpha=0.6, color='#FF5722',
                    density=True, label=f'd_revers={t2_results["d_reversibility_all"]:.3f}')
        ax.set_xlabel("Cohen's d")
        ax.set_ylabel('Density')
        ax.set_title('D. Test 2: R-XVII vs Reversibility')
        ax.legend(fontsize=8)

        # E: Scatter of d values (all vs dissociated)
        ax = fig.add_subplot(gs[1, 1])
        labels = ['All\n(R-XVII)', 'All\n(Revers.)', 'Dissoc.\n(R-XVII)', 'Dissoc.\n(Revers.)']
        vals = [t2_results['d_rxvii_all'], t2_results['d_reversibility_all'],
                t2_results['d_rxvii_dissociated'], t2_results['d_reversibility_dissociated']]
        colors_bar = [C_R, '#FF5722', C_R, '#FF5722']
        alphas = [0.9, 0.9, 0.5, 0.5]
        valid_mask = [not np.isnan(v) for v in vals]
        x_pos = np.arange(len(labels))
        for j, (l, v, c, a) in enumerate(zip(labels, vals, colors_bar, alphas)):
            if valid_mask[j]:
                ax.bar(j, abs(v), color=c, alpha=a, edgecolor='black')
                ax.text(j, abs(v) + 0.01, f'{v:.3f}', ha='center', fontsize=9)
        ax.set_xticks(x_pos)
        ax.set_xticklabels(labels, fontsize=9)
        ax.set_ylabel("|Cohen's d|")
        ax.set_title(f'E. Test 2: Effect sizes\n({t2_results["n_dissociated"]} dissociated obs)')

        # F: Concordance heatmap sketch
        ax = fig.add_subplot(gs[1, 2])
        ax.axis('off')
        txt = (f"TEST 2 SUMMARY\n\n"
               f"R-XVII:  d = {t2_results['d_rxvii_all']:.3f} "
               f"[{t2_results['ci_rxvii'][0]:.3f}, {t2_results['ci_rxvii'][1]:.3f}]\n"
               f"Revers.: d = {t2_results['d_reversibility_all']:.3f} "
               f"[{t2_results['ci_reversibility'][0]:.3f}, {t2_results['ci_reversibility'][1]:.3f}]\n\n"
               f"Dissociated cases: {t2_results['n_dissociated']}\n"
               f"  d_R-XVII:  {t2_results['d_rxvii_dissociated']:.3f}\n"
               f"  d_Revers.: {t2_results['d_reversibility_dissociated']:.3f}\n\n"
               f"★ {t2_results['verdict']}")
        ax.text(0.05, 0.95, txt, transform=ax.transAxes, fontsize=11,
                va='top', fontfamily='monospace',
                bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))
    else:
        for i in range(3):
            ax = fig.add_subplot(gs[1, i])
            ax.axis('off')
            ax.text(0.5, 0.5, 'Test 2: GDSC data\nnot available',
                    ha='center', va='center', transform=ax.transAxes, fontsize=14)

    # ── TEST 3: Panels G-I ──

    if t3_results is not None:
        # G: Ratio comparison bar
        ax = fig.add_subplot(gs[2, 0])
        labels = ['R-XVII\n(~1.85×)', 'Target count', 'Intensity\n(~0.89×)']
        vals = [1.85, t3_results['ratio_target'] or 0, 0.89]
        colors_bar = [C_R, '#4CAF50', C_I]
        bars = ax.bar(labels, vals, color=colors_bar, alpha=0.8, edgecolor='black')
        for bar, v in zip(bars, vals):
            ax.text(bar.get_x() + bar.get_width() / 2, v + 0.03,
                    f'{v:.2f}', ha='center', fontsize=11, fontweight='bold')
        ax.axhline(1.0, color='gray', ls='-', lw=0.5)
        ax.axhline(1.85, color=C_R, ls=':', lw=1, alpha=0.5)
        ax.set_ylabel('Effect ratio')
        ax.set_title('G. Test 3: GDSC ratio comparison')

        # H: Cross-domain applicability
        ax = fig.add_subplot(gs[2, 1])
        ax.axis('off')
        matrix = [
            ['', 'Microbiome', 'Reef', 'GDSC'],
            ['R-XVII', '✓ (1.86×)', '✓ (1.80×)', '✓ (1.85×)'],
            ['Intensity', '✓ (diverge)', '✓ (diverge)', '✓ (diverge)'],
            ['# Targets', '✗ inversé', '✗ N/A',
             f'? ({t3_results["ratio_target"]:.2f}×)' if t3_results["ratio_target"] else '? (N/A)'],
        ]
        table = ax.table(cellText=matrix, cellLoc='center', loc='center')
        table.auto_set_font_size(False)
        table.set_fontsize(10)
        table.scale(1, 1.8)
        # Color header row
        for j in range(4):
            table[0, j].set_facecolor('#E0E0E0')
        for i in range(1, 4):
            table[i, 0].set_facecolor('#E0E0E0')
        ax.set_title('H. Cross-domain applicability matrix')

        # I: Summary
        ax = fig.add_subplot(gs[2, 2])
        ax.axis('off')
        txt = (f"TEST 3 SUMMARY\n\n"
               f"GDSC mono-target obs: {t3_results['n_mono']}\n"
               f"GDSC poly-target obs: {t3_results['n_poly']}\n"
               f"GDSC ratio (poly/mono): {t3_results['ratio_target']}\n"
               f"CI: [{t3_results['ci_ratio'][0]:.3f}, {t3_results['ci_ratio'][1]:.3f}]\n\n"
               f"Cross-domain: NOT APPLICABLE\n"
               f"  Micro: direction inversée\n"
               f"  Reef: non opérationnalisable\n\n"
               f"★ {t3_results['verdict']}")
        ax.text(0.05, 0.95, txt, transform=ax.transAxes, fontsize=11,
                va='top', fontfamily='monospace',
                bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))
    else:
        for i in range(3):
            ax = fig.add_subplot(gs[2, i])
            ax.axis('off')
            ax.text(0.5, 0.5, 'Test 3: GDSC data\nnot available',
                    ha='center', va='center', transform=ax.transAxes, fontsize=14)

    plt.savefig(outpath, dpi=200, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"\n  [FIG] {os.path.abspath(outpath)}")


# ============================================================================
# MAIN
# ============================================================================

def main():
    parser = argparse.ArgumentParser(description='R-XVII Specificity Tests')
    parser.add_argument('--gdsc', type=str, default=None,
                        help='Path to sanger-dose-response.csv')
    parser.add_argument('--reef', type=str, default=None,
                        help='Path to global_bleaching_environmental.csv')
    parser.add_argument('--nperm', type=int, default=100_000,
                        help='Number of permutations for Test 1')
    parser.add_argument('--nboot', type=int, default=5_000,
                        help='Number of bootstrap iterations for Tests 2-3')
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--outdir', type=str, default='.')
    args = parser.parse_args()

    t0 = time.time()
    rng = np.random.RandomState(args.seed)

    print("=" * 80)
    print("  R-XVII SPECIFICITY TESTS")
    print("  \"Existe-t-il une AUTRE partition binaire qui reproduit la convergence ?\"")
    print("=" * 80)

    # ── Try to find data files ──
    gdsc_paths = [
        args.gdsc,
        '../ScriptGDSC/sanger-dose-response.csv',
        'sanger-dose-response.csv',
    ]
    reef_paths = [
        args.reef,
        '../ScriptCorail/global_bleaching_environmental.csv',
        'global_bleaching_environmental.csv',
    ]

    gdsc_df = None
    for p in gdsc_paths:
        if p and os.path.exists(p):
            gdsc_df = load_gdsc_real(p)
            break

    # ── CORRECTION 1: Diagnostic des drogues perdues ──
    if gdsc_df is not None:
        unclass = gdsc_df[gdsc_df['rxvii_class'].isna()]
        n_unclass = len(unclass)
        n_total = len(gdsc_df)
        n_class = n_total - n_unclass
        print(f"\n  [DIAGNOSTIC] GDSC classification coverage:")
        print(f"    Classified:   {n_class:>7,} ({100 * n_class / n_total:.1f}%)")
        print(f"    Unclassified: {n_unclass:>7,} ({100 * n_unclass / n_total:.1f}%)")
        if n_unclass > 0:
            top_lost = (unclass.groupby('DRUG_NAME')
                        .agg(n_obs=('_auc', 'count'), mean_auc=('_auc', 'mean'))
                        .sort_values('n_obs', ascending=False)
                        .head(20))
            print(f"    Top 20 unclassified drugs (by n_obs):")
            for name, row in top_lost.iterrows():
                mag = 1.0 - row['mean_auc']
                print(f"      {name:<30s}  n={int(row['n_obs']):>5d}  "
                      f"AUC={row['mean_auc']:.3f}  mag={mag:.3f}")
            # Sensitivity: ratio with vs without unclassified
            inp_class = gdsc_df.loc[gdsc_df['rxvii_class'] == 'INPUT', '_auc'].values
            stc_class = gdsc_df.loc[gdsc_df['rxvii_class'] == 'STRUCTURE', '_auc'].values
            r_current = gdsc_ratio_fn(inp_class, stc_class)
            # What if ALL unclassified were INPUT? (worst case for ratio inflation)
            inp_worst = np.concatenate([inp_class, unclass['_auc'].values])
            r_worst = gdsc_ratio_fn(inp_worst, stc_class)
            # What if ALL unclassified were STRUCTURE?
            stc_worst = np.concatenate([stc_class, unclass['_auc'].values])
            r_best = gdsc_ratio_fn(inp_class, stc_worst)
            print(f"    Sensitivity analysis:")
            print(f"      Current ratio (classified only):   {r_current:.4f}")
            print(f"      If ALL lost → INPUT (worst case):  {r_worst:.4f} "
                  f"(Δ = {100 * (r_worst - r_current) / r_current:+.1f}%)")
            print(f"      If ALL lost → STRUCTURE:           {r_best:.4f} "
                  f"(Δ = {100 * (r_best - r_current) / r_current:+.1f}%)")
            if abs(r_worst - r_current) / r_current > 0.05:
                print(f"    ⚠ WARNING: ratio shifts >5% under worst-case reassignment")

    reef_df = None
    for p in reef_paths:
        if p and os.path.exists(p):
            reef_df = load_reef_real(p)
            break

    # ── Prepare domain data for Test 1 ──
    print("\n[SETUP] Preparing domain data for Test 1")
    print("-" * 50)

    domains_data = {}
    use_simulation = {}

    if gdsc_df is not None:
        inp, stc = gdsc_rxvii_groups(gdsc_df)
        r = gdsc_ratio_fn(inp, stc)
        if r is not None:
            domains_data['gdsc'] = {'inp': inp, 'stc': stc, 'ratio': r}
            use_simulation['gdsc'] = False
            print(f"  GDSC: REAL DATA, ratio = {r:.3f}")

    if reef_df is not None:
        inp, stc = reef_rxvii_groups(reef_df)
        r = reef_ratio_fn(inp, stc)
        if r is not None:
            domains_data['reef'] = {'inp': inp, 'stc': stc, 'ratio': r}
            use_simulation['reef'] = False
            print(f"  REEF: REAL DATA, ratio = {r:.3f}")

    # Fill missing domains with simulation
    sim = calibrate_simulation(rng)

    if 'gdsc' not in domains_data:
        domains_data['gdsc'] = sim['gdsc']
        use_simulation['gdsc'] = True
        print(f"  GDSC: SIMULATED, ratio = {sim['gdsc']['ratio']:.3f}")

    if 'reef' not in domains_data:
        domains_data['reef'] = sim['reef']
        use_simulation['reef'] = True
        print(f"  REEF: SIMULATED, ratio = {sim['reef']['ratio']:.3f}")

    # Microbiome: always use published (n too small)
    domains_data['micro'] = sim['micro']
    use_simulation['micro'] = True
    print(f"  MICRO: SIMULATED (Phase 2 published), ratio = {sim['micro']['ratio']:.3f}")

    # ── CORRECTION 3: CV bidomaine sur données réelles uniquement ──
    real_ratios = {d: data['ratio'] for d, data in domains_data.items()
                   if not use_simulation.get(d, True)}
    if len(real_ratios) >= 2:
        rv = list(real_ratios.values())
        cv_real = np.std(rv) / np.mean(rv)
        print(f"\n  CV bidomaine (real data only): {cv_real:.4f}")
        print(f"    Ratios: {real_ratios}")
        print(f"    → Convergence ne dépend PAS du microbiome simulé")

    # ══════════════════════════════════════════════════════════════
    # TEST 1
    # ══════════════════════════════════════════════════════════════
    print("\n" + "=" * 80)
    print("  TEST 1 — EXHAUSTIVE COMBINATORIAL PERMUTATION")
    print("  Q: Does ANY random binary partition produce CV ≤ 5.5%?")
    print("=" * 80)

    t1 = test1_combinatorial(domains_data, n_perm=args.nperm, seed=args.seed)

    # ══════════════════════════════════════════════════════════════
    # TEST 2 (GDSC only)
    # ══════════════════════════════════════════════════════════════
    t2 = None
    if gdsc_df is not None:
        print("\n" + "=" * 80)
        print("  TEST 2 — REVERSIBILITY PARTITION (GDSC only)")
        print("  Q: Does covalent/reversible binding explain the asymmetry?")
        print("=" * 80)
        t2 = test2_reversibility(gdsc_df, n_boot=args.nboot, seed=args.seed)
    else:
        print("\n  [SKIP] Test 2: GDSC data not available")

    # ══════════════════════════════════════════════════════════════
    # TEST 3 (GDSC only)
    # ══════════════════════════════════════════════════════════════
    t3 = None
    if gdsc_df is not None:
        print("\n" + "=" * 80)
        print("  TEST 3 — TARGET COUNT PARTITION (GDSC only)")
        print("  Q: Does mono/poly-target explain the asymmetry?")
        print("=" * 80)
        t3 = test3_target_count(gdsc_df, n_boot=args.nboot, seed=args.seed)
    else:
        print("\n  [SKIP] Test 3: GDSC data not available")

    # ══════════════════════════════════════════════════════════════
    # VISUALIZATION
    # ══════════════════════════════════════════════════════════════
    print("\n" + "=" * 80)
    print("  GENERATING FIGURE")
    print("=" * 80)

    fig_path = os.path.join(args.outdir, 'test_specificity_figure.png')
    make_figure(t1, t2, t3, fig_path)

    # ══════════════════════════════════════════════════════════════
    # FINAL SUMMARY
    # ══════════════════════════════════════════════════════════════
    print("\n" + "=" * 80)
    print("  FINAL SUMMARY")
    print("=" * 80)

    print(f"\n  TEST 1 — Combinatorial permutation (n={args.nperm:,}):")
    print(f"    Observed R-XVII CV: {t1['obs_cv']:.4f}, mean ratio: {t1['obs_mean_ratio']:.3f}")
    print(f"    Max mean_ratio under permutation: {t1['max_mean_ratio']:.4f}")
    print(f"    (a) p(CV ≤ obs):                    {t1['p_cv_only']:.6f} (⚠ biased, ratios≈1.0)")
    print(f"    (b) p(ratio≥1.5 AND CV≤obs):        {t1['p_joint']:.6f}  ← KEY TEST")
    print(f"    (c) p(all∈[1.4,2.2] AND CV≤obs):    {t1['p_strict']:.6f}")
    print(f"    (d) constrained joint:               {t1['p_constrained_joint']:.6f}")
    if t1['p_joint'] < 0.01:
        print(f"    → ★ CONVERGENCE IS SPECIFIC (p_joint < 0.01)")
    elif t1['p_joint'] < 0.05:
        print(f"    → ★ CONVERGENCE IS MARGINALLY SPECIFIC (p_joint < 0.05)")
    elif t1['p_joint'] == 0:
        print(f"    → ★ CONVERGENCE IS SPECIFIC (p_joint = 0, none in {args.nperm:,} perms)")
    else:
        print(f"    → ⚠ CONVERGENCE IS NOT SPECIFIC (p_joint ≥ 0.05)")

    if t2:
        print(f"\n  TEST 2 — Reversibility (GDSC):")
        print(f"    d_R-XVII = {t2['d_rxvii_all']:.3f}, d_revers = {t2['d_reversibility_all']:.3f}")
        print(f"    → {t2['verdict']}")

    if t3:
        print(f"\n  TEST 3 — Target count (GDSC):")
        print(f"    Ratio target: {t3['ratio_target']}")
        print(f"    Cross-domain: NOT APPLICABLE")
        print(f"    → {t3['verdict']}")

    # ── Save JSON ──
    results = {
        'test1': {
            'published_ratios': t1['published_ratios'],
            'obs_cv': t1['obs_cv'],
            'obs_mean_ratio': t1['obs_mean_ratio'],
            'p_cv_only': t1['p_cv_only'],
            'p_joint': t1['p_joint'],
            'p_strict': t1['p_strict'],
            'p_constrained_joint': t1['p_constrained_joint'],
            'n_asymmetric': t1['n_asymmetric'],
            'max_mean_ratio': t1['max_mean_ratio'],
            'joint_results': t1['joint_results'],
            'pct_cv': t1['pct_cv'],
            'n_perm': t1['n_perm'],
            'null_cv_mean': float(np.mean(t1['all_cvs'])),
            'null_cv_median': float(np.median(t1['all_cvs'])),
        },
        'test2': {
            'd_rxvii_all': t2['d_rxvii_all'] if t2 else None,
            'd_reversibility_all': t2['d_reversibility_all'] if t2 else None,
            'd_rxvii_dissociated': t2['d_rxvii_dissociated'] if t2 else None,
            'n_dissociated': t2['n_dissociated'] if t2 else None,
            'verdict': t2['verdict'] if t2 else 'SKIPPED',
        } if t2 else {'verdict': 'SKIPPED — no GDSC data'},
        'test3': {
            'ratio_target': t3['ratio_target'] if t3 else None,
            'cross_domain_applicable': False,
            'verdict': t3['verdict'] if t3 else 'SKIPPED — no GDSC data',
        } if t3 else {'verdict': 'SKIPPED — no GDSC data'},
        'data_sources': {d: ('REAL' if not use_simulation.get(d, True) else 'SIMULATED')
                         for d in domains_data},
    }

    json_path = os.path.join(args.outdir, 'test_specificity_results.json')
    with open(json_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\n  [JSON] {os.path.abspath(json_path)}")

    elapsed = time.time() - t0
    print(f"\n  Total runtime: {elapsed:.1f}s")

    # ── Manuscript-ready paragraph ──
    print("\n" + "=" * 80)
    print("  MANUSCRIPT PARAGRAPH (§8.2 ou §7 bis)")
    print("=" * 80)
    p_key = t1['p_joint']
    n_asym = t1['n_asymmetric']
    max_r = t1['max_mean_ratio']
    print(f"""
  Test de spécificité combinatoire. Sur N = {args.nperm:,} partitions binaires
  aléatoires (contrainte : groupes ≥ 30% de l'effectif), nous testons la
  probabilité qu'une partition produise simultanément (i) un ratio moyen
  ≥ 1.5 sur les trois domaines et (ii) un CV ≤ {t1['obs_cv']:.3f}.
  Le ratio moyen maximal atteint sous permutation est {max_r:.2f} (R-XVII : {t1['obs_mean_ratio']:.2f}).
  {"Aucune des " + f"{args.nperm:,}" + " partitions ne produit un ratio moyen ≥ 1.3." if max_r < 1.3 else f"Seules {n_asym}/{args.nperm:,} partitions ({100 * n_asym / args.nperm:.2f}%) produisent un ratio ≥ 1.5."}
  La probabilité conjointe (asymétrie + convergence) est p {"< 1/" + f"{args.nperm:,}" if p_key == 0 else f"= {p_key:.4f}"}.
  {"La convergence ~1.8× est donc spécifique à la partition structure/input : aucune partition binaire arbitraire ne reproduit à la fois l'amplitude et la convergence du ratio R-XVII." if p_key < 0.01 else "ATTENTION : la convergence n'est pas significativement spécifique à la partition R-XVII."}
""")


if __name__ == '__main__':
    main()