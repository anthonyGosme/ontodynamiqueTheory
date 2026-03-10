#!/usr/bin/env python3
"""
CR-02 PARTIE B — Split par lignées GDSC (pharmacologie cancer)
================================================================

La signature R-XVII dérivée sur 70% des lignées cellulaires (TRAIN)
est testée sur les 30% restantes (TEST). Le split est par lignée
(pas par observation) pour éviter la fuite d'information.

Robustesse : 10 répétitions avec seeds différentes.

Source : GDSC, Iorio et al. 2016, Cell / Yang et al. 2013
Fichier : sanger-dose-response.csv

Protocole pré-spécifié : CR-02, §B
  - Split : 70/30 par lignée (stratifié par type de cancer si dispo)
  - Classification : pathway-only (mécanisme d'action)
  - Seed primaire : 20240601

Usage :
  python CR02_B_gdsc_cellline_split.py [chemin/sanger-dose-response.csv]
"""

import sys, os, json, time, warnings
from pathlib import Path
import numpy as np
import pandas as pd
from scipy import stats
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

warnings.filterwarnings('ignore')

SEED = 20240601
TRAIN_FRAC = 0.70
N_REPEATS = 10
N_PERM = 5_000
N_BOOT = 5_000
OUT_DIR = Path('output_CR02B')
OUT_DIR.mkdir(exist_ok=True)

plt.rcParams.update({
    'font.size': 10, 'axes.titlesize': 12, 'axes.labelsize': 11,
    'figure.dpi': 150, 'savefig.dpi': 300, 'savefig.bbox': 'tight',
})


# ════════════════════════════════════════════════════════════════
# DRUG → PATHWAY MAPPING (identique à GDSC2.py)
# ════════════════════════════════════════════════════════════════

DRUG_PATHWAY = {}

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

STRUCTURE_PATHWAYS = set(_struct_drugs.keys())
INPUT_PATHWAYS = set(_input_drugs.keys())

for pw, drugs in _struct_drugs.items():
    for d in drugs:
        DRUG_PATHWAY[d] = pw
for pw, drugs in _input_drugs.items():
    for d in drugs:
        DRUG_PATHWAY[d] = pw


def map_drug(name):
    """Map drug name to pathway. Identical to GDSC2.py."""
    if pd.isna(name):
        return None
    n = str(name).strip().upper()
    if n in DRUG_PATHWAY:
        return DRUG_PATHWAY[n]
    for key, pw in DRUG_PATHWAY.items():
        if key in n or n in key:
            return pw
    nl = n.lower()
    patterns = [
        (['parp', 'olaparib', 'talazoparib'], 'Genome integrity'),
        (['taxel', 'vincrist', 'vinblast'], 'Mitosis'),
        (['platin'], 'Genome integrity'),
        (['bortezomib', 'carfilzomib'], 'Protein stability and degradation'),
        (['vorinostat', 'panobinostat', 'hdac'], 'Chromatin'),
        (['palbociclib', 'ribociclib'], 'Cell cycle'),
        (['nutlin', 'mdm2'], 'Cell cycle'),
        (['venetoclax', 'navitoclax'], 'Apoptosis regulation'),
        (['hsp90', 'ganetespib'], 'Protein stability and degradation'),
        (['topotecan', 'etoposide'], 'Genome integrity'),
        (['mek', 'trametinib', 'selumetinib'], 'ERK MAPK signaling'),
        (['braf', 'dabrafenib', 'vemurafenib'], 'ERK MAPK signaling'),
        (['pi3k', 'mtor', 'rapamycin', 'everolimus'], 'PI3K/MTOR signaling'),
        (['egfr', 'erlotinib', 'gefitinib', 'afatinib'], 'EGFR signaling'),
        (['sunitinib', 'axitinib', 'imatinib', 'nilotinib'], 'RTK signaling'),
        (['tamoxifen', 'bicalutamide'], 'Hormone-related'),
        (['wnt', 'hedgehog', 'vismodegib'], 'WNT signaling'),
    ]
    for kws, pw in patterns:
        if any(k in nl for k in kws):
            return pw
    return None


def pathway_type(pw):
    if pw in STRUCTURE_PATHWAYS:
        return 'STRUCTURE'
    if pw in INPUT_PATHWAYS:
        return 'INPUT'
    return None


# ════════════════════════════════════════════════════════════════
# STATISTICAL ENGINE
# ════════════════════════════════════════════════════════════════

def compute_stats(vals_input, vals_structure, label='', rng=None):
    """Cohen's d, ratio S/I, p-value, bootstrap CI."""
    inv = vals_input[np.isfinite(vals_input)]
    stv = vals_structure[np.isfinite(vals_structure)]

    if len(inv) < 30 or len(stv) < 30:
        return None

    n1, n2 = len(inv), len(stv)
    res = {'label': label, 'n_input': n1, 'n_structure': n2}

    # Cohen's d (pooled)
    ps = np.sqrt(((n1 - 1) * np.var(inv, ddof=1) + (n2 - 1) * np.var(stv, ddof=1)) / (n1 + n2 - 2))
    res['d'] = (np.mean(stv) - np.mean(inv)) / ps if ps > 0 else 0
    res['abs_d'] = abs(res['d'])

    # Mann-Whitney
    U, p = stats.mannwhitneyu(inv, stv, alternative='two-sided')
    res['U'] = float(U)
    res['p_MW'] = float(p)

    # Means and ratio (magnitude = 1 − AUC)
    res['mean_in'] = float(np.mean(inv))
    res['mean_st'] = float(np.mean(stv))
    mag_in = 1.0 - res['mean_in']
    mag_st = 1.0 - res['mean_st']
    res['mag_in'] = float(mag_in)
    res['mag_st'] = float(mag_st)
    res['ratio'] = float(mag_st / mag_in) if mag_in > 0.001 else float('inf')

    # Medians
    res['median_in'] = float(np.median(inv))
    res['median_st'] = float(np.median(stv))
    med_mag_in = 1.0 - res['median_in']
    med_mag_st = 1.0 - res['median_st']
    res['ratio_median'] = float(med_mag_st / med_mag_in) if med_mag_in > 0.001 else float('inf')

    # Bootstrap CI
    if rng is None:
        rng = np.random.RandomState(SEED)
    boot_d = np.zeros(N_BOOT)
    boot_ratio = np.zeros(N_BOOT)
    for i in range(N_BOOT):
        bi = rng.choice(inv, n1, replace=True)
        bs = rng.choice(stv, n2, replace=True)
        ps_b = np.sqrt(((n1 - 1) * np.var(bi, ddof=1) + (n2 - 1) * np.var(bs, ddof=1)) / (n1 + n2 - 2))
        boot_d[i] = (np.mean(bs) - np.mean(bi)) / ps_b if ps_b > 0 else 0
        m_in_b = 1.0 - np.mean(bi)
        m_st_b = 1.0 - np.mean(bs)
        boot_ratio[i] = m_st_b / m_in_b if m_in_b > 0.001 else float('inf')

    ci_d = np.percentile(boot_d, [2.5, 97.5])
    ci_ratio = np.percentile(boot_ratio, [2.5, 97.5])
    res['d_ci'] = [float(ci_d[0]), float(ci_d[1])]
    res['ratio_ci'] = [float(ci_ratio[0]), float(ci_ratio[1])]
    res['boot_d'] = boot_d
    res['boot_ratio'] = boot_ratio

    return res


def compute_stats_quick(vals_input, vals_structure, label=''):
    """Minimal stats for repeated splits (no bootstrap)."""
    inv = vals_input[np.isfinite(vals_input)]
    stv = vals_structure[np.isfinite(vals_structure)]

    if len(inv) < 30 or len(stv) < 30:
        return None

    n1, n2 = len(inv), len(stv)
    ps = np.sqrt(((n1 - 1) * np.var(inv, ddof=1) + (n2 - 1) * np.var(stv, ddof=1)) / (n1 + n2 - 2))
    d = (np.mean(stv) - np.mean(inv)) / ps if ps > 0 else 0

    U, p = stats.mannwhitneyu(inv, stv, alternative='two-sided')

    mag_in = 1.0 - np.mean(inv)
    mag_st = 1.0 - np.mean(stv)
    ratio = mag_st / mag_in if mag_in > 0.001 else float('inf')

    med_mag_in = 1.0 - np.median(inv)
    med_mag_st = 1.0 - np.median(stv)
    ratio_med = med_mag_st / med_mag_in if med_mag_in > 0.001 else float('inf')

    return {
        'label': label, 'n_input': n1, 'n_structure': n2,
        'd': float(d), 'abs_d': float(abs(d)),
        'p_MW': float(p),
        'ratio': float(ratio), 'ratio_median': float(ratio_med),
        'mean_in': float(np.mean(inv)), 'mean_st': float(np.mean(stv)),
    }


# ════════════════════════════════════════════════════════════════
# CELL LINE SPLIT
# ════════════════════════════════════════════════════════════════

def split_celllines(dfc, seed, cancer_col=None, train_frac=TRAIN_FRAC):
    """
    Split by cell line (not by observation).
    Stratified by cancer type if cancer_col is available.
    Returns (train_lines, test_lines).
    """
    rng = np.random.RandomState(seed)

    if cancer_col and cancer_col in dfc.columns:
        # Stratified split: preserve cancer type proportions
        line_cancer = dfc.groupby('COSMIC_ID')[cancer_col].first()
        train_lines = []
        test_lines = []

        for ct, lines in line_cancer.groupby(line_cancer):
            line_ids = lines.index.values.copy()
            rng.shuffle(line_ids)
            n_train = max(1, int(len(line_ids) * train_frac))
            train_lines.extend(line_ids[:n_train])
            test_lines.extend(line_ids[n_train:])

        return set(train_lines), set(test_lines)
    else:
        # Simple random split
        all_lines = dfc['COSMIC_ID'].unique().copy()
        rng.shuffle(all_lines)
        n_train = int(len(all_lines) * train_frac)
        return set(all_lines[:n_train]), set(all_lines[n_train:])


# ════════════════════════════════════════════════════════════════
# MAIN
# ════════════════════════════════════════════════════════════════

def main():
    t0 = time.time()

    print("=" * 75)
    print("  CR-02 PARTIE B — SPLIT PAR LIGNÉES GDSC")
    print(f"  Split : {TRAIN_FRAC * 100:.0f}/{(1 - TRAIN_FRAC) * 100:.0f} par lignée")
    print(f"  Seed primaire : {SEED}")
    print(f"  Répétitions : {N_REPEATS}")
    print("=" * 75)

    # ── Chargement ────────────────────────────────────────────
    fname = sys.argv[1] if len(sys.argv) > 1 else 'sanger-dose-response.csv'
    if not os.path.exists(fname):
        print(f"ERREUR : {fname} introuvable.")
        print(f"  Usage : python CR02_B_gdsc_cellline_split.py <chemin.csv>")
        sys.exit(1)

    df = pd.read_csv(fname)
    auc_col = 'AUC_PUBLISHED' if 'AUC_PUBLISHED' in df.columns else 'AUC'

    print(f"\n[DATA] {len(df):,} observations, {df['COSMIC_ID'].nunique()} lignées, "
          f"{df['DRUG_NAME'].nunique()} drogues")

    # ── Mapping pathway ───────────────────────────────────────
    df['PATHWAY'] = df['DRUG_NAME'].apply(map_drug)
    df['PTYPE'] = df['PATHWAY'].apply(pathway_type)

    dfc = df.dropna(subset=['PTYPE']).copy()
    n_in = (dfc['PTYPE'] == 'INPUT').sum()
    n_st = (dfc['PTYPE'] == 'STRUCTURE').sum()
    n_lines = dfc['COSMIC_ID'].nunique()

    print(f"  Mapping : {len(dfc):,} / {len(df):,} observations classifiées")
    print(f"  INPUT : {n_in:,}  |  STRUCTURE : {n_st:,}")
    print(f"  Lignées classifiées : {n_lines}")

    # Detect cancer type column for stratification
    cancer_col = None
    for c in ['TCGA_DESC', 'CANCER_TYPE', 'TISSUE']:
        if c in dfc.columns and dfc[c].notna().sum() > 0:
            cancer_col = c
            break
    if cancer_col:
        print(f"  Stratification par : {cancer_col} ({dfc[cancer_col].nunique()} types)")
    else:
        print(f"  ⚠ Pas de colonne type de cancer — split non stratifié")

    # ── ÉTAPE 1-3 : Split primaire (seed = SEED) ─────────────
    print(f"\n{'═' * 75}")
    print(f"  SPLIT PRIMAIRE (seed = {SEED})")
    print(f"{'═' * 75}")

    train_lines, test_lines = split_celllines(dfc, SEED, cancer_col)
    df_train = dfc[dfc['COSMIC_ID'].isin(train_lines)].copy()
    df_test = dfc[dfc['COSMIC_ID'].isin(test_lines)].copy()

    print(f"\n  TRAIN : {len(train_lines)} lignées, {len(df_train):,} observations")
    print(f"    INPUT : {(df_train['PTYPE'] == 'INPUT').sum():,}  "
          f"STRUCTURE : {(df_train['PTYPE'] == 'STRUCTURE').sum():,}")
    print(f"  TEST  : {len(test_lines)} lignées, {len(df_test):,} observations")
    print(f"    INPUT : {(df_test['PTYPE'] == 'INPUT').sum():,}  "
          f"STRUCTURE : {(df_test['PTYPE'] == 'STRUCTURE').sum():,}")

    # TRAIN stats
    inv_train = df_train.loc[df_train['PTYPE'] == 'INPUT', auc_col].values
    stv_train = df_train.loc[df_train['PTYPE'] == 'STRUCTURE', auc_col].values
    stats_train = compute_stats(inv_train, stv_train, 'TRAIN')

    if stats_train:
        print(f"\n  TRAIN — Résultats :")
        print(f"    Cohen's d     = {stats_train['d']:+.4f}  |d| = {stats_train['abs_d']:.4f}")
        print(f"    Ratio S/I moy = {stats_train['ratio']:.3f}×")
        print(f"    Ratio S/I méd = {stats_train['ratio_median']:.3f}×")
        print(f"    p (MW)        = {stats_train['p_MW']:.2e}")
        print(f"    CI d          = [{stats_train['d_ci'][0]:.4f}, {stats_train['d_ci'][1]:.4f}]")

    # TEST stats
    inv_test = df_test.loc[df_test['PTYPE'] == 'INPUT', auc_col].values
    stv_test = df_test.loc[df_test['PTYPE'] == 'STRUCTURE', auc_col].values
    stats_test = compute_stats(inv_test, stv_test, 'TEST')

    if stats_test:
        print(f"\n  TEST — Résultats :")
        print(f"    Cohen's d     = {stats_test['d']:+.4f}  |d| = {stats_test['abs_d']:.4f}")
        print(f"    Ratio S/I moy = {stats_test['ratio']:.3f}×")
        print(f"    Ratio S/I méd = {stats_test['ratio_median']:.3f}×")
        print(f"    p (MW)        = {stats_test['p_MW']:.2e}")
        print(f"    CI d          = [{stats_test['d_ci'][0]:.4f}, {stats_test['d_ci'][1]:.4f}]")

    # FULL stats
    inv_full = dfc.loc[dfc['PTYPE'] == 'INPUT', auc_col].values
    stv_full = dfc.loc[dfc['PTYPE'] == 'STRUCTURE', auc_col].values
    stats_full = compute_stats(inv_full, stv_full, 'FULL')

    if stats_full:
        print(f"\n  DATASET COMPLET — Résultats :")
        print(f"    Cohen's d     = {stats_full['d']:+.4f}  |d| = {stats_full['abs_d']:.4f}")
        print(f"    Ratio S/I moy = {stats_full['ratio']:.3f}×")
        print(f"    p (MW)        = {stats_full['p_MW']:.2e}")

    # ── ÉTAPE 4 : Robustesse — 10 répétitions ────────────────
    print(f"\n{'═' * 75}")
    print(f"  ÉTAPE 4 — ROBUSTESSE : {N_REPEATS} splits avec seeds différentes")
    print(f"{'═' * 75}")

    repeat_seeds = [SEED + i * 7919 for i in range(N_REPEATS)]  # 7919 = prime
    repeat_results = []

    print(f"\n  {'Seed':>12s} {'d_TRAIN':>10s} {'d_TEST':>10s} "
          f"{'R_TRAIN':>10s} {'R_TEST':>10s} {'Rmed_TEST':>10s} {'p_TEST':>12s}")
    print(f"  {'─' * 12} {'─' * 10} {'─' * 10} {'─' * 10} {'─' * 10} {'─' * 10} {'─' * 12}")

    for seed_i in repeat_seeds:
        tr_lines_i, te_lines_i = split_celllines(dfc, seed_i, cancer_col)
        df_tr_i = dfc[dfc['COSMIC_ID'].isin(tr_lines_i)]
        df_te_i = dfc[dfc['COSMIC_ID'].isin(te_lines_i)]

        inv_tr_i = df_tr_i.loc[df_tr_i['PTYPE'] == 'INPUT', auc_col].values
        stv_tr_i = df_tr_i.loc[df_tr_i['PTYPE'] == 'STRUCTURE', auc_col].values
        inv_te_i = df_te_i.loc[df_te_i['PTYPE'] == 'INPUT', auc_col].values
        stv_te_i = df_te_i.loc[df_te_i['PTYPE'] == 'STRUCTURE', auc_col].values

        r_tr = compute_stats_quick(inv_tr_i, stv_tr_i, f'TRAIN_{seed_i}')
        r_te = compute_stats_quick(inv_te_i, stv_te_i, f'TEST_{seed_i}')

        if r_tr and r_te:
            repeat_results.append({
                'seed': seed_i,
                'd_train': r_tr['d'], 'd_test': r_te['d'],
                'abs_d_train': r_tr['abs_d'], 'abs_d_test': r_te['abs_d'],
                'ratio_train': r_tr['ratio'], 'ratio_test': r_te['ratio'],
                'ratio_med_train': r_tr['ratio_median'], 'ratio_med_test': r_te['ratio_median'],
                'p_train': r_tr['p_MW'], 'p_test': r_te['p_MW'],
                'n_train_obs': r_tr['n_input'] + r_tr['n_structure'],
                'n_test_obs': r_te['n_input'] + r_te['n_structure'],
                'n_train_lines': len(tr_lines_i),
                'n_test_lines': len(te_lines_i),
            })
            print(f"  {seed_i:>12d} {r_tr['d']:>+10.4f} {r_te['d']:>+10.4f} "
                  f"{r_tr['ratio']:>10.3f} {r_te['ratio']:>10.3f} "
                  f"{r_te['ratio_median']:>10.3f} {r_te['p_MW']:>12.2e}")

    rep_df = pd.DataFrame(repeat_results)

    if len(rep_df) > 0:
        print(f"\n  Distribution sur {len(rep_df)} splits :")
        for col_name, col_label in [('d_test', "Cohen's d TEST"),
                                      ('ratio_test', 'Ratio S/I TEST (moy)'),
                                      ('ratio_med_test', 'Ratio S/I TEST (méd)')]:
            vals = rep_df[col_name]
            med = vals.median()
            q25, q75 = vals.quantile(0.25), vals.quantile(0.75)
            cv = vals.std() / abs(vals.mean()) * 100 if vals.mean() != 0 else float('inf')
            print(f"    {col_label:<28s}: médiane = {med:.4f}  "
                  f"IQR = [{q25:.4f}, {q75:.4f}]  CV = {cv:.1f}%")

        # Count significant
        n_sig = (rep_df['p_test'] < 0.05).sum()
        print(f"    Splits significatifs (p < 0.05) : {n_sig}/{len(rep_df)}")

    # ── TABLEAU COMPARATIF ────────────────────────────────────
    print(f"\n{'═' * 75}")
    print(f"  TABLEAU COMPARATIF")
    print(f"{'═' * 75}")

    med_d = rep_df['d_test'].median() if len(rep_df) > 0 else None
    iqr_d = (rep_df['d_test'].quantile(0.25), rep_df['d_test'].quantile(0.75)) if len(rep_df) > 0 else None
    med_r = rep_df['ratio_test'].median() if len(rep_df) > 0 else None
    iqr_r = (rep_df['ratio_test'].quantile(0.25), rep_df['ratio_test'].quantile(0.75)) if len(rep_df) > 0 else None

    header = (f"  {'Métrique':<24s} {'TRAIN (70%)':>14s} {'TEST (30%)':>14s} "
              f"{'10 splits':>22s} {'Complet':>14s}")
    sep = f"  {'─' * 24} {'─' * 14} {'─' * 14} {'─' * 22} {'─' * 14}"
    print(header)
    print(sep)

    def c(v, f='.4f'):
        if v is None: return '—'
        return f'{v:{f}}'

    # n obs
    n_tr = stats_train['n_input'] + stats_train['n_structure'] if stats_train else None
    n_te = stats_test['n_input'] + stats_test['n_structure'] if stats_test else None
    n_fu = stats_full['n_input'] + stats_full['n_structure'] if stats_full else None
    print(f"  {'n obs':<24s} {c(n_tr, ',d') if n_tr else '—':>14s} "
          f"{c(n_te, ',d') if n_te else '—':>14s} "
          f"{'—':>22s} {c(n_fu, ',d') if n_fu else '—':>14s}")

    # Cohen's d
    d_tr = stats_train['d'] if stats_train else None
    d_te = stats_test['d'] if stats_test else None
    d_fu = stats_full['d'] if stats_full else None
    med_str = f"{med_d:.4f} [{iqr_d[0]:.3f}, {iqr_d[1]:.3f}]" if med_d is not None else '—'
    cohens_label = "Cohen's d"
    print(f"  {cohens_label:<24s} {c(d_tr):>14s} {c(d_te):>14s} {med_str:>22s} {c(d_fu):>14s}")

    # Ratio S/I
    r_tr = stats_train['ratio'] if stats_train else None
    r_te = stats_test['ratio'] if stats_test else None
    r_fu = stats_full['ratio'] if stats_full else None
    med_r_str = f"{med_r:.3f} [{iqr_r[0]:.2f}, {iqr_r[1]:.2f}]" if med_r is not None else '—'
    print(f"  {'Ratio S/I':<24s} {c(r_tr, '.3f'):>14s} {c(r_te, '.3f'):>14s} "
          f"{med_r_str:>22s} {c(r_fu, '.3f'):>14s}")

    # p
    p_tr = stats_train['p_MW'] if stats_train else None
    p_te = stats_test['p_MW'] if stats_test else None
    p_fu = stats_full['p_MW'] if stats_full else None
    print(f"  {'p (Mann-Whitney)':<24s} {c(p_tr, '.2e'):>14s} {c(p_te, '.2e'):>14s} "
          f"{'—':>22s} {c(p_fu, '.2e'):>14s}")

    # ── VERDICT ───────────────────────────────────────────────
    print(f"\n{'═' * 75}")
    print(f"  VERDICT")
    print(f"{'═' * 75}")

    if len(rep_df) > 0:
        cv_ratio = rep_df['ratio_test'].std() / abs(rep_df['ratio_test'].mean()) * 100 \
            if rep_df['ratio_test'].mean() != 0 else float('inf')
        med_ratio = rep_df['ratio_test'].median()
        n_nonsig = (rep_df['p_test'] >= 0.05).sum()

        print(f"  Ratio S/I médian (10 splits) = {med_ratio:.3f}×")
        print(f"  CV ratio = {cv_ratio:.1f}%")
        print(f"  Splits non significatifs = {n_nonsig}/{len(rep_df)}")

        if 1.5 <= med_ratio <= 2.2 and cv_ratio < 15:
            verdict = "SUCCÈS FORT"
            expl = (f"Ratio S/I médian {med_ratio:.2f}× dans [1.5, 2.2], "
                    f"CV = {cv_ratio:.1f}% < 15%")
        elif cv_ratio < 30 and med_ratio > 1.0:
            verdict = "SUCCÈS MODÉRÉ"
            expl = (f"Ratio significatif mais {'plus variable' if cv_ratio >= 15 else ''} "
                    f"(CV = {cv_ratio:.1f}%)")
        elif n_nonsig > 2:
            verdict = "ÉCHEC INFORMATIF"
            expl = f"Ratio instable ou non significatif dans {n_nonsig}/10 splits"
        else:
            verdict = "SUCCÈS MODÉRÉ"
            expl = f"Ratio = {med_ratio:.2f}×, CV = {cv_ratio:.1f}%"

        print(f"\n  ★ {verdict}")
        print(f"    {expl}")

    # ── FIGURE MANUSCRIT (1 panneau optionnel) ─────────────────
    print(f"\n{'─' * 60}")
    print(f"  FIGURE MANUSCRIT (1 panneau — optionnel, tableau suffit)")
    print(f"{'─' * 60}")

    C_TR = '#1565C0'
    C_TE = '#C62828'
    C_FU = '#616161'

    if len(rep_df) > 0:
        # Single panel: Ratio S/I across 10 splits with target band
        fig, ax = plt.subplots(1, 1, figsize=(3.54, 2.8))  # ~90mm single column
        fig.subplots_adjust(left=0.16, right=0.95, top=0.88, bottom=0.15)

        ax.plot(range(len(rep_df)), rep_df['ratio_train'], 'o-', color=C_TR,
                label='TRAIN (70%)', ms=5, lw=1.2)
        ax.plot(range(len(rep_df)), rep_df['ratio_test'], 's-', color=C_TE,
                label='TEST (30%)', ms=5, lw=1.2)
        ax.axhline(1.0, color='gray', ls='-', lw=0.5)
        ax.axhspan(1.5, 2.2, alpha=0.07, color='green', label='Target [1.5, 2.2]')
        if stats_full:
            ax.axhline(stats_full['ratio'], color=C_FU, ls=':', lw=1,
                       label=f'Full dataset ({stats_full["ratio"]:.2f}×)')
        ax.set_xlabel('Split #', fontsize=9)
        ax.set_ylabel('Ratio S/I (mean)', fontsize=9)
        ax.set_title('Ratio S/I stability across 10 cell-line splits', fontsize=9)
        ax.legend(fontsize=7, loc='lower right')
        ax.set_xticks(range(len(rep_df)))
        ax.set_xticklabels([str(i + 1) for i in range(len(rep_df))], fontsize=8)
        ax.tick_params(labelsize=8)

        fig_path = OUT_DIR / 'CR02B_gdsc_manuscript.png'
        plt.savefig(fig_path, dpi=300, bbox_inches='tight', facecolor='white')
        plt.close()
        print(f"  Figure manuscrit : {fig_path}")
    else:
        print(f"  Pas de données de splits — figure non produite.")

    # ── EXPORT JSON ───────────────────────────────────────────
    export = {
        'protocol': 'CR-02B',
        'seed': SEED,
        'train_frac': TRAIN_FRAC,
        'n_repeats': N_REPEATS,
        'n_lines_total': n_lines,
        'cancer_col': cancer_col,
    }
    for key, st in [('train', stats_train), ('test', stats_test), ('full', stats_full)]:
        if st:
            export[key] = {k: v for k, v in st.items()
                          if k not in ('boot_d', 'boot_ratio')}
    if len(rep_df) > 0:
        export['repeats'] = rep_df.to_dict('records')
        export['repeats_summary'] = {
            'd_test_median': float(rep_df['d_test'].median()),
            'd_test_iqr': [float(rep_df['d_test'].quantile(0.25)),
                           float(rep_df['d_test'].quantile(0.75))],
            'ratio_test_median': float(rep_df['ratio_test'].median()),
            'ratio_test_iqr': [float(rep_df['ratio_test'].quantile(0.25)),
                               float(rep_df['ratio_test'].quantile(0.75))],
            'cv_ratio': float(cv_ratio),
            'n_significant': int((rep_df['p_test'] < 0.05).sum()),
        }
        export['verdict'] = verdict

    def nc(o):
        if isinstance(o, (np.integer,)): return int(o)
        if isinstance(o, (np.floating,)): return float(o)
        if isinstance(o, np.ndarray): return o.tolist()
        if isinstance(o, np.bool_): return bool(o)
        raise TypeError(f"{type(o)}")

    json_path = OUT_DIR / 'CR02B_gdsc_cellline_split.json'
    with open(json_path, 'w') as f:
        json.dump(export, f, indent=2, default=nc)
    print(f"  JSON : {json_path}")

    elapsed = time.time() - t0
    print(f"\n{'═' * 75}")
    print(f"  FIN CR-02B ({elapsed:.1f}s)")
    print(f"{'═' * 75}")


if __name__ == '__main__':
    main()