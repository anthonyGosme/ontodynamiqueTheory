#!/usr/bin/env python3
"""
=============================================================================
R-XVII ASYMMETRY TEST v2 — PATHWAY-ONLY CLASSIFICATION
=============================================================================
Correction méthodologique: la v1 utilisait un filtre IC50 > MAX_CONC pour
définir INPUT, ce qui sélectionnait par construction les paires résistantes.

Cette v2 fait TROIS analyses distinctes:

  (A) PATHWAY-ONLY: classification uniquement sur la cible de la drogue
      STRUCTURE = drogue ciblant maintenance (DNA repair, proteasome, etc.)
      INPUT     = drogue ciblant signalisation (MAPK, PI3K, RTK, etc.)
      → Pas de filtre sur la dose ni sur la réponse. Le plus propre.

  (B) DOSE-MATCHED: même classification pathway, mais restreint aux
      observations dans la même fenêtre de concentration
      → Contrôle le confondant "dose"

  (C) INTRA-PATHWAY: pour chaque pathway INPUT, compare sub-létal
      (IC50 > MAX_CONC) vs supra-létal (IC50 ≤ MAX_CONC)
      → Teste l'asymétrie dose-dépendante DANS une même classe de drogue

Usage:
  python3 rXVII_v2_pathway_only.py
  (sanger-dose-response.csv doit être dans le même dossier)
=============================================================================
"""

import numpy as np
import pandas as pd
from scipy import stats
from scipy.optimize import curve_fit
import matplotlib

matplotlib.use('Agg')
import matplotlib.pyplot as plt
import os, sys, time
import warnings

warnings.filterwarnings('ignore')

# ============================================================================
# DRUG → PATHWAY MAPPING (identique à v1)
# ============================================================================

DRUG_PATHWAY = {}

# STRUCTURE pathways
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
    """Return 'STRUCTURE', 'INPUT', or None."""
    if pw in STRUCTURE_PATHWAYS:
        return 'STRUCTURE'
    if pw in INPUT_PATHWAYS:
        return 'INPUT'
    return None


# ============================================================================
# STATISTICAL ENGINE
# ============================================================================

def run_test(vals_input, vals_structure, label='', n_perm=10000):
    """Full battery on two arrays. Returns dict or None."""
    inv = vals_input[np.isfinite(vals_input)]
    stv = vals_structure[np.isfinite(vals_structure)]

    if len(inv) < 30 or len(stv) < 30:
        print(f"  ⚠ {label}: n trop faible (INPUT={len(inv)}, STRUCT={len(stv)})")
        return None

    res = {'label': label, 'n_input': len(inv), 'n_structure': len(stv)}

    # 1. Mann-Whitney U + Cohen's d
    U, p = stats.mannwhitneyu(inv, stv, alternative='two-sided')
    n1, n2 = len(inv), len(stv)
    ps = np.sqrt(((n1 - 1) * np.var(inv, ddof=1) + (n2 - 1) * np.var(stv, ddof=1)) / (n1 + n2 - 2))
    res['U'] = U
    res['p_MW'] = p
    res['d'] = (np.mean(stv) - np.mean(inv)) / ps if ps > 0 else 0
    res['abs_d'] = abs(res['d'])

    # 2. Permutation (vectorized, subsampled if needed)
    obs = np.mean(stv) - np.mean(inv)
    combined = np.concatenate([inv, stv])
    MAX_N = 50000
    rng = np.random.RandomState(42)
    if len(combined) > MAX_N:
        idx_i = rng.choice(len(inv), min(len(inv), MAX_N // 2), replace=False)
        idx_s = rng.choice(len(stv), min(len(stv), MAX_N // 2), replace=False)
        comb_sub = np.concatenate([inv[idx_i], stv[idx_s]])
        n_in_sub = len(idx_i)
    else:
        comb_sub = combined.copy()
        n_in_sub = n1

    perms = np.empty(n_perm)
    for i in range(n_perm):
        rng.shuffle(comb_sub)
        perms[i] = np.mean(comb_sub[n_in_sub:]) - np.mean(comb_sub[:n_in_sub])

    res['obs_diff'] = obs
    res['p_perm'] = float(np.mean(np.abs(perms) >= np.abs(obs)))
    res['perm_diffs'] = perms

    # 3. Means and ratio
    res['mean_in'] = np.mean(inv)
    res['mean_st'] = np.mean(stv)
    mag_in = 1.0 - res['mean_in']
    mag_st = 1.0 - res['mean_st']
    res['mag_in'] = mag_in
    res['mag_st'] = mag_st
    res['ratio'] = mag_st / mag_in if mag_in > 0.001 else np.inf

    # 4. Medians (more robust)
    res['median_in'] = np.median(inv)
    res['median_st'] = np.median(stv)
    med_mag_in = 1.0 - res['median_in']
    med_mag_st = 1.0 - res['median_st']
    res['ratio_median'] = med_mag_st / med_mag_in if med_mag_in > 0.001 else np.inf

    return res


def print_result(res):
    if not res:
        return
    d = res['abs_d']
    eff = "négligeable" if d < 0.2 else ("faible" if d < 0.5 else ("moyen" if d < 0.8 else "FORT"))
    print(f"\n  N: INPUT={res['n_input']:,}  STRUCTURE={res['n_structure']:,}")
    print(f"  Mann-Whitney p = {res['p_MW']:.2e}")
    print(f"  Cohen's d = {res['d']:+.4f}  |d| = {res['abs_d']:.4f}  ({eff})")
    print(f"  Permutation p  = {res['p_perm']:.4f}")
    print(f"  AUC moyen:   INPUT={res['mean_in']:.4f}  STRUCT={res['mean_st']:.4f}")
    print(f"  AUC médian:  INPUT={res['median_in']:.4f}  STRUCT={res['median_st']:.4f}")
    print(f"  Magnitude (1−AUC):  INPUT={res['mag_in']:.4f}  STRUCT={res['mag_st']:.4f}")
    print(f"  ★ Ratio (moyennes)  = {res['ratio']:.3f}×")
    print(f"  ★ Ratio (médianes)  = {res['ratio_median']:.3f}×")
    print(f"    (cible trans-domaniale R-XVII ≈ 1.8×)")


# ============================================================================
# MAIN
# ============================================================================

def main():
    t0 = time.time()

    # --- Load ---
    fname = 'sanger-dose-response.csv'
    if not os.path.exists(fname):
        print(f"ERREUR: {fname} introuvable. Place-le dans le même dossier.")
        sys.exit(1)

    df = pd.read_csv(fname)
    auc_col = 'AUC_PUBLISHED' if 'AUC_PUBLISHED' in df.columns else 'AUC'
    ic50_col = 'IC50_PUBLISHED' if 'IC50_PUBLISHED' in df.columns else 'LN_IC50'

    print("=" * 75)
    print("  R-XVII v2 — PATHWAY-ONLY CLASSIFICATION (sans filtre dose)")
    print("=" * 75)
    print(f"  {len(df):,} observations, {df['COSMIC_ID'].nunique()} lignées, "
          f"{df['DRUG_NAME'].nunique()} drogues")

    # --- Map ---
    df['PATHWAY'] = df['DRUG_NAME'].apply(map_drug)
    df['PTYPE'] = df['PATHWAY'].apply(pathway_type)

    mapped = df['PTYPE'].notna().sum()
    print(f"  Mapping: {mapped:,} / {len(df):,} ({100 * mapped / len(df):.1f}%)")

    dfc = df.dropna(subset=['PTYPE']).copy()
    n_in = (dfc['PTYPE'] == 'INPUT').sum()
    n_st = (dfc['PTYPE'] == 'STRUCTURE').sum()
    print(f"  INPUT: {n_in:,}  |  STRUCTURE: {n_st:,}")

    # ==================================================================
    # (A) PATHWAY-ONLY — le test le plus propre
    # ==================================================================
    print(f"\n{'=' * 75}")
    print("  (A) PATHWAY-ONLY: toute drogue maintenance vs toute drogue signalisation")
    print("      Classification purement sur le mécanisme, aucun filtre dose/réponse")
    print(f"{'=' * 75}")

    inv_a = dfc.loc[dfc['PTYPE'] == 'INPUT', auc_col].values
    stv_a = dfc.loc[dfc['PTYPE'] == 'STRUCTURE', auc_col].values
    res_a = run_test(inv_a, stv_a, 'Pathway-only (global)')
    print_result(res_a)

    # GDSC2 only
    dfc2 = dfc[dfc['DATASET'] == 'GDSC2']
    inv_a2 = dfc2.loc[dfc2['PTYPE'] == 'INPUT', auc_col].values
    stv_a2 = dfc2.loc[dfc2['PTYPE'] == 'STRUCTURE', auc_col].values
    res_a2 = run_test(inv_a2, stv_a2, 'Pathway-only (GDSC2)', n_perm=5000)
    print(f"\n  --- GDSC2 seul ---")
    print_result(res_a2)

    # ==================================================================
    # (B) DOSE-MATCHED: même pathway classification, fenêtre de conc comparable
    # ==================================================================
    print(f"\n{'=' * 75}")
    print("  (B) DOSE-MATCHED: même classification, fenêtre de concentration comparable")
    print("      Restreint aux observations où MAX_CONC est dans le même intervalle")
    print(f"{'=' * 75}")

    # Find overlapping concentration range
    if 'MAX_CONC' in dfc.columns:
        q25 = dfc['MAX_CONC'].quantile(0.25)
        q75 = dfc['MAX_CONC'].quantile(0.75)
        dfc_dm = dfc[(dfc['MAX_CONC'] >= q25) & (dfc['MAX_CONC'] <= q75)]
        print(f"  Fenêtre MAX_CONC: [{q25:.2f}, {q75:.2f}] µM")
        print(f"  Observations retenues: {len(dfc_dm):,} / {len(dfc):,}")

        inv_b = dfc_dm.loc[dfc_dm['PTYPE'] == 'INPUT', auc_col].values
        stv_b = dfc_dm.loc[dfc_dm['PTYPE'] == 'STRUCTURE', auc_col].values
        res_b = run_test(inv_b, stv_b, 'Dose-matched (IQR)', n_perm=5000)
        print_result(res_b)
    else:
        res_b = None
        print("  ⚠ Colonne MAX_CONC absente")

    # ==================================================================
    # (C) INTRA-PATHWAY: sub-létal vs supra-létal DANS les drogues INPUT
    # ==================================================================
    print(f"\n{'=' * 75}")
    print("  (C) INTRA-PATHWAY: sub-létal vs supra-létal dans chaque pathway INPUT")
    print("      Même drogue, même pathway — seule la dose change")
    print(f"{'=' * 75}")

    dfc_input = dfc[dfc['PTYPE'] == 'INPUT'].copy()
    dfc_input['DOSE_REGIME'] = np.where(
        dfc_input[ic50_col] > dfc_input['MAX_CONC'], 'SUB_LETHAL', 'SUPRA_LETHAL'
    )

    n_sub = (dfc_input['DOSE_REGIME'] == 'SUB_LETHAL').sum()
    n_sup = (dfc_input['DOSE_REGIME'] == 'SUPRA_LETHAL').sum()
    print(f"  Input drugs: SUB-létal={n_sub:,}  SUPRA-létal={n_sup:,}")

    inv_c = dfc_input.loc[dfc_input['DOSE_REGIME'] == 'SUB_LETHAL', auc_col].values
    stv_c = dfc_input.loc[dfc_input['DOSE_REGIME'] == 'SUPRA_LETHAL', auc_col].values
    res_c = run_test(inv_c, stv_c, 'Intra-input: sub vs supra', n_perm=5000)
    print_result(res_c)

    # Per pathway
    print(f"\n  --- Par pathway ---")
    intra_results = []
    for pw in sorted(INPUT_PATHWAYS):
        sub = dfc_input[dfc_input['PATHWAY'] == pw]
        if len(sub) < 100:
            continue
        inv_pw = sub.loc[sub['DOSE_REGIME'] == 'SUB_LETHAL', auc_col].values
        stv_pw = sub.loc[sub['DOSE_REGIME'] == 'SUPRA_LETHAL', auc_col].values
        r = run_test(inv_pw, stv_pw, f'{pw}', n_perm=2000)
        if r:
            intra_results.append(r)
            sig = '***' if r['p_MW'] < 0.001 else ('**' if r['p_MW'] < 0.01 else ('*' if r['p_MW'] < 0.05 else 'ns'))
            print(f"    {pw:<28s}: |d|={r['abs_d']:.3f}, p={r['p_MW']:.2e} {sig}, "
                  f"ratio={r['ratio']:.2f}×, ratio_med={r['ratio_median']:.2f}×")

    # ==================================================================
    # (D) ROBUSTESSE: par type de cancer (pathway-only)
    # ==================================================================
    print(f"\n{'=' * 75}")
    print("  (D) ROBUSTESSE: par type de cancer (pathway-only)")
    print(f"{'=' * 75}")

    # Detect cancer type column
    cancer_col = None
    for c in ['TCGA_DESC', 'CANCER_TYPE', 'TISSUE']:
        if c in dfc.columns:
            cancer_col = c
            break

    cancer_results = []
    if cancer_col:
        for ct, grp in dfc.groupby(cancer_col):
            if len(grp) < 200:
                continue
            inv_ct = grp.loc[grp['PTYPE'] == 'INPUT', auc_col].values
            stv_ct = grp.loc[grp['PTYPE'] == 'STRUCTURE', auc_col].values
            r = run_test(inv_ct, stv_ct, f'{ct}', n_perm=2000)
            if r:
                cancer_results.append(r)
                sig = '***' if r['p_MW'] < 0.001 else (
                    '**' if r['p_MW'] < 0.01 else ('*' if r['p_MW'] < 0.05 else 'ns'))
                print(f"  {str(ct):<25s}: |d|={r['abs_d']:.3f}, p={r['p_MW']:.2e} {sig}, "
                      f"ratio={r['ratio']:.2f}×, ratio_med={r['ratio_median']:.2f}×")
    else:
        # If no cancer type column, check what's available
        print(f"  Colonnes disponibles: {list(dfc.columns)}")
        print("  ⚠ Pas de colonne type de cancer trouvée")

    # ==================================================================
    # VISUALIZATIONS
    # ==================================================================
    print(f"\n{'=' * 75}")
    print("  FIGURES")
    print(f"{'=' * 75}")

    fig, axes = plt.subplots(2, 3, figsize=(20, 13))
    fig.suptitle('R-XVII v2 — Pathway-Only Classification (REAL GDSC)',
                 fontsize=15, fontweight='bold', y=0.98)

    # 1. Distribution (pathway-only)
    ax = axes[0, 0]
    ax.hist(inv_a[np.isfinite(inv_a)], bins=80, alpha=0.55, density=True,
            color='#2196F3', label=f'INPUT (n={len(inv_a):,})')
    ax.hist(stv_a[np.isfinite(stv_a)], bins=80, alpha=0.55, density=True,
            color='#E53935', label=f'STRUCTURE (n={len(stv_a):,})')
    if res_a:
        ax.axvline(res_a['mean_in'], color='#0D47A1', ls='--', lw=2)
        ax.axvline(res_a['mean_st'], color='#B71C1C', ls='--', lw=2)
    ax.set_xlabel('AUC')
    ax.set_ylabel('Densité')
    ax.set_title('(A) Pathway-only: distribution AUC')
    ax.legend(fontsize=8)

    # 2. Permutation (pathway-only)
    ax = axes[0, 1]
    if res_a and 'perm_diffs' in res_a:
        ax.hist(res_a['perm_diffs'], bins=80, alpha=0.7, color='#9E9E9E', density=True)
        ax.axvline(res_a['obs_diff'], color='#E53935', lw=2.5,
                   label=f"Observé: {res_a['obs_diff']:+.4f}")
        ax.set_title(f"(A) Permutation (p={res_a['p_perm']:.4f})")
        ax.set_xlabel('Δ(Struct − Input) sous H₀')
        ax.legend()

    # 3. Comparison of 3 analyses
    ax = axes[0, 2]
    labels_3 = []
    ratios_3 = []
    ratios_med_3 = []
    ds_3 = []
    for r, lbl in [(res_a, 'Pathway\n(all)'), (res_b, 'Dose-\nmatched'), (res_c, 'Intra-\npathway')]:
        if r:
            labels_3.append(lbl)
            ratios_3.append(r['ratio'])
            ratios_med_3.append(r['ratio_median'])
            ds_3.append(r['abs_d'])

    x = np.arange(len(labels_3))
    w = 0.35
    ax.bar(x - w / 2, ratios_3, w, alpha=0.7, color='#E53935', label='Ratio (moy)')
    ax.bar(x + w / 2, ratios_med_3, w, alpha=0.7, color='#FF8A65', label='Ratio (méd)')
    ax.axhline(1.8, color='black', ls=':', lw=1.5, label='Cible 1.8×')
    ax.axhline(1.0, color='gray', ls='-', lw=0.5)
    ax.set_xticks(x)
    ax.set_xticklabels(labels_3)
    ax.set_ylabel('Ratio Magnitude S/I')
    ax.set_title('Comparaison des 3 analyses')
    ax.legend(fontsize=8)
    # Add d values as text
    for i, d in enumerate(ds_3):
        ax.text(i, max(ratios_3[i], ratios_med_3[i]) + 0.1, f'|d|={d:.2f}',
                ha='center', fontsize=9)

    # 4. By pathway (pathway-only)
    ax = axes[1, 0]
    pw_data = []
    for pw, grp in dfc.groupby('PATHWAY'):
        if pw and len(grp) > 200:
            pt = pathway_type(pw)
            if pt:
                pw_data.append({
                    'pathway': str(pw)[:22],
                    'mean_AUC': grp[auc_col].mean(),
                    'type': pt
                })
    if pw_data:
        pw_df = pd.DataFrame(pw_data).sort_values('mean_AUC')
        colors = ['#E53935' if t == 'STRUCTURE' else '#2196F3' for t in pw_df['type']]
        ax.barh(pw_df['pathway'], pw_df['mean_AUC'], color=colors, alpha=0.7)
        m_in = pw_df[pw_df['type'] == 'INPUT']['mean_AUC'].mean()
        m_st = pw_df[pw_df['type'] == 'STRUCTURE']['mean_AUC'].mean()
        ax.axvline(m_in, color='#0D47A1', ls='--', lw=1.5, label=f'μ INPUT={m_in:.3f}')
        ax.axvline(m_st, color='#B71C1C', ls='--', lw=1.5, label=f'μ STRUCT={m_st:.3f}')
        ax.set_xlabel('Mean AUC')
        ax.set_title('AUC moyen par pathway\n(bleu=input, rouge=structure)')
        ax.legend(fontsize=8)

    # 5. Intra-pathway per pathway
    ax = axes[1, 1]
    if intra_results:
        pw_labels = [r['label'][:22] for r in intra_results]
        pw_ratios = [r['ratio'] for r in intra_results]
        pw_ratios_m = [r['ratio_median'] for r in intra_results]
        x = np.arange(len(pw_labels))
        ax.barh(x - 0.15, pw_ratios, 0.3, alpha=0.7, color='#7B1FA2', label='Ratio (moy)')
        ax.barh(x + 0.15, pw_ratios_m, 0.3, alpha=0.7, color='#CE93D8', label='Ratio (méd)')
        ax.axvline(1.8, color='black', ls=':', lw=1.5, label='Cible 1.8×')
        ax.axvline(1.0, color='gray', ls='-', lw=0.5)
        ax.set_yticks(x)
        ax.set_yticklabels(pw_labels)
        ax.set_xlabel('Ratio Magnitude S/I')
        ax.set_title('(C) Intra-pathway: sub vs supra')
        ax.legend(fontsize=8)

    # 6. Cancer types
    ax = axes[1, 2]
    if cancer_results:
        ct_labels = [r['label'][:20] for r in cancer_results]
        ct_ratios = [r['ratio'] for r in cancer_results]
        ct_d = [r['abs_d'] for r in cancer_results]
        colors = ['#E53935' if d > 0.5 else '#9E9E9E' for d in ct_d]
        ax.barh(ct_labels, ct_ratios, color=colors, alpha=0.7)
        ax.axvline(1.8, color='black', ls=':', lw=1.5, label='Cible 1.8×')
        ax.set_xlabel('Ratio Magnitude S/I')
        ax.set_title('(D) Par type de cancer (pathway-only)')
        ax.legend(fontsize=8)

    plt.tight_layout()
    plt.savefig('rXVII_v2_results.png', dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  → rXVII_v2_results.png")

    # ==================================================================
    # SUMMARY
    # ==================================================================
    print(f"\n{'=' * 75}")
    print("  TABLE RÉCAPITULATIVE")
    print(f"{'=' * 75}")
    h = f"  {'Analyse':<40s} {'n_in':>7s} {'n_st':>8s} {'|d|':>6s} {'p(MW)':>11s} {'R(moy)':>7s} {'R(méd)':>7s}"
    print(h)
    print(f"  {'-' * 40} {'-' * 7} {'-' * 8} {'-' * 6} {'-' * 11} {'-' * 7} {'-' * 7}")
    for r in [res_a, res_a2, res_b, res_c]:
        if r:
            print(f"  {r['label']:<40s} {r['n_input']:>7,d} {r['n_structure']:>8,d} "
                  f"{r['abs_d']:>6.3f} {r['p_MW']:>11.2e} "
                  f"{r['ratio']:>6.2f}× {r['ratio_median']:>6.2f}×")

    # ==================================================================
    # TRANS-DOMAIN COMPARISON
    # ==================================================================
    print(f"\n{'=' * 75}")
    print("  COMPARAISON TRANS-DOMANIALE")
    print(f"{'=' * 75}")
    print(f"  {'Domaine':<30s} {'|d|':>6s} {'Ratio S/I':>10s} {'p':>12s}")
    print(f"  {'-' * 30} {'-' * 6} {'-' * 10} {'-' * 12}")
    print(f"  {'Microbiome (MDSINE2, dysb.)':<30s} {'1.16':>6s} {'1.86×':>10s} {'0.0006':>12s}")
    print(f"  {'Récifs (GCBD, n=34k)':<30s} {'0.39':>6s} {'1.80×':>10s} {'1.96e-48':>12s}")
    if res_a:
        print(f"  {'Cancer GDSC (pathway-only)':<30s} {res_a['abs_d']:>6.2f} "
              f"{res_a['ratio']:>9.2f}× {res_a['p_MW']:>12.2e}")
        print(f"  {'Cancer GDSC (ratio médian)':<30s} {'':>6s} "
              f"{res_a['ratio_median']:>9.2f}×")
    if res_b:
        print(f"  {'Cancer GDSC (dose-matched)':<30s} {res_b['abs_d']:>6.2f} "
              f"{res_b['ratio']:>9.2f}× {res_b['p_MW']:>12.2e}")
    if res_c:
        print(f"  {'Cancer GDSC (intra-pathway)':<30s} {res_c['abs_d']:>6.2f} "
              f"{res_c['ratio']:>9.2f}× {res_c['p_MW']:>12.2e}")

    print(f"\n  Note: le ratio 'cible' de 1.8× vient du microbiome (1.86×) et des")
    print(f"  récifs (1.80×). Si le ratio GDSC est supérieur, trois hypothèses:")
    print(f"  (1) Biais résiduel de dose dans la v1 — corrigé par pathway-only")
    print(f"  (2) Spécificité du substrat: les cellules cancéreuses ont une")
    print(f"      machinerie de maintenance sous tension → ratio amplifié (R-XVII)")
    print(f"  (3) Le 1.8× n'est pas un invariant universel mais un ordre de grandeur")

    elapsed = time.time() - t0
    print(f"\n  Temps: {elapsed:.1f}s")

    # Export
    all_r = []
    for r in [res_a, res_a2, res_b, res_c] + intra_results + cancer_results:
        if r:
            row = {k: v for k, v in r.items() if k != 'perm_diffs'}
            all_r.append(row)
    pd.DataFrame(all_r).to_csv('rXVII_v2_results.csv', index=False)
    print(f"  → rXVII_v2_results.csv")


if __name__ == '__main__':
    main()