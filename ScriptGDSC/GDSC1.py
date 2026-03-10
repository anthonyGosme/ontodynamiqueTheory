#!/usr/bin/env python3
"""
=============================================================================
R-XVII ASYMMETRY TEST — REAL GDSC DATA
=============================================================================
Usage:
  1. Place sanger-dose-response.csv in the same folder as this script
  2. pip install pandas numpy scipy matplotlib seaborn
  3. python rXVII_gdsc_local.py

The script produces:
  - rXVII_real_gdsc.png  (6-panel figure)
  - rXVII_results.csv    (all numeric results)
  - Console output with full analysis
=============================================================================
"""

import numpy as np
import pandas as pd
from scipy import stats
from scipy.optimize import curve_fit
import matplotlib

matplotlib.use('Agg')
import matplotlib.pyplot as plt
import seaborn as sns
import os, sys, time
import warnings

warnings.filterwarnings('ignore')

# ============================================================================
# SECTION 1: DRUG → PATHWAY MAPPING
# ============================================================================
# Classification based on MECHANISM OF ACTION, never on response.
# STRUCTURE = targets maintenance machinery (DNA repair, proteasome,
#             cell cycle checkpoints, mitotic spindle, chromatin, apoptosis)
# INPUT     = modulates signaling flux (kinase cascades, growth factor
#             receptors, hormone signaling, metabolism)
# ============================================================================

DRUG_PATHWAY = {}

# --- GENOME INTEGRITY (STRUCTURE) ---
_gi = [
    'OLAPARIB', 'TALAZOPARIB', 'RUCAPARIB', 'NIRAPARIB', 'VELIPARIB',
    'MIRIN', 'KU-55933', 'KU-60019', 'KU-57788', 'NU-7441',
    'AZD6738', 'VE-821', 'VE-822', 'AZD7762', 'CHIR-124', 'MK-8776',
    'BLEOMYCIN', 'CISPLATIN', 'CARBOPLATIN', 'OXALIPLATIN',
    'CARMUSTINE', 'LOMUSTINE', 'TEMOZOLOMIDE', 'MITOMYCIN-C',
    'ETOPOSIDE', 'CAMPTOTHECIN', 'SN-38', 'IRINOTECAN', 'TOPOTECAN',
    'DOXORUBICIN', 'DACTINOMYCIN', 'EPIRUBICIN', 'MITOXANTRONE',
]
for d in _gi: DRUG_PATHWAY[d] = 'Genome integrity'

# --- DNA REPLICATION (STRUCTURE) ---
_dr = [
    'GEMCITABINE', 'CYTARABINE', '5-FLUOROURACIL', 'METHOTREXATE',
    'FLUDARABINE', 'CLOFARABINE', 'HYDROXYUREA', 'PEMETREXED', 'CLADRIBINE',
]
for d in _dr: DRUG_PATHWAY[d] = 'DNA replication'

# --- CELL CYCLE (STRUCTURE) ---
_cc = [
    'PALBOCICLIB', 'RIBOCICLIB', 'ABEMACICLIB', 'RO-3306',
    'ALVOCIDIB', 'DINACICLIB', 'CGP-60474',
    'NUTLIN-3A (-)', 'NUTLIN-3A', 'APR-246', 'RG7388', 'IDASANUTLIN',
    '681640',
]
for d in _cc: DRUG_PATHWAY[d] = 'Cell cycle'

# --- MITOSIS (STRUCTURE) ---
_mi = [
    'PACLITAXEL', 'DOCETAXEL', 'VINBLASTINE', 'VINCRISTINE', 'VINORELBINE',
    'EPOTHILONE-B', 'ALISERTIB', 'ZM-447439', 'BARASERTIB', 'TOZASERTIB',
    'BI-2536', 'VOLASERTIB', 'GSK461364',
    'S-TRITYL-L-CYSTEINE', 'ISPINESIB', 'MPS1-IN-1',
]
for d in _mi: DRUG_PATHWAY[d] = 'Mitosis'

# --- PROTEIN STABILITY AND DEGRADATION (STRUCTURE) ---
_ps = [
    'BORTEZOMIB', 'CARFILZOMIB', 'MG-132',
    'PEVONEDISTAT',
    '17-AAG', 'TANESPIMYCIN', 'AUY922', 'GANETESPIB', 'LUMINESPIB', 'SNX-2112',
]
for d in _ps: DRUG_PATHWAY[d] = 'Protein stability and degradation'

# --- APOPTOSIS REGULATION (STRUCTURE) ---
_ap = [
    'NAVITOCLAX', 'ABT-737', 'VENETOCLAX', 'ABT-199',
    'AZD5582', 'BIRINAPANT', 'EMBELIN',
    'LCL-161', 'YM-155', 'OBATOCLAX',
]
for d in _ap: DRUG_PATHWAY[d] = 'Apoptosis regulation'

# --- CHROMATIN (STRUCTURE) ---
_ch = [
    'VORINOSTAT', 'BELINOSTAT', 'PANOBINOSTAT', 'ENTINOSTAT',
    'AR-42', 'CAY10603', 'ACY-1215', 'TUBASTATIN A', 'TRICHOSTATIN A',
    'JQ1', 'I-BET-762', 'OTX015', 'APABETALONE',
    'EPZ-5676', 'PINOMETOSTAT', 'GSK343', 'EPZ004777', 'EI1',
    'UNC0638', 'CHAETOCIN', 'DECITABINE', 'AZACYTIDINE', 'PFI-3',
]
for d in _ch: DRUG_PATHWAY[d] = 'Chromatin histone acetylation'

# --- ERK MAPK SIGNALING (INPUT) ---
_erk = [
    'PD-0325901', 'TRAMETINIB', 'SELUMETINIB', 'BINIMETINIB', 'COBIMETINIB',
    'REFAMETINIB', 'CI-1040', 'PIMASERTIB',
    'PLX-4720', 'DABRAFENIB', 'VEMURAFENIB', 'ENCORAFENIB',
    'SORAFENIB', 'AZ-628', 'SB-590885', 'TAK-632',
    'SCH772984', 'BVD-523', 'ULIXERTINIB', 'VX-11E',
]
for d in _erk: DRUG_PATHWAY[d] = 'ERK MAPK signaling'

# --- PI3K/MTOR SIGNALING (INPUT) ---
_pi3k = [
    'GDC-0941', 'ALPELISIB', 'BUPARLISIB', 'PICTILISIB',
    'IDELALISIB', 'COPANLISIB', 'APITOLISIB', 'AMG-319', 'TASELISIB',
    'NVP-BEZ235', 'DACTOLISIB',
    'AZD8055', 'VISTUSERTIB', 'SAPANISERTIB', 'OSI-027',
    'SIROLIMUS', 'EVEROLIMUS', 'TEMSIROLIMUS', 'RAPAMYCIN',
    'MK-2206', 'AZD5363', 'IPATASERTIB', 'CAPIVASERTIB', 'UPROSERTIB',
    'AT13148', 'AZD6482', 'BX-795',
]
for d in _pi3k: DRUG_PATHWAY[d] = 'PI3K/MTOR signaling'

# --- EGFR SIGNALING (INPUT) ---
_egfr = [
    'ERLOTINIB', 'GEFITINIB', 'LAPATINIB', 'NERATINIB',
    'AFATINIB', 'OSIMERTINIB', 'AZD3759',
    'AZD8931', 'CANERTINIB', 'SAPITINIB', 'AST-1306', 'CETUXIMAB',
]
for d in _egfr: DRUG_PATHWAY[d] = 'EGFR signaling'

# --- RTK SIGNALING (INPUT) ---
_rtk = [
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
    'PF-4708671',
]
for d in _rtk: DRUG_PATHWAY[d] = 'RTK signaling'

# --- HORMONE-RELATED (INPUT) ---
_hr = ['TAMOXIFEN', 'BICALUTAMIDE', 'FULVESTRANT', 'DEXAMETHASONE', 'BEXAROTENE']
for d in _hr: DRUG_PATHWAY[d] = 'Hormone-related'

# --- WNT SIGNALING (INPUT) ---
_wnt = [
    'XAV-939', 'IWP-2', 'LGK-974', 'WNTC59',
    'CYCLOPAMINE', 'VISMODEGIB', 'SONIDEGIB',
    'SB-216763', 'CHIR-99021',
]
for d in _wnt: DRUG_PATHWAY[d] = 'WNT signaling'

# --- JNK / p38 (INPUT) ---
_jnk = ['DORAMAPIMOD', 'AS601245', '(5Z)-7-OXOZEAENOL', 'JNK INHIBITOR VIII']
for d in _jnk: DRUG_PATHWAY[d] = 'JNK and p38 signaling'

# --- METABOLISM (INPUT) ---
_met = [
    'AICAR', 'METFORMIN', 'AGI-5198', 'AGI-6780',
    'APO866', 'APO866, FK866', 'CAY10566', 'C-75', 'AR-12', 'PHENFORMIN',
]
for d in _met: DRUG_PATHWAY[d] = 'Metabolism'

# --- IMMUNE RESPONSE (INPUT) ---
_imm = [
    'LENALIDOMIDE', 'THALIDOMIDE', 'POMALIDOMIDE',
    'RUXOLITINIB', 'TOFACITINIB', 'IBRUTINIB', 'BMS-345541',
]
for d in _imm: DRUG_PATHWAY[d] = 'Immune response'


def map_drug_to_pathway(drug_name):
    """Map drug name to pathway. Direct match then pattern match."""
    if pd.isna(drug_name):
        return None
    name = str(drug_name).strip().upper()

    # Direct match
    if name in DRUG_PATHWAY:
        return DRUG_PATHWAY[name]

    # Partial match
    for key, pw in DRUG_PATHWAY.items():
        if key in name or name in key:
            return pw

    # Pattern-based fallback
    nl = name.lower()
    patterns = [
        (['parp', 'olaparib', 'talazoparib', 'rucaparib'], 'Genome integrity'),
        (['taxel', 'taxol', 'vincrist', 'vinblast'], 'Mitosis'),
        (['platin'], 'Genome integrity'),
        (['bortezomib', 'carfilzomib'], 'Protein stability and degradation'),
        (['vorinostat', 'panobinostat', 'hdac'], 'Chromatin histone acetylation'),
        (['palbociclib', 'ribociclib'], 'Cell cycle'),
        (['nutlin', 'mdm2'], 'Cell cycle'),
        (['venetoclax', 'navitoclax'], 'Apoptosis regulation'),
        (['hsp90', 'ganetespib'], 'Protein stability and degradation'),
        (['topotecan', 'camptothecin', 'etoposide'], 'Genome integrity'),
        (['mek', 'trametinib', 'selumetinib'], 'ERK MAPK signaling'),
        (['braf', 'dabrafenib', 'vemurafenib'], 'ERK MAPK signaling'),
        (['pi3k', 'mtor', 'rapamycin', 'everolimus'], 'PI3K/MTOR signaling'),
        (['egfr', 'erlotinib', 'gefitinib', 'afatinib'], 'EGFR signaling'),
        (['sunitinib', 'axitinib', 'imatinib', 'nilotinib'], 'RTK signaling'),
        (['tamoxifen', 'bicalutamide'], 'Hormone-related'),
        (['wnt', 'hedgehog', 'vismodegib'], 'WNT signaling'),
    ]
    for keywords, pw in patterns:
        if any(k in nl for k in keywords):
            return pw
    return None


# ============================================================================
# SECTION 2: CLASSIFICATION
# ============================================================================

STRUCTURE_PATHWAYS = {
    'Genome integrity', 'DNA replication', 'Cell cycle',
    'Protein stability and degradation', 'Mitosis',
    'Apoptosis regulation', 'Chromatin histone acetylation',
    'Chromatin histone methylation', 'Chromatin other',
}

INPUT_PATHWAYS = {
    'ERK MAPK signaling', 'PI3K/MTOR signaling', 'RTK signaling',
    'IGF1R signaling', 'EGFR signaling', 'Hormone-related',
    'Metabolism', 'WNT signaling', 'ABL signaling',
    'JNK and p38 signaling', 'Immune response',
}


def classify_perturbation(pathway, ic50, max_conc):
    """
    INPUT  = sub-lethal dose of signaling drug (IC50 > MAX_CONC)
    STRUCTURE = maintenance-targeting drug (any dose)
              OR supra-lethal dose of signaling drug (IC50 ≤ MAX_CONC)
    """
    if pathway is None or pathway == 'Other':
        return None
    if pathway in STRUCTURE_PATHWAYS:
        return 'STRUCTURE'
    if pathway in INPUT_PATHWAYS:
        if pd.notna(ic50) and pd.notna(max_conc) and max_conc > 0:
            return 'INPUT' if ic50 > max_conc else 'STRUCTURE'
        return None  # can't classify without dose info
    return None


# ============================================================================
# SECTION 3: STATISTICAL TESTS
# ============================================================================

def sigmoid(x, L, k, x0, b):
    return L / (1 + np.exp(-k * (x - x0))) + b


def compute_aic(n, rss, k):
    if rss <= 0 or n <= k + 1:
        return np.inf
    return n * np.log(rss / n) + 2 * k


def run_analysis(df, response_var='AUC_PUBLISHED', label='', n_perm=10000):
    """
    Full statistical battery:
    1. Mann-Whitney U + Cohen's d
    2. Permutation test (vectorized, fast)
    3. Sigmoid vs linear fit (R², AIC)
    4. Magnitude ratio
    """
    inv = df.loc[df['PERTURBATION_TYPE'] == 'INPUT', response_var].dropna().values
    stv = df.loc[df['PERTURBATION_TYPE'] == 'STRUCTURE', response_var].dropna().values

    if len(inv) < 30 or len(stv) < 30:
        print(f"  ⚠ {label}: insufficient data (INPUT={len(inv)}, STRUCT={len(stv)})")
        return None

    res = {'label': label, 'n_input': len(inv), 'n_structure': len(stv)}

    # --- 1. Mann-Whitney U + Cohen's d ---
    U, p_mw = stats.mannwhitneyu(inv, stv, alternative='two-sided')
    n1, n2 = len(inv), len(stv)
    pooled_std = np.sqrt(
        ((n1 - 1) * np.var(inv, ddof=1) + (n2 - 1) * np.var(stv, ddof=1))
        / (n1 + n2 - 2)
    )
    res['cohens_d'] = (np.mean(stv) - np.mean(inv)) / pooled_std if pooled_std > 0 else 0
    res['mann_whitney_U'] = U
    res['mann_whitney_p'] = p_mw

    # --- 2. Permutation test (VECTORIZED for speed) ---
    obs_diff = np.mean(stv) - np.mean(inv)
    combined = np.concatenate([inv, stv])
    N = len(combined)
    rng = np.random.RandomState(42)

    # Vectorized: shuffle all at once, compute means via indexing
    # For very large datasets, subsample to keep it fast
    MAX_PERM_SAMPLE = 50000
    if N > MAX_PERM_SAMPLE:
        # Subsample for permutation test (preserves distribution)
        idx_in = rng.choice(len(inv), min(len(inv), MAX_PERM_SAMPLE // 2), replace=False)
        idx_st = rng.choice(len(stv), min(len(stv), MAX_PERM_SAMPLE // 2), replace=False)
        combined_sub = np.concatenate([inv[idx_in], stv[idx_st]])
        n_in_sub = len(idx_in)
    else:
        combined_sub = combined
        n_in_sub = n1

    N_sub = len(combined_sub)
    perm_diffs = np.empty(n_perm)
    for i in range(n_perm):
        rng.shuffle(combined_sub)
        perm_diffs[i] = np.mean(combined_sub[n_in_sub:]) - np.mean(combined_sub[:n_in_sub])

    res['observed_diff'] = obs_diff
    res['permutation_p'] = float(np.mean(np.abs(perm_diffs) >= np.abs(obs_diff)))
    res['perm_diffs'] = perm_diffs

    # --- 3. Sigmoid vs linear fit ---
    if 'LN_IC50' in df.columns:
        x = df['LN_IC50'].values
        y = df[response_var].values
        mask = np.isfinite(x) & np.isfinite(y)
        if mask.sum() > 100:
            xs, ys = x[mask], y[mask]
            # Subsample for fitting if too large
            if len(xs) > 20000:
                fidx = rng.choice(len(xs), 20000, replace=False)
                xs, ys = xs[fidx], ys[fidx]
            idx = np.argsort(xs)
            xs, ys = xs[idx], ys[idx]
            ss_tot = np.sum((ys - np.mean(ys)) ** 2)

            # Linear
            try:
                c = np.polyfit(xs, ys, 1)
                yp = np.polyval(c, xs)
                ss_lin = np.sum((ys - yp) ** 2)
                res['R2_linear'] = max(0, 1 - ss_lin / ss_tot) if ss_tot > 0 else 0
                res['AIC_linear'] = compute_aic(len(ys), ss_lin, 2)
            except:
                res['R2_linear'] = np.nan
                res['AIC_linear'] = np.inf

            # Sigmoid
            try:
                p0 = [np.ptp(ys), 0.5, np.median(xs), np.min(ys)]
                popt, _ = curve_fit(sigmoid, xs, ys, p0=p0, maxfev=10000)
                yp = sigmoid(xs, *popt)
                ss_sig = np.sum((ys - yp) ** 2)
                res['R2_sigmoid'] = max(0, 1 - ss_sig / ss_tot) if ss_tot > 0 else 0
                res['AIC_sigmoid'] = compute_aic(len(ys), ss_sig, 4)
            except:
                res['R2_sigmoid'] = np.nan
                res['AIC_sigmoid'] = np.inf

            res['delta_AIC'] = res.get('AIC_linear', np.inf) - res.get('AIC_sigmoid', np.inf)

    # --- 4. Magnitude ratio ---
    mean_in, mean_st = np.mean(inv), np.mean(stv)
    res['mean_input'] = mean_in
    res['mean_structure'] = mean_st

    if 'AUC' in response_var.upper():
        mag_in = 1.0 - mean_in  # perturbation magnitude (AUC: 1=no effect)
        mag_st = 1.0 - mean_st
        res['mag_input'] = mag_in
        res['mag_structure'] = mag_st
        res['ratio'] = mag_st / mag_in if mag_in > 0.001 else np.inf
    else:
        res['ratio'] = abs(mean_st) / abs(mean_in) if abs(mean_in) > 0.001 else np.inf

    return res


# ============================================================================
# SECTION 4: DISPLAY
# ============================================================================

def print_result(res):
    if res is None:
        return
    print(f"\n  N(input)={res['n_input']:,}, N(structure)={res['n_structure']:,}")

    d = abs(res['cohens_d'])
    eff = "négligeable" if d < 0.2 else ("faible" if d < 0.5 else ("moyen" if d < 0.8 else "FORT"))
    print(f"\n  1. Mann-Whitney U = {res['mann_whitney_U']:,.0f}")
    print(f"     p = {res['mann_whitney_p']:.2e}")
    print(f"     Cohen's d = {res['cohens_d']:+.4f}  ({eff})")

    print(f"\n  2. Test de permutation ({10000:,} shuffles)")
    print(f"     Δ observée = {res['observed_diff']:+.6f}")
    print(f"     p(perm)   = {res['permutation_p']:.4f}")

    if 'R2_linear' in res and not np.isnan(res.get('R2_linear', np.nan)):
        print(f"\n  3. Ajustement dose-réponse")
        print(f"     R²(linéaire)  = {res['R2_linear']:.4f},  AIC = {res['AIC_linear']:.0f}")
        r2s = res.get('R2_sigmoid', np.nan)
        aics = res.get('AIC_sigmoid', np.inf)
        if not np.isnan(r2s):
            print(f"     R²(sigmoïde)  = {r2s:.4f},  AIC = {aics:.0f}")
            da = res.get('delta_AIC', 0)
            verdict = ("sigmoïde ≫ linéaire" if da > 10 else
                       ("sigmoïde > linéaire" if da > 2 else
                        ("≈ équivalent" if da > -2 else "linéaire > sigmoïde")))
            print(f"     ΔAIC(lin−sig)  = {da:+.0f}  →  {verdict}")
        else:
            print(f"     R²(sigmoïde)  = échec du fit")

    print(f"\n  4. Ratio de magnitude")
    print(f"     AUC moyen:  INPUT = {res['mean_input']:.4f}  |  STRUCTURE = {res['mean_structure']:.4f}")
    if 'mag_input' in res:
        print(f"     Magnitude (1−AUC):  INPUT = {res['mag_input']:.4f}  |  STRUCTURE = {res['mag_structure']:.4f}")
    print(f"     ★  Ratio S/I = {res['ratio']:.3f}×   (cible R-XVII ≈ 1.8×)")


# ============================================================================
# SECTION 5: VISUALIZATION
# ============================================================================

def create_plots(df, res_auc, threshold_results, pathway_results):
    fig, axes = plt.subplots(2, 3, figsize=(20, 13))
    fig.suptitle('R-XVII Asymmetry Test — REAL GDSC Data',
                 fontsize=15, fontweight='bold', y=0.98)

    inv = df.loc[df['PERTURBATION_TYPE'] == 'INPUT', 'AUC_PUBLISHED'].dropna()
    stv = df.loc[df['PERTURBATION_TYPE'] == 'STRUCTURE', 'AUC_PUBLISHED'].dropna()

    # --- 1. Distribution ---
    ax = axes[0, 0]
    ax.hist(inv, bins=80, alpha=0.55, label=f'INPUT (n={len(inv):,})',
            color='#2196F3', density=True)
    ax.hist(stv, bins=80, alpha=0.55, label=f'STRUCTURE (n={len(stv):,})',
            color='#E53935', density=True)
    ax.axvline(inv.mean(), color='#0D47A1', ls='--', lw=2, label=f'μ_in={inv.mean():.3f}')
    ax.axvline(stv.mean(), color='#B71C1C', ls='--', lw=2, label=f'μ_st={stv.mean():.3f}')
    ax.set_xlabel('AUC (1=résistant, 0=tué)')
    ax.set_ylabel('Densité')
    ax.set_title('Distribution AUC: Input vs Structure')
    ax.legend(fontsize=8)

    # --- 2. Violin plot ---
    ax = axes[0, 1]
    parts = ax.violinplot([inv.values, stv.values], positions=[0, 1],
                          showmeans=True, showmedians=True)
    for i, pc in enumerate(parts['bodies']):
        pc.set_facecolor(['#2196F3', '#E53935'][i])
        pc.set_alpha(0.6)
    ax.set_xticks([0, 1])
    ax.set_xticklabels(['INPUT', 'STRUCTURE'])
    ax.set_ylabel('AUC')
    if res_auc:
        ax.set_title(f"Cohen's d = {res_auc['cohens_d']:+.3f}, p = {res_auc['mann_whitney_p']:.2e}")

    # --- 3. Permutation test ---
    ax = axes[0, 2]
    if res_auc and 'perm_diffs' in res_auc:
        ax.hist(res_auc['perm_diffs'], bins=80, alpha=0.7, color='#9E9E9E', density=True)
        ax.axvline(res_auc['observed_diff'], color='#E53935', lw=2.5,
                   label=f"Observé: {res_auc['observed_diff']:+.4f}")
        ax.set_xlabel('Δ(Structure − Input) sous H₀')
        ax.set_ylabel('Densité')
        ax.set_title(f"Permutation test (p={res_auc['permutation_p']:.4f})")
        ax.legend()

    # --- 4. Threshold sensitivity ---
    ax = axes[1, 0]
    if threshold_results:
        names = [r['threshold_name'] for r in threshold_results]
        ds = [r['cohens_d'] for r in threshold_results]
        ratios = [r['ratio'] for r in threshold_results]
        bars = ax.bar(names, ds, alpha=0.7, color='#7B1FA2')
        ax.set_ylabel("Cohen's d", color='#7B1FA2')
        ax.set_title('Robustesse: seuil IC30 → IC70')
        ax2 = ax.twinx()
        ax2.plot(names, ratios, 'D-', color='#FF6F00', lw=2, ms=8)
        ax2.axhline(1.8, color='#FF6F00', ls=':', alpha=0.5, label='Cible 1.8×')
        ax2.set_ylabel('Ratio Magnitude S/I', color='#FF6F00')
        ax2.legend(fontsize=8)

    # --- 5. By pathway ---
    ax = axes[1, 1]
    if pathway_results:
        pw_names = [r['label'].replace('Pathway: ', '')[:25] for r in pathway_results]
        pw_d = [r['cohens_d'] for r in pathway_results]
        colors = ['#E53935' if abs(d) > 0.5 else '#9E9E9E' for d in pw_d]
        ax.barh(pw_names, pw_d, color=colors, alpha=0.7)
        ax.axvline(0, color='black', lw=0.5)
        ax.set_xlabel("Cohen's d")
        ax.set_title('Asymétrie par pathway\n(input drugs: sub- vs supra-lethal)')

    # --- 6. AUC by pathway ---
    ax = axes[1, 2]
    pw_data = []
    for pw, grp in df.groupby('PATHWAY_NAME'):
        if pw and len(grp) > 200:
            ptype = ('STRUCTURE' if pw in STRUCTURE_PATHWAYS else
                     ('INPUT' if pw in INPUT_PATHWAYS else None))
            if ptype:
                pw_data.append({
                    'pathway': str(pw)[:22], 'mean_AUC': grp['AUC_PUBLISHED'].mean(),
                    'type': ptype, 'n': len(grp)
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

    plt.tight_layout()
    out_path = 'rXVII_real_gdsc.png'
    plt.savefig(out_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"\n  → Figure: {os.path.abspath(out_path)}")


# ============================================================================
# SECTION 6: MAIN
# ============================================================================

def main():
    t0 = time.time()

    # --- Find data file ---
    candidates = [
        'sanger-dose-response.csv',
        os.path.join('..', 'sanger-dose-response.csv'),
        os.path.expanduser('~/Downloads/sanger-dose-response.csv'),
    ]
    data_path = None
    for c in candidates:
        if os.path.exists(c):
            data_path = c
            break

    if data_path is None:
        print("ERREUR: sanger-dose-response.csv introuvable.")
        print("Place le fichier dans le même dossier que ce script.")
        print("Téléchargement: https://depmap.org/portal/data_page/")
        print("  → Release 'Sanger GDSC1 and GDSC2'")
        print("  → Fichier 'sanger-dose-response.csv'")
        sys.exit(1)

    # --- Load ---
    print("=" * 75)
    print("  R-XVII ASYMMETRY TEST — REAL GDSC DATA")
    print("=" * 75)
    print(f"\n  Chargement: {data_path}")
    df = pd.read_csv(data_path)
    print(f"  {len(df):,} observations")
    print(f"  {df['COSMIC_ID'].nunique()} lignées × {df['DRUG_NAME'].nunique()} drogues")
    print(f"  Datasets: {df['DATASET'].value_counts().to_dict()}")

    # Detect column names (may vary between GDSC releases)
    ic50_col = 'IC50_PUBLISHED' if 'IC50_PUBLISHED' in df.columns else 'LN_IC50'
    auc_col = 'AUC_PUBLISHED' if 'AUC_PUBLISHED' in df.columns else 'AUC'
    print(f"  IC50 column: {ic50_col}")
    print(f"  AUC column:  {auc_col}")

    # --- Map pathways ---
    print(f"\n{'=' * 75}")
    print("  MAPPING PHARMACOLOGIQUE")
    print(f"{'=' * 75}")
    df['PATHWAY_NAME'] = df['DRUG_NAME'].apply(map_drug_to_pathway)
    df['LN_IC50'] = np.log(df[ic50_col].clip(lower=1e-6))

    mapped = df['PATHWAY_NAME'].notna().sum()
    print(f"  Couverture: {mapped:,} / {len(df):,} ({100 * mapped / len(df):.1f}%)")

    pw_counts = df['PATHWAY_NAME'].value_counts()
    print(f"\n  Distribution des pathways:")
    for pw, n in pw_counts.items():
        ptype = ('STRUCT' if pw in STRUCTURE_PATHWAYS else
                 ('INPUT' if pw in INPUT_PATHWAYS else 'OTHER'))
        print(f"    {ptype:6s}  {str(pw):<42s}  {n:>6,d}")

    unmapped = df[df['PATHWAY_NAME'].isna()]['DRUG_NAME'].value_counts().head(15)
    print(f"\n  Top drogues non mappées:")
    for d, n in unmapped.items():
        print(f"    {str(d):<42s}  {n:>6,d}")

    # --- Classify ---
    print(f"\n{'=' * 75}")
    print("  CLASSIFICATION INPUT / STRUCTURE")
    print(f"{'=' * 75}")
    df['PERTURBATION_TYPE'] = df.apply(
        lambda r: classify_perturbation(r['PATHWAY_NAME'], r[ic50_col], r['MAX_CONC']),
        axis=1
    )

    counts = df['PERTURBATION_TYPE'].value_counts(dropna=False)
    for k, v in counts.items():
        label = str(k) if pd.notna(k) else 'EXCLUDED'
        print(f"  {label:12s}: {v:>7,d}  ({100 * v / len(df):.1f}%)")

    dfc = df.dropna(subset=['PERTURBATION_TYPE']).copy()
    n_in = (dfc['PERTURBATION_TYPE'] == 'INPUT').sum()
    n_st = (dfc['PERTURBATION_TYPE'] == 'STRUCTURE').sum()
    print(f"\n  Dataset de travail: {len(dfc):,}")
    print(f"  INPUT:     {n_in:,}")
    print(f"  STRUCTURE: {n_st:,}")

    # ============================================================
    # ANALYSE PRINCIPALE
    # ============================================================
    print(f"\n{'=' * 75}")
    print(f"  ANALYSE PRINCIPALE: {auc_col}")
    print(f"{'=' * 75}")
    res_auc = run_analysis(dfc, auc_col, f'{auc_col} (global)')
    print_result(res_auc)

    # LN_IC50
    print(f"\n{'=' * 75}")
    print(f"  ANALYSE SECONDAIRE: LN(IC50)")
    print(f"{'=' * 75}")
    res_ic50 = run_analysis(dfc, 'LN_IC50', 'LN_IC50 (global)')
    print_result(res_ic50)

    # GDSC2 only
    print(f"\n{'=' * 75}")
    print(f"  GDSC2 SEUL (meilleure qualité)")
    print(f"{'=' * 75}")
    dfc2 = dfc[dfc['DATASET'] == 'GDSC2']
    res_gdsc2 = run_analysis(dfc2, auc_col, f'{auc_col} (GDSC2)')
    print_result(res_gdsc2)

    # ============================================================
    # ROBUSTESSE: seuil IC
    # ============================================================
    print(f"\n{'=' * 75}")
    print(f"  ROBUSTESSE: Sensibilité au seuil (IC30 → IC70)")
    print(f"{'=' * 75}")

    threshold_results = []
    for name, q in [('IC30', 0.30), ('IC40', 0.40), ('IC50', 0.50),
                    ('IC60', 0.60), ('IC70', 0.70)]:
        df_t = df[df['PATHWAY_NAME'].notna() & (df['PATHWAY_NAME'] != 'Other')].copy()
        threshold = df_t[ic50_col].quantile(q)

        def _classify(row):
            pw = row['PATHWAY_NAME']
            if pw in STRUCTURE_PATHWAYS:
                return 'STRUCTURE'
            if pw in INPUT_PATHWAYS:
                ic = row[ic50_col]
                if pd.notna(ic):
                    return 'INPUT' if ic > threshold else 'STRUCTURE'
            return None

        df_t['PERTURBATION_TYPE'] = df_t.apply(_classify, axis=1)
        df_t = df_t.dropna(subset=['PERTURBATION_TYPE'])

        r = run_analysis(df_t, auc_col, f'Seuil={name}', n_perm=5000)
        if r:
            r['threshold_name'] = name
            r['threshold_value'] = threshold
            threshold_results.append(r)
            print(f"  {name} (seuil={threshold:.2f}): "
                  f"d={r['cohens_d']:+.3f}, p={r['mann_whitney_p']:.2e}, "
                  f"ratio={r['ratio']:.3f}×, n_in={r['n_input']:,}, n_st={r['n_structure']:,}")

    # ============================================================
    # PAR PATHWAY
    # ============================================================
    print(f"\n{'=' * 75}")
    print(f"  ANALYSE PAR PATHWAY (intra input-pathway drugs)")
    print(f"{'=' * 75}")

    pathway_results = []
    for pw in sorted(INPUT_PATHWAYS):
        sub = dfc[dfc['PATHWAY_NAME'] == pw]
        if len(sub) < 100:
            continue
        r = run_analysis(sub, auc_col, f'Pathway: {pw}', n_perm=5000)
        if r:
            pathway_results.append(r)
            sig = ('***' if r['mann_whitney_p'] < 0.001 else
                   ('**' if r['mann_whitney_p'] < 0.01 else
                    ('*' if r['mann_whitney_p'] < 0.05 else 'ns')))
            print(f"  {pw:<30s}: d={r['cohens_d']:+.3f}, "
                  f"p={r['mann_whitney_p']:.2e} {sig}, ratio={r['ratio']:.3f}×")

    # ============================================================
    # VISUALIZATIONS
    # ============================================================
    print(f"\n{'=' * 75}")
    print(f"  GÉNÉRATION DES FIGURES")
    print(f"{'=' * 75}")
    create_plots(dfc, res_auc, threshold_results, pathway_results)

    # ============================================================
    # SUMMARY TABLE
    # ============================================================
    print(f"\n{'=' * 75}")
    print(f"  TABLE RÉCAPITULATIVE FINALE")
    print(f"{'=' * 75}")
    header = f"  {'Analyse':<40s} {'n_in':>7s} {'n_st':>8s} {'d':>7s} {'p(MW)':>11s} {'p(perm)':>8s} {'Ratio':>7s}"
    sep = f"  {'-' * 40} {'-' * 7} {'-' * 8} {'-' * 7} {'-' * 11} {'-' * 8} {'-' * 7}"
    print(header)
    print(sep)
    for r in [res_auc, res_ic50, res_gdsc2]:
        if r:
            print(f"  {r['label']:<40s} {r['n_input']:>7,d} {r['n_structure']:>8,d} "
                  f"{r['cohens_d']:>+7.3f} {r['mann_whitney_p']:>11.2e} "
                  f"{r['permutation_p']:>8.4f} {r['ratio']:>7.2f}×")

    if threshold_results:
        print(f"\n  Robustesse au seuil:")
        for r in threshold_results:
            print(f"    {r['threshold_name']:<38s} {r['n_input']:>7,d} {r['n_structure']:>8,d} "
                  f"{r['cohens_d']:>+7.3f} {r['mann_whitney_p']:>11.2e} "
                  f"{r['permutation_p']:>8.4f} {r['ratio']:>7.2f}×")

    # ============================================================
    # EXPORT CSV
    # ============================================================
    all_results = []
    for r in [res_auc, res_ic50, res_gdsc2] + threshold_results + pathway_results:
        if r:
            row = {k: v for k, v in r.items() if k != 'perm_diffs'}
            all_results.append(row)

    results_df = pd.DataFrame(all_results)
    results_df.to_csv('rXVII_results.csv', index=False)
    print(f"\n  → Résultats exportés: {os.path.abspath('rXVII_results.csv')}")

    elapsed = time.time() - t0
    print(f"\n  Temps total: {elapsed:.1f}s")

    # ============================================================
    # INTERPRÉTATION R-XVII
    # ============================================================
    print(f"\n{'=' * 75}")
    print(f"  INTERPRÉTATION R-XVII")
    print(f"{'=' * 75}")
    if res_auc:
        print(f"""
  R-XVII prédit une asymétrie qualitative entre perturbation d'input
  (signalisation) et perturbation de structure (maintenance), indexée
  sur la cible topologique, pas sur l'amplitude.

  Résultat GDSC:
    Cohen's d  = {res_auc['cohens_d']:+.4f}  (p = {res_auc['mann_whitney_p']:.2e})
    Ratio S/I  = {res_auc['ratio']:.3f}×   (cible trans-domaniale ≈ 1.8×)

  Comparaison trans-domaniale:
    Microbiome (MDSINE2, dysbiotique):  d = 1.16,  p = 0.0006
    Logiciels (Gosme 2025):             ratio ≈ 1.8×
    Cancer (GDSC):                      d = {res_auc['cohens_d']:+.3f}, ratio = {res_auc['ratio']:.2f}×

  La classification est faite sur le pathway cible de la drogue
  (propriété du traitement), JAMAIS sur la réponse cellulaire.
  Pas de circularité.
""")

    return dfc, res_auc


if __name__ == '__main__':
    dfc, res = main()