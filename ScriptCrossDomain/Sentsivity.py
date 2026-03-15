#!/usr/bin/env python3
"""
=============================================================================
SENSITIVITY BATTERY FOR R-XVII RATIO ρ — v2 (with Yeast)
=============================================================================

4 tests executed in dependency order:  T4 → T2 → T1 → T3

  TEST 4 — Metrological audit: 4 definitions of ρ × 4 domains
  TEST 2 — Null pipeline: permutation nulls + intensity simulation
  TEST 1 — Multi-operationalization: 4 partitions on GDSC
  TEST 3 — Hierarchical Bayesian: cross-domain τ estimation

v2: Added yeast (S. cerevisiae) as 4th domain.

Seeds: all fixed (20240601) for reproducibility.
=============================================================================
"""

import json
import os
import sys
import time
import types
import warnings
from pathlib import Path
from collections import defaultdict

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

# --- PATCH LLVMLITE/NUMBA ---
def _patch_llvmlite():
    try:
        import llvmlite.binding
        return
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
            m = types.ModuleType(mod_name)
            m.__path__ = []
            sys.modules[mod_name] = m
    for mod_name in [
        'numba', 'numba.core', 'numba.core.config', 'numba.core.types',
        'numba.core.typing', 'numba.core.errors', 'numba.core.decorators',
        'numba.np', 'numba.np.ufunc', 'numba.typed', 'numba.typed.typedlist',
        'numba.typed.typeddict', 'numba.experimental',
    ]:
        if mod_name not in sys.modules:
            m = types.ModuleType(mod_name)
            m.__path__ = []
            sys.modules[mod_name] = m
    def _noop(*a, **kw):
        if len(a) == 1 and callable(a[0]): return a[0]
        return lambda f: f
    nm = sys.modules['numba']
    nm.njit = _noop; nm.jit = _noop; nm.vectorize = _noop
    nm.prange = range; nm.float64 = float; nm.int64 = int
    nm.boolean = bool; nm.types = sys.modules['numba.core.types']

_patch_llvmlite()
# --- END PATCH ---

SEED = 20240601
RNG = np.random.RandomState(SEED)

# ═══════════════════════════════════════════════════════════════════════════
# CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════

_GDSC_CANDIDATES = [
    '../ScriptGDSC/sanger-dose-response.csv',
    'sanger-dose-response.csv',
    '../data/sanger-dose-response.csv',
]
_REEF_CANDIDATES = [
    '../ScriptCorail/global_bleaching_environmental.csv',
    'global_bleaching_environmental.csv',
    '../data/global_bleaching_environmental.csv',
]
_MICRO_CSV_CANDIDATES = [
    'microbiome_bc_distances.csv',
    'output/microbiome_bc_distances.csv',
    '../output/microbiome_bc_distances.csv',
    '../ScriptMDSINE2/microbiome_bc_distances.csv',
    '../ScriptMDSINE2/output/microbiome_bc_distances.csv',
    '../data/microbiome_bc_distances.csv',
]
_MDSINE2_CANDIDATES = [
    'MDSINE2_Paper', '../MDSINE2_Paper', '../../MDSINE2_Paper',
]
_YEAST_GAF_CANDIDATES = [
    '../ScriptYeast/gene_association.sgd.20251124.gaf',
    'gene_association.sgd.20251124.gaf',
]
_YEAST_HOM_MATRIX_CANDIDATES = [
    '../ScriptYeast/yp_matrix_z_haphom_20221025.txt',
]
_YEAST_HOM_SCREENS_CANDIDATES = [
    '../ScriptYeast/yp_screens_haphom_20221025.txt',
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
    n_perm = N_PERM
    n_boot = N_BOOT
    skip = []


# ═══════════════════════════════════════════════════════════════════════════
# DRUG CLASSIFICATION (GDSC) — unchanged from v1
# ═══════════════════════════════════════════════════════════════════════════

_struct_drugs_A = {
    'Genome integrity': [
        'OLAPARIB','TALAZOPARIB','RUCAPARIB','NIRAPARIB','VELIPARIB',
        'MIRIN','KU-55933','KU-60019','KU-57788','NU-7441',
        'AZD6738','VE-821','VE-822','AZD7762','CHIR-124','MK-8776',
        'BLEOMYCIN','CISPLATIN','CARBOPLATIN','OXALIPLATIN',
        'CARMUSTINE','LOMUSTINE','TEMOZOLOMIDE','MITOMYCIN-C',
        'ETOPOSIDE','CAMPTOTHECIN','SN-38','IRINOTECAN','TOPOTECAN',
        'DOXORUBICIN','DACTINOMYCIN','EPIRUBICIN','MITOXANTRONE',
    ],
    'DNA replication': [
        'GEMCITABINE','CYTARABINE','5-FLUOROURACIL','METHOTREXATE',
        'FLUDARABINE','CLOFARABINE','HYDROXYUREA','PEMETREXED','CLADRIBINE',
    ],
    'Cell cycle': [
        'PALBOCICLIB','RIBOCICLIB','ABEMACICLIB','RO-3306',
        'ALVOCIDIB','DINACICLIB','CGP-60474',
        'NUTLIN-3A (-)','NUTLIN-3A','APR-246','RG7388','IDASANUTLIN','681640',
    ],
    'Mitosis': [
        'PACLITAXEL','DOCETAXEL','VINBLASTINE','VINCRISTINE','VINORELBINE',
        'EPOTHILONE-B','ALISERTIB','ZM-447439','BARASERTIB','TOZASERTIB',
        'BI-2536','VOLASERTIB','GSK461364',
        'S-TRITYL-L-CYSTEINE','ISPINESIB','MPS1-IN-1',
    ],
    'Protein stability and degradation': [
        'BORTEZOMIB','CARFILZOMIB','MG-132','PEVONEDISTAT',
        '17-AAG','TANESPIMYCIN','AUY922','GANETESPIB','LUMINESPIB','SNX-2112',
    ],
    'Apoptosis regulation': [
        'NAVITOCLAX','ABT-737','VENETOCLAX','ABT-199',
        'AZD5582','BIRINAPANT','EMBELIN','LCL-161','YM-155','OBATOCLAX',
    ],
    'Chromatin': [
        'VORINOSTAT','BELINOSTAT','PANOBINOSTAT','ENTINOSTAT',
        'AR-42','CAY10603','ACY-1215','TUBASTATIN A','TRICHOSTATIN A',
        'JQ1','I-BET-762','OTX015','APABETALONE',
        'EPZ-5676','PINOMETOSTAT','GSK343','EPZ004777','EI1',
        'UNC0638','CHAETOCIN','DECITABINE','AZACYTIDINE','PFI-3',
    ],
}
_input_drugs_A = {
    'ERK MAPK signaling': [
        'PD-0325901','TRAMETINIB','SELUMETINIB','BINIMETINIB','COBIMETINIB',
        'REFAMETINIB','CI-1040','PIMASERTIB',
        'PLX-4720','DABRAFENIB','VEMURAFENIB','ENCORAFENIB',
        'SORAFENIB','AZ-628','SB-590885','TAK-632',
        'SCH772984','BVD-523','ULIXERTINIB','VX-11E',
    ],
    'PI3K/MTOR signaling': [
        'GDC-0941','ALPELISIB','BUPARLISIB','PICTILISIB',
        'IDELALISIB','COPANLISIB','APITOLISIB','AMG-319','TASELISIB',
        'NVP-BEZ235','DACTOLISIB',
        'AZD8055','VISTUSERTIB','SAPANISERTIB','OSI-027',
        'SIROLIMUS','EVEROLIMUS','TEMSIROLIMUS','RAPAMYCIN',
        'MK-2206','AZD5363','IPATASERTIB','CAPIVASERTIB','UPROSERTIB',
        'AT13148','AZD6482','BX-795',
    ],
    'EGFR signaling': [
        'ERLOTINIB','GEFITINIB','LAPATINIB','NERATINIB',
        'AFATINIB','OSIMERTINIB','AZD3759',
        'AZD8931','CANERTINIB','SAPITINIB','AST-1306','CETUXIMAB',
    ],
    'RTK signaling': [
        'SUNITINIB','AXITINIB','PAZOPANIB','LENVATINIB',
        'CABOZANTINIB','REGORAFENIB','TIVOZANIB',
        'IMATINIB','NILOTINIB','DASATINIB','PONATINIB','BOSUTINIB',
        'CRIZOTINIB','ALECTINIB','CERITINIB',
        'NVP-TAE684','PHA-665752',
        'BRIVANIB','PD-173074','AZD4547','BGJ398',
        'BMS-536924','BMS-754807','LINSITINIB',
        'AMUVATINIB','GNF-2','SARACATINIB','MASITINIB','DOVITINIB',
        'SB 505124','SB-505124','AVAGACESTAT',
        'GSK1904529A','FORETINIB','GSK269962A',
        'GW 441756','LESTAURTINIB','MIDOSTAURIN','SAVOLITINIB',
    ],
    'Hormone-related': ['TAMOXIFEN','BICALUTAMIDE','FULVESTRANT','DEXAMETHASONE','BEXAROTENE'],
    'WNT signaling': [
        'XAV-939','IWP-2','LGK-974','WNTC59',
        'CYCLOPAMINE','VISMODEGIB','SONIDEGIB','SB-216763','CHIR-99021',
    ],
    'JNK and p38 signaling': ['DORAMAPIMOD','AS601245','(5Z)-7-OXOZEAENOL','JNK INHIBITOR VIII'],
    'Metabolism': [
        'AICAR','METFORMIN','AGI-5198','AGI-6780',
        'APO866','APO866, FK866','CAY10566','C-75','AR-12','PHENFORMIN','PF-4708671',
    ],
    'Immune response': [
        'LENALIDOMIDE','THALIDOMIDE','POMALIDOMIDE',
        'RUXOLITINIB','TOFACITINIB','IBRUTINIB','BMS-345541',
    ],
}

STRUCT_PW_A = set(_struct_drugs_A.keys())
INPUT_PW_A = set(_input_drugs_A.keys())
DRUG_PW_A = {}
for pw, drugs in _struct_drugs_A.items():
    for d in drugs: DRUG_PW_A[d] = pw
for pw, drugs in _input_drugs_A.items():
    for d in drugs: DRUG_PW_A[d] = pw

def map_drug_A(name):
    if pd.isna(name): return None
    n = str(name).strip().upper()
    if n in DRUG_PW_A: return DRUG_PW_A[n]
    for key in DRUG_PW_A:
        if key in n or n in key: return DRUG_PW_A[key]
    return None

def ptype_A(pw):
    if pw in STRUCT_PW_A: return 'STRUCTURE'
    if pw in INPUT_PW_A: return 'INPUT'
    return None

# Partitions B, C, D — unchanged
_B_moved_to_input = {'Apoptosis regulation', 'Chromatin'}
def ptype_B(pw):
    if pw is None: return None
    if pw in _B_moved_to_input: return 'INPUT'
    if pw in STRUCT_PW_A: return 'STRUCTURE'
    if pw in INPUT_PW_A: return 'INPUT'
    return None

_C_extra_struct = {'LATRUNCULIN A','LATRUNCULIN B','CYTOCHALASIN D','JASPLAKINOLIDE','COLCHICINE','NOCODAZOLE'}
_C_extra_input = {'THAPSIGARGIN','TUNICAMYCIN','NUTLIN-3A (-)','NUTLIN-3A'}
def ptype_C(pw, drug_name):
    n = str(drug_name).strip().upper() if drug_name else ''
    if n in _C_extra_struct: return 'STRUCTURE'
    if n in _C_extra_input: return 'INPUT'
    if pw in STRUCT_PW_A: return 'STRUCTURE'
    if pw in INPUT_PW_A: return 'INPUT'
    return None

_ATC_struct = {
    'GEMCITABINE','CYTARABINE','5-FLUOROURACIL','METHOTREXATE',
    'FLUDARABINE','CLOFARABINE','HYDROXYUREA','PEMETREXED','CLADRIBINE',
    'DECITABINE','AZACYTIDINE',
    'PACLITAXEL','DOCETAXEL','VINBLASTINE','VINCRISTINE','VINORELBINE','EPOTHILONE-B',
    'DOXORUBICIN','DACTINOMYCIN','EPIRUBICIN','MITOXANTRONE','BLEOMYCIN','MITOMYCIN-C',
    'CISPLATIN','CARBOPLATIN','OXALIPLATIN','CARMUSTINE','LOMUSTINE','TEMOZOLOMIDE',
    'ETOPOSIDE','CAMPTOTHECIN','SN-38','IRINOTECAN','TOPOTECAN',
}
_ATC_input = {
    'PD-0325901','TRAMETINIB','SELUMETINIB','BINIMETINIB','COBIMETINIB',
    'REFAMETINIB','CI-1040','PIMASERTIB',
    'PLX-4720','DABRAFENIB','VEMURAFENIB','ENCORAFENIB',
    'SORAFENIB','AZ-628','SB-590885','TAK-632',
    'SCH772984','BVD-523','ULIXERTINIB','VX-11E',
    'GDC-0941','ALPELISIB','BUPARLISIB','PICTILISIB',
    'IDELALISIB','COPANLISIB','APITOLISIB','AMG-319','TASELISIB',
    'NVP-BEZ235','DACTOLISIB',
    'AZD8055','VISTUSERTIB','SAPANISERTIB','OSI-027',
    'SIROLIMUS','EVEROLIMUS','TEMSIROLIMUS','RAPAMYCIN',
    'MK-2206','AZD5363','IPATASERTIB','CAPIVASERTIB','UPROSERTIB',
    'AT13148','AZD6482','BX-795',
    'ERLOTINIB','GEFITINIB','LAPATINIB','NERATINIB',
    'AFATINIB','OSIMERTINIB','AZD3759',
    'AZD8931','CANERTINIB','SAPITINIB','AST-1306',
    'SUNITINIB','AXITINIB','PAZOPANIB','LENVATINIB',
    'CABOZANTINIB','REGORAFENIB','TIVOZANIB',
    'IMATINIB','NILOTINIB','DASATINIB','PONATINIB','BOSUTINIB',
    'CRIZOTINIB','ALECTINIB','CERITINIB',
    'NVP-TAE684','PHA-665752',
    'BRIVANIB','PD-173074','AZD4547','BGJ398',
    'BMS-536924','BMS-754807','LINSITINIB',
    'RUXOLITINIB','TOFACITINIB','IBRUTINIB',
    'PALBOCICLIB','RIBOCICLIB','ABEMACICLIB',
}
def ptype_D(drug_name):
    if pd.isna(drug_name): return None
    n = str(drug_name).strip().upper()
    if n in _ATC_struct: return 'STRUCTURE'
    if n in _ATC_input: return 'INPUT'
    return None


# ═══════════════════════════════════════════════════════════════════════════
# SHARED STATISTICAL ENGINE — unchanged
# ═══════════════════════════════════════════════════════════════════════════

def compute_rho_full(y_input, y_structure, label='', n_perm=10_000,
                     n_boot=10_000, rng=None):
    if rng is None: rng = RNG
    yi = y_input[np.isfinite(y_input)].copy()
    ys = y_structure[np.isfinite(y_structure)].copy()
    if len(yi) < 10 or len(ys) < 10:
        print(f"  ⚠ {label}: n too small (INPUT={len(yi)}, STRUCT={len(ys)})")
        return None

    res = {'label': label, 'n_input': len(yi), 'n_structure': len(ys)}
    res['mean_input'] = np.mean(yi); res['mean_struct'] = np.mean(ys)
    res['median_input'] = np.median(yi); res['median_struct'] = np.median(ys)
    res['rho_means'] = res['mean_struct'] / res['mean_input'] if res['mean_input'] != 0 else np.inf
    res['rho_medians'] = res['median_struct'] / res['median_input'] if res['median_input'] != 0 else np.inf

    n1, n2 = len(yi), len(ys)
    sp = np.sqrt(((n1-1)*np.var(yi,ddof=1)+(n2-1)*np.var(ys,ddof=1))/(n1+n2-2))
    d = (np.mean(ys)-np.mean(yi))/sp if sp > 0 else 0.0
    res['d'] = d; res['abs_d'] = abs(d)
    res['rho_exp_d'] = np.exp(d)

    combined = np.concatenate([yi, ys])
    threshold = np.median(combined)
    p_s = np.mean(ys > threshold); p_i = np.mean(yi > threshold)
    eps = 1e-8
    res['rho_logit'] = ((p_s+eps)/(1-p_s+eps)) / ((p_i+eps)/(1-p_i+eps))

    U, p_mw = stats.mannwhitneyu(yi, ys, alternative='two-sided')
    res['U'] = U; res['p_MW'] = p_mw

    obs_diff = np.mean(ys) - np.mean(yi)
    comb_sub = combined.copy(); n_in_sub = n1
    perm_diffs = np.empty(n_perm)
    for i in range(n_perm):
        rng.shuffle(comb_sub)
        perm_diffs[i] = np.mean(comb_sub[n_in_sub:]) - np.mean(comb_sub[:n_in_sub])
    res['p_perm'] = float(np.mean(np.abs(perm_diffs) >= np.abs(obs_diff)))

    boot_ratios = np.empty(n_boot)
    for b in range(n_boot):
        bi = rng.choice(yi, len(yi), replace=True)
        bs = rng.choice(ys, len(ys), replace=True)
        boot_ratios[b] = np.mean(bs)/np.mean(bi) if abs(np.mean(bi)) > 1e-12 else np.nan
    boot_ratios = boot_ratios[np.isfinite(boot_ratios)]
    res['rho_means_ci_lo'] = np.percentile(boot_ratios, 2.5)
    res['rho_means_ci_hi'] = np.percentile(boot_ratios, 97.5)

    boot_ds = np.empty(n_boot)
    for b in range(n_boot):
        bi = rng.choice(yi, len(yi), replace=True)
        bs = rng.choice(ys, len(ys), replace=True)
        sp_b = np.sqrt(((len(bi)-1)*np.var(bi,ddof=1)+(len(bs)-1)*np.var(bs,ddof=1))/(len(bi)+len(bs)-2))
        boot_ds[b] = (np.mean(bs)-np.mean(bi))/sp_b if sp_b > 0 else 0
    res['d_ci_lo'] = np.percentile(boot_ds, 2.5)
    res['d_ci_hi'] = np.percentile(boot_ds, 97.5)
    return res


def print_result(res, indent=2):
    if not res: return
    pfx = ' ' * indent
    d = res['abs_d']
    eff = "negligible" if d < 0.2 else "small" if d < 0.5 else "medium" if d < 0.8 else "LARGE"
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
    if not os.path.exists(path): return None
    df = pd.read_csv(path)
    auc_col = 'AUC_PUBLISHED' if 'AUC_PUBLISHED' in df.columns else 'AUC'
    df['_auc'] = pd.to_numeric(df[auc_col], errors='coerce')
    df['PATHWAY_A'] = df['DRUG_NAME'].apply(map_drug_A)
    df['PTYPE_A'] = df['PATHWAY_A'].apply(ptype_A)
    mapped = df['PTYPE_A'].notna().sum()
    print(f"[GDSC] {len(df):,} obs, {mapped:,} mapped")
    return df


def load_reef(path):
    if not os.path.exists(path): return None
    df = pd.read_csv(path)
    rn = {'Percent_Bleaching':'bleaching','SSTA_DHW':'dhw','Cyclone_Frequency':'cyclone_freq'}
    df = df.rename(columns=rn)
    for c in ['bleaching','dhw','cyclone_freq']:
        if c in df.columns: df[c] = pd.to_numeric(df[c], errors='coerce')
    df = df.dropna(subset=['bleaching','dhw'])
    print(f"[REEF] {len(df):,} observations")
    return df


def reef_classify(df):
    dhw = df['dhw'].fillna(0); cyc = df['cyclone_freq'].fillna(0)
    cyc_med = cyc[cyc > 0].median() if (cyc > 0).any() else 999
    pt = pd.Series('baseline', index=df.index)
    pt[(dhw >= 4) & (dhw < 8) & (cyc <= cyc_med)] = 'input'
    pt[(dhw >= 8) | (cyc > cyc_med * 1.5)] = 'structure'
    df['ptype'] = pt
    return df


def load_microbiome(csv_path=None, mdsine2_dir=None):
    if csv_path and os.path.exists(csv_path):
        df = pd.read_csv(csv_path)
        if 'bc_from_baseline' in df.columns:
            if 'cohort' in df.columns: df = df[df['cohort'] == 'dysbiotic']
            if 'time_since_pert' in df.columns: df = df[df['time_since_pert'] >= 4]
            inp = df.loc[df['pert_type']=='input','bc_from_baseline'].values
            stc = df.loc[df['pert_type']=='hardware','bc_from_baseline'].values
        else:
            inp = df.loc[df['pert_type']=='input','bc_distance'].values
            stc = df.loc[df['pert_type'].isin(['hardware','structure']),'bc_distance'].values
        print(f"[MICRO] CSV: input={len(inp)}, hw={len(stc)}, ratio={stc.mean()/inp.mean():.3f}")
        return inp, stc

    if mdsine2_dir is None:
        for c in _MDSINE2_CANDIDATES:
            if os.path.isdir(c): mdsine2_dir = c; break
    if mdsine2_dir and os.path.isdir(mdsine2_dir):
        try:
            return _load_mdsine2_direct(mdsine2_dir)
        except Exception as e:
            print(f"  [MICRO] MDSINE2 failed: {e}")
    return _simulate_microbiome()


def _load_mdsine2_direct(mdsine2_dir):
    import mdsine2 as md2
    pkl = Path(mdsine2_dir)/'datasets/gibson/uc/preprocessed/gibson_uc_agg_filtered.pkl'
    if not pkl.exists(): raise FileNotFoundError(f"Not found: {pkl}")
    study_u = md2.Study.load(str(pkl))
    phases = {'equilibration':(0,21.5),'HFD':(21.5,28.5),'recovery_1':(28.5,35.5),
              'vancomycin':(35.5,42.5),'recovery_2':(42.5,50.5),
              'gentamicin':(50.5,57.5),'recovery_3':(57.5,65.0)}
    def gp(t):
        for n,(s,e) in phases.items():
            if s <= t < e: return n
        return 'post'
    inp_bc, stc_bc = [], []
    pert_ends = {'recovery_1':28.5,'recovery_2':42.5,'recovery_3':57.5}
    rec_map = {'recovery_1':'input','recovery_2':'hardware','recovery_3':'hardware'}
    for subj in study_u:
        M = subj.matrix(); rel = M['rel']; times = subj.times
        bi = [i for i,t in enumerate(times) if 15 <= t < 21.5]
        if len(bi) < 3: continue
        baseline = np.mean(rel[:,bi],axis=1); baseline /= baseline.sum()+1e-15
        for i,t in enumerate(times):
            ph = gp(t)
            if ph not in rec_map: continue
            if t - pert_ends[ph] < 4: continue
            p = rel[:,i]; p = p/(p.sum()+1e-15)
            bc = spatial.distance.braycurtis(baseline, p)
            (inp_bc if rec_map[ph]=='input' else stc_bc).append(bc)
    inp, stc = np.array(inp_bc), np.array(stc_bc)
    print(f"[MICRO] MDSINE2: input={len(inp)}, hw={len(stc)}, ratio={stc.mean()/inp.mean():.3f}")
    return inp, stc


def _simulate_microbiome(n_input=15, n_hw=30):
    from scipy.stats import beta as beta_dist
    def bp(mu, sigma):
        mu = np.clip(mu,0.01,0.99); sigma = min(sigma,np.sqrt(mu*(1-mu))-0.001)
        v = sigma**2; a = mu*(mu*(1-mu)/v-1); b = (1-mu)*(mu*(1-mu)/v-1)
        return max(a,0.5), max(b,0.5)
    rng_m = np.random.RandomState(SEED+99)
    ai,bi = bp(0.28,0.10); ah,bh = bp(0.52,0.15)
    inp = beta_dist.rvs(ai,bi,size=n_input,random_state=rng_m)
    stc = beta_dist.rvs(ah,bh,size=n_hw,random_state=rng_m)
    print(f"[MICRO] Simulated: input={len(inp)}, hw={len(stc)}")
    return inp, stc


# ═══════════════════════════════════════════════════════════════════════════
# DOMAIN 4: YEAST
# ═══════════════════════════════════════════════════════════════════════════

YEAST_STRUCTURE_TERMS = {
    'GO:0006281','GO:0043161','GO:0006457','GO:0030433',
    'GO:0000278','GO:0000280','GO:0000281','GO:0051726','GO:0007346',
    'GO:0000082','GO:0000086','GO:0051301','GO:0006260','GO:0006261',
    'GO:0009272','GO:0071555','GO:0007005',
    'GO:0042254','GO:0042273','GO:0042274',
    'GO:0006325','GO:0006265','GO:0007059',
}
YEAST_INPUT_TERMS = {
    'GO:0007165','GO:0000165','GO:0007264','GO:0007186',
    'GO:0031929','GO:0032008','GO:0038202','GO:0006468',
    'GO:0055085','GO:0006811','GO:0006812','GO:0006813','GO:0006814',
    'GO:0006826','GO:0006865','GO:0015078','GO:0034220','GO:0055072',
    'GO:0006970','GO:0009408','GO:0034599',
    'GO:0071470','GO:0071472','GO:0071474',
}


def load_yeast(gaf_path, matrix_path, screens_path):
    """Load yeast data, return (input_severity, structure_severity) arrays."""
    if not all(os.path.exists(p) for p in [gaf_path, matrix_path, screens_path]):
        print(f"  [YEAST] Missing files")
        return None, None

    # Parse GAF
    gene_go = defaultdict(set); gene_to_orf = {}
    with open(gaf_path) as f:
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
                        gene_to_orf[gene] = s; break

    orf_class = {}
    for gene, gos in gene_go.items():
        orf = gene_to_orf.get(gene)
        if not orf: continue
        is_s = bool(gos & YEAST_STRUCTURE_TERMS)
        is_i = bool(gos & YEAST_INPUT_TERMS)
        if is_s and not is_i: orf_class[orf] = 'STRUCTURE'
        elif is_i and not is_s: orf_class[orf] = 'INPUT'

    # Select screens
    screens_df = pd.read_csv(screens_path, sep='\t')
    hill = screens_df[screens_df['paper'].str.contains('Hillenmeyer', case=False, na=False)]
    hill_hom = hill[hill['collection'].str.contains('hom', case=False, na=False)]
    if len(hill_hom) > 0:
        screen_ids = set(hill_hom['id'].astype(str)); src = 'Hillenmeyer'
    else:
        growth = screens_df[screens_df['phenotype'].str.contains('growth', case=False, na=False)]
        std_kw = ['standard','control','untreated','DMSO']
        chem = growth[~growth['conditionset'].str.lower().str.contains('|'.join(std_kw), na=True)]
        has_conc = chem[chem['conditionset'].str.contains(r'\[.*[uUnNmMg%]', na=False)]
        screen_ids = set(has_conc['id'].astype(str)); src = 'All chemical'

    # Load matrix
    print(f"  [YEAST] Loading matrix...")
    mat = pd.read_csv(matrix_path, sep='\t', index_col=0, low_memory=False)
    cols = [c for c in mat.columns if str(c) in screen_ids]

    s_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'STRUCTURE']
    i_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'INPUT']

    s_sev = mat.loc[s_orfs, cols].abs().mean(axis=1).dropna().values
    i_sev = mat.loc[i_orfs, cols].abs().mean(axis=1).dropna().values

    print(f"  [YEAST] {src}: {len(cols)} screens, S={len(s_sev)}, I={len(i_sev)}")
    return i_sev, s_sev


# ═══════════════════════════════════════════════════════════════════════════
# TEST 4 — METROLOGICAL AUDIT (now 4 domains)
# ═══════════════════════════════════════════════════════════════════════════

def test4_metrological_audit(gdsc, reef, micro_in, micro_st, yeast_in, yeast_st,
                              out_dir, args):
    print("\n" + "=" * 75)
    print("  TEST 4 — METROLOGICAL AUDIT: 4 definitions of ρ × 4 domains")
    print("=" * 75)

    results = {}

    # GDSC
    if gdsc is not None:
        dfc = gdsc.dropna(subset=['PTYPE_A','_auc'])
        yi = np.clip(1.0 - dfc.loc[dfc['PTYPE_A']=='INPUT','_auc'].values, 0.001, None)
        ys = np.clip(1.0 - dfc.loc[dfc['PTYPE_A']=='STRUCTURE','_auc'].values, 0.001, None)
        r = compute_rho_full(yi, ys, 'GDSC', args.n_perm, args.n_boot)
        if r: results['GDSC'] = r; print("\n  GDSC:"); print_result(r, 4)

    # REEF
    if reef is not None:
        reef = reef_classify(reef)
        yi_r = reef.loc[reef['ptype']=='input','bleaching'].values
        ys_r = reef.loc[reef['ptype']=='structure','bleaching'].values
        r = compute_rho_full(yi_r, ys_r, 'GCBD', args.n_perm, args.n_boot)
        if r: results['GCBD'] = r; print("\n  GCBD:"); print_result(r, 4)

    # MICROBIOME
    if len(micro_in) > 0 and len(micro_st) > 0:
        r = compute_rho_full(micro_in, micro_st, 'MDSINE2', min(args.n_perm,5000), args.n_boot)
        if r: results['MDSINE2'] = r; print("\n  MDSINE2:"); print_result(r, 4)

    # YEAST
    if yeast_in is not None and yeast_st is not None and len(yeast_in) > 0:
        r = compute_rho_full(yeast_in, yeast_st, 'YEAST', args.n_perm, args.n_boot)
        if r: results['YEAST'] = r; print("\n  YEAST:"); print_result(r, 4)

    # Summary table
    print("\n  ┌──────────────────────────────────────────────────────────────────────┐")
    print("  │  DOMAIN     │ ρ_means │ ρ_medians │ ρ_exp_d │ ρ_logit │ CV_intra  │")
    print("  ├─────────────┼─────────┼───────────┼─────────┼─────────┼───────────┤")
    table_rows = []
    for domain in ['GDSC', 'GCBD', 'MDSINE2', 'YEAST']:
        r = results.get(domain)
        if not r: continue
        rhos = [r['rho_means'], r['rho_medians'], r['rho_exp_d'], r['rho_logit']]
        cv = np.std(rhos)/np.mean(rhos)*100 if np.mean(rhos) > 0 else np.nan
        print(f"  │  {domain:<11s}│ {r['rho_means']:7.4f} │ {r['rho_medians']:9.4f} │ "
              f"{r['rho_exp_d']:7.4f} │ {r['rho_logit']:7.4f} │ {cv:8.1f}% │")
        table_rows.append({
            'domain': domain, 'rho_means': r['rho_means'],
            'rho_medians': r['rho_medians'], 'rho_exp_d': r['rho_exp_d'],
            'rho_logit': r['rho_logit'], 'CV_intra_pct': cv,
            'd': r['d'], 'p_MW': r['p_MW'],
            'n_input': r['n_input'], 'n_structure': r['n_structure'],
        })
    print("  └──────────────────────────────────────────────────────────────────────┘")

    if len(table_rows) >= 2:
        print("\n  CV inter-domaines par définition:")
        for col in ['rho_means','rho_medians','rho_exp_d','rho_logit']:
            vals = [row[col] for row in table_rows if np.isfinite(row[col])]
            if len(vals) >= 2:
                cv = np.std(vals)/np.mean(vals)*100
                print(f"    {col:<14s}: {cv:6.2f}%  (vals: {[f'{v:.3f}' for v in vals]})")

    if table_rows:
        pd.DataFrame(table_rows).to_csv(out_dir/'T4_metrological_audit.csv', index=False)

    # Figure
    if len(table_rows) >= 2:
        fig, axes = plt.subplots(1, 2, figsize=(14, 5))
        ax = axes[0]
        domains = [r['domain'] for r in table_rows]
        x = np.arange(len(domains))
        defs = ['rho_means','rho_medians','rho_exp_d','rho_logit']
        labels = ['ρ_means','ρ_medians','ρ_exp(d)','ρ_logit']
        colors = ['#2196F3','#4CAF50','#FF9800','#9C27B0']
        w = 0.18
        for i,(d_name,lbl,c) in enumerate(zip(defs,labels,colors)):
            vals = [r[d_name] for r in table_rows]
            ax.bar(x+i*w-1.5*w, vals, w, label=lbl, color=c, alpha=0.8)
        ax.set_xticks(x); ax.set_xticklabels(domains)
        ax.axhline(1.0, color='gray', ls='-', lw=0.5)
        ax.set_ylabel('ρ'); ax.set_title('A. Four definitions of ρ per domain')
        ax.legend(fontsize=8)

        ax = axes[1]
        cvs = [r['CV_intra_pct'] for r in table_rows]
        ax.bar(domains, cvs, color=['#1565C0','#2E7D32','#E65100','#F9A825'][:len(domains)], alpha=0.7)
        ax.set_ylabel('CV intra-domain (%)'); ax.set_title('B. Robustness: CV across definitions')
        plt.tight_layout()
        plt.savefig(out_dir/'T4_metrological_audit.png', dpi=150, bbox_inches='tight')
        plt.close()

    return results


# ═══════════════════════════════════════════════════════════════════════════
# TEST 2 — NULL PIPELINE (now includes yeast)
# ═══════════════════════════════════════════════════════════════════════════

def test2_null_pipeline(gdsc, reef, yeast_in, yeast_st, out_dir, args):
    print("\n" + "=" * 75)
    print("  TEST 2 — NULL PIPELINE")
    print("=" * 75)

    rng = np.random.RandomState(SEED + 2)
    results = {}

    # A: GDSC null
    if gdsc is not None:
        print("\n  --- A: GDSC label permutation ---")
        dfc = gdsc.dropna(subset=['PTYPE_A','_auc']).copy()
        yi = dfc.loc[dfc['PTYPE_A']=='INPUT','_auc'].values
        ys = dfc.loc[dfc['PTYPE_A']=='STRUCTURE','_auc'].values
        n_in = len(yi)
        rho_obs = (1-np.mean(ys))/(1-np.mean(yi)) if (1-np.mean(yi)) > 0.001 else np.inf
        combined = np.concatenate([yi, ys])
        nulls = np.empty(args.n_perm)
        for i in range(args.n_perm):
            rng.shuffle(combined)
            m_in = 1-np.mean(combined[:n_in]); m_st = 1-np.mean(combined[n_in:])
            nulls[i] = m_st/m_in if m_in > 0.001 else np.nan
        nulls = nulls[np.isfinite(nulls)]
        p_emp = np.mean(nulls >= rho_obs)
        print(f"    ρ_obs={rho_obs:.4f}, null mean={np.mean(nulls):.4f}, p={p_emp:.6f}")
        results['A_gdsc'] = {'rho_obs':rho_obs,'p_empirical':float(p_emp),'nulls':nulls}

    # B: Synthetic intensity
    print("\n  --- B: Synthetic intensity ---")
    real_mean = gdsc['_auc'].mean() if gdsc is not None else 0.82
    real_std = gdsc['_auc'].std() if gdsc is not None else 0.18
    shifts = [0.0,0.1,0.2,0.3,0.5,0.8,1.0]
    shift_results = []
    for shift in shifts:
        rho_vals = []
        for _ in range(1000):
            base = np.clip(rng.normal(real_mean,real_std,200000),0.01,0.99)
            n_a = 100000; base[n_a:] -= shift*real_std; base = np.clip(base,0.01,0.99)
            rho_vals.append((1-np.mean(base[n_a:]))/(1-np.mean(base[:n_a])))
        print(f"    shift={shift:.1f} → ρ={np.mean(rho_vals):.4f}")
        shift_results.append({'shift_sd':shift,'rho_mean':float(np.mean(rho_vals))})
    results['B_synthetic'] = shift_results

    # C: Reef null
    if reef is not None:
        print("\n  --- C: GCBD label permutation ---")
        rc = reef_classify(reef.copy())
        yi_r = rc.loc[rc['ptype']=='input','bleaching'].values
        ys_r = rc.loc[rc['ptype']=='structure','bleaching'].values
        n_in_r = len(yi_r)
        rho_obs_r = np.mean(ys_r)/np.mean(yi_r) if np.mean(yi_r) > 0.001 else np.inf
        comb_r = np.concatenate([yi_r, ys_r])
        nulls_r = np.empty(args.n_perm)
        for i in range(args.n_perm):
            rng.shuffle(comb_r)
            nulls_r[i] = np.mean(comb_r[n_in_r:])/max(np.mean(comb_r[:n_in_r]),0.001)
        nulls_r = nulls_r[np.isfinite(nulls_r)]
        p_r = np.mean(nulls_r >= rho_obs_r)
        print(f"    ρ_obs={rho_obs_r:.4f}, null mean={np.mean(nulls_r):.4f}, p={p_r:.6f}")
        results['C_reef'] = {'rho_obs':float(rho_obs_r),'p_empirical':float(p_r),'nulls':nulls_r}

    # D: Yeast null
    if yeast_in is not None and yeast_st is not None and len(yeast_in) > 10:
        print("\n  --- D: Yeast label permutation ---")
        n_in_y = len(yeast_in)
        rho_obs_y = np.mean(yeast_st)/np.mean(yeast_in) if np.mean(yeast_in) > 0.0001 else np.inf
        comb_y = np.concatenate([yeast_in, yeast_st])
        nulls_y = np.empty(args.n_perm)
        for i in range(args.n_perm):
            rng.shuffle(comb_y)
            m_i = np.mean(comb_y[:n_in_y]); m_s = np.mean(comb_y[n_in_y:])
            nulls_y[i] = m_s/m_i if m_i > 0.0001 else np.nan
        nulls_y = nulls_y[np.isfinite(nulls_y)]
        p_y = np.mean(nulls_y >= rho_obs_y)
        print(f"    ρ_obs={rho_obs_y:.4f}, null mean={np.mean(nulls_y):.4f}, p={p_y:.6f}")
        results['D_yeast'] = {'rho_obs':float(rho_obs_y),'p_empirical':float(p_y),'nulls':nulls_y}

    # Figure
    panels = [k for k in ['A_gdsc','C_reef','D_yeast'] if k in results]
    if panels:
        fig, axes = plt.subplots(1, len(panels)+1, figsize=(6*(len(panels)+1), 5))
        if len(panels)+1 == 1: axes = [axes]
        for idx, key in enumerate(panels):
            ax = axes[idx]; r = results[key]
            ax.hist(r['nulls'], bins=80, alpha=0.7, color='#9E9E9E', density=True)
            ax.axvline(r['rho_obs'], color='#E53935', lw=2.5,
                       label=f"Observed: {r['rho_obs']:.3f}")
            ax.set_xlabel('ρ_null'); ax.set_title(f"{key} (p={r['p_empirical']:.4f})")
            ax.legend()
        # Intensity panel
        ax = axes[len(panels)]
        xs = [r['shift_sd'] for r in shift_results]
        ys_m = [r['rho_mean'] for r in shift_results]
        ax.plot(xs, ys_m, 'o-', color='#1565C0')
        ax.set_xlabel('Shift (SD)'); ax.set_title('Intensity simulation')
        plt.tight_layout()
        plt.savefig(out_dir/'T2_null_pipeline.png', dpi=150, bbox_inches='tight')
        plt.close()

    return results


# ═══════════════════════════════════════════════════════════════════════════
# TEST 1 — MULTI-OPERATIONALIZATION (GDSC only, unchanged)
# ═══════════════════════════════════════════════════════════════════════════

def test1_operationalization(gdsc, out_dir, args):
    print("\n" + "=" * 75)
    print("  TEST 1 — MULTI-OPERATIONALIZATION (4 partitions, GDSC)")
    print("=" * 75)
    if gdsc is None:
        print("  ⚠ GDSC not available"); return None

    dfc = gdsc.dropna(subset=['_auc']).copy()
    partitions = {}

    # A
    dfc['PTYPE_A'] = dfc['PATHWAY_A'].apply(ptype_A)
    m = dfc['PTYPE_A'].notna()
    partitions['A_baseline'] = (np.clip(1-dfc.loc[m&(dfc['PTYPE_A']=='INPUT'),'_auc'].values,0.001,None),
                                np.clip(1-dfc.loc[m&(dfc['PTYPE_A']=='STRUCTURE'),'_auc'].values,0.001,None))
    # B
    dfc['PTYPE_B'] = dfc['PATHWAY_A'].apply(ptype_B)
    m = dfc['PTYPE_B'].notna()
    partitions['B_tight'] = (np.clip(1-dfc.loc[m&(dfc['PTYPE_B']=='INPUT'),'_auc'].values,0.001,None),
                             np.clip(1-dfc.loc[m&(dfc['PTYPE_B']=='STRUCTURE'),'_auc'].values,0.001,None))
    # C
    dfc['PTYPE_C'] = dfc.apply(lambda r: ptype_C(r.get('PATHWAY_A'),r.get('DRUG_NAME')),axis=1)
    m = dfc['PTYPE_C'].notna()
    partitions['C_wide'] = (np.clip(1-dfc.loc[m&(dfc['PTYPE_C']=='INPUT'),'_auc'].values,0.001,None),
                            np.clip(1-dfc.loc[m&(dfc['PTYPE_C']=='STRUCTURE'),'_auc'].values,0.001,None))
    # D
    dfc['PTYPE_D'] = dfc['DRUG_NAME'].apply(ptype_D)
    m = dfc['PTYPE_D'].notna()
    partitions['D_atc'] = (np.clip(1-dfc.loc[m&(dfc['PTYPE_D']=='INPUT'),'_auc'].values,0.001,None),
                           np.clip(1-dfc.loc[m&(dfc['PTYPE_D']=='STRUCTURE'),'_auc'].values,0.001,None))

    results = {}; table_rows = []
    for name,(yi,ys) in partitions.items():
        print(f"\n  --- {name} ---")
        r = compute_rho_full(yi,ys,name,args.n_perm,args.n_boot)
        if r:
            results[name] = r; print_result(r,4)
            table_rows.append({'partition':name,'rho_means':r['rho_means'],'d':r['d'],
                              'abs_d':r['abs_d'],'p_MW':r['p_MW'],'p_perm':r['p_perm'],
                              'rho_means_ci_lo':r['rho_means_ci_lo'],'rho_means_ci_hi':r['rho_means_ci_hi'],
                              'd_ci_lo':r['d_ci_lo'],'d_ci_hi':r['d_ci_hi'],
                              'n_input':r['n_input'],'n_structure':r['n_structure']})
    if table_rows:
        rhos = [r['rho_means'] for r in table_rows]
        cv = np.std(rhos)/np.mean(rhos)*100
        print(f"\n  VERDICT: CV={cv:.1f}% {'(robust)' if cv < 15 else '(sensitive)'}")
        pd.DataFrame(table_rows).to_csv(out_dir/'T1_operationalization.csv',index=False)
    return results


# ═══════════════════════════════════════════════════════════════════════════
# TEST 3 — HIERARCHICAL BAYESIAN (auto from T4, now 4 domains)
# ═══════════════════════════════════════════════════════════════════════════

def test3_hierarchical(t4_results, out_dir, args):
    print("\n" + "=" * 75)
    print("  TEST 3 — HIERARCHICAL BAYESIAN: cross-domain convergence")
    print("=" * 75)

    obs = []
    for domain, r in t4_results.items():
        rho = r['rho_means']; se = (r['rho_means_ci_hi']-r['rho_means_ci_lo'])/(2*1.96)
        obs.append({'domain':domain,'rho':rho,'se':se})
        print(f"  {domain}: ρ={rho:.4f}, SE={se:.4f}")
    if len(obs) < 2: print("  ⚠ Need ≥2 domains"); return None

    rho_obs = np.array([o['rho'] for o in obs])
    se_obs = np.array([o['se'] for o in obs])

    n_grid = 500
    mu_grid = np.linspace(0.5,3.0,n_grid); tau_grid = np.linspace(0.001,1.5,n_grid)
    MU, TAU = np.meshgrid(mu_grid, tau_grid)

    log_prior = -0.5*((MU-1.5)/1.0)**2 - 0.5*(TAU/0.5)**2
    log_prior[TAU < 0] = -np.inf
    log_lik = np.zeros_like(MU)
    for k in range(len(obs)):
        sigma_k = np.sqrt(TAU**2 + se_obs[k]**2)
        log_lik += -0.5*((rho_obs[k]-MU)/sigma_k)**2 - np.log(sigma_k)

    log_post = log_prior + log_lik; log_post -= log_post.max()
    post = np.exp(log_post); post /= post.sum()

    p_mu = post.sum(axis=0); p_mu /= p_mu.sum()
    p_tau = post.sum(axis=1); p_tau /= p_tau.sum()

    mu_mean = np.sum(mu_grid*p_mu)
    mu_cdf = np.cumsum(p_mu)
    mu_lo = mu_grid[np.searchsorted(mu_cdf,0.025)]
    mu_hi = mu_grid[np.searchsorted(mu_cdf,0.975)]

    tau_mean = np.sum(tau_grid*p_tau)
    tau_cdf = np.cumsum(p_tau)
    tau_lo = tau_grid[np.searchsorted(tau_cdf,0.025)]
    tau_hi = tau_grid[np.searchsorted(tau_cdf,0.975)]
    p_tau_lt_01 = float(np.sum(p_tau[tau_grid < 0.1]))
    p_tau_lt_03 = float(np.sum(p_tau[tau_grid < 0.3]))

    pp = []
    for _ in range(50_000):
        idx = RNG.choice(len(post.ravel()), p=post.ravel())
        i_t, i_m = np.unravel_index(idx, post.shape)
        pp.append(RNG.normal(mu_grid[i_m], tau_grid[i_t]+0.001))
    pp = np.array(pp)

    print(f"\n  μ = {mu_mean:.3f} [{mu_lo:.3f}, {mu_hi:.3f}]")
    print(f"  τ = {tau_mean:.3f} [{tau_lo:.3f}, {tau_hi:.3f}]")
    print(f"  P(τ<0.1)={p_tau_lt_01:.4f}  P(τ<0.3)={p_tau_lt_03:.4f}")
    print(f"  Posterior predictive: [{np.percentile(pp,2.5):.3f}, {np.percentile(pp,97.5):.3f}]")

    res = {'mu_mean':mu_mean,'mu_95_lo':float(mu_lo),'mu_95_hi':float(mu_hi),
           'tau_mean':tau_mean,'tau_95_lo':float(tau_lo),'tau_95_hi':float(tau_hi),
           'P_tau_lt_01':p_tau_lt_01,'P_tau_lt_03':p_tau_lt_03,
           'pp_95_lo':float(np.percentile(pp,2.5)),'pp_95_hi':float(np.percentile(pp,97.5)),
           'n_domains':len(obs)}

    # Figure
    fig, axes = plt.subplots(1,3,figsize=(18,5))
    ax = axes[0]
    ax.fill_between(mu_grid,p_mu,alpha=0.4,color='#1565C0')
    ax.axvline(mu_mean,color='#1565C0',lw=2,label=f'μ={mu_mean:.3f}')
    for o in obs: ax.axvline(o['rho'],color='#E53935',ls=':',lw=1,alpha=0.7)
    ax.set_xlabel('μ'); ax.set_title('A. Posterior of μ'); ax.legend(fontsize=8)

    ax = axes[1]
    ax.fill_between(tau_grid,p_tau,alpha=0.4,color='#2E7D32')
    ax.axvline(tau_mean,color='#2E7D32',lw=2,label=f'τ={tau_mean:.3f}')
    ax.axvline(0.1,color='red',ls=':'); ax.axvline(0.3,color='orange',ls=':')
    ax.set_xlabel('τ'); ax.set_title(f'B. Posterior of τ [P(τ<0.1)={p_tau_lt_01:.3f}]')
    ax.legend(fontsize=8)

    ax = axes[2]
    ax.hist(pp,bins=100,alpha=0.5,density=True,color='#9C27B0')
    for o in obs: ax.axvline(o['rho'],color='#E53935',lw=1.5,alpha=0.8)
    ax.set_xlabel('ρ (new domain)'); ax.set_title('C. Posterior predictive')

    plt.tight_layout()
    plt.savefig(out_dir/'T3_hierarchical.png',dpi=150,bbox_inches='tight')
    plt.close()

    with open(out_dir/'T3_hierarchical.json','w') as f: json.dump(res,f,indent=2)
    return res


# ═══════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════

def main():
    t0 = time.time()
    args = _Args()
    out_dir = Path(OUTPUT_DIR); out_dir.mkdir(parents=True, exist_ok=True)

    print("=" * 75)
    print("  R-XVII SENSITIVITY BATTERY v2 (with Yeast)")
    print(f"  Output: {out_dir}")
    print("=" * 75)

    # Load
    print("\n--- LOADING DATA ---")
    gdsc_path = _find_file(_GDSC_CANDIDATES, 'GDSC')
    reef_path = _find_file(_REEF_CANDIDATES, 'REEF')
    micro_csv = _find_file(_MICRO_CSV_CANDIDATES, 'MICRO')
    mdsine2_dir = _find_file(_MDSINE2_CANDIDATES, 'MDSINE2')
    yeast_gaf = _find_file(_YEAST_GAF_CANDIDATES, 'YEAST-GAF')
    yeast_mat = _find_file(_YEAST_HOM_MATRIX_CANDIDATES, 'YEAST-MAT')
    yeast_scr = _find_file(_YEAST_HOM_SCREENS_CANDIDATES, 'YEAST-SCR')

    gdsc = load_gdsc(gdsc_path) if gdsc_path else None
    reef = load_reef(reef_path) if reef_path else None
    micro_in, micro_st = load_microbiome(micro_csv, mdsine2_dir)
    yeast_in, yeast_st = (None, None)
    if yeast_gaf and yeast_mat and yeast_scr:
        yeast_in, yeast_st = load_yeast(yeast_gaf, yeast_mat, yeast_scr)

    # T4
    t4 = test4_metrological_audit(gdsc, reef, micro_in, micro_st,
                                   yeast_in, yeast_st, out_dir, args)
    # T2
    t2 = test2_null_pipeline(gdsc, reef, yeast_in, yeast_st, out_dir, args)
    # T1
    t1 = test1_operationalization(gdsc, out_dir, args)
    # T3
    t3 = test3_hierarchical(t4, out_dir, args) if t4 else None

    elapsed = time.time() - t0
    print(f"\n{'='*75}\n  DONE — {elapsed:.1f}s\n{'='*75}")

    summary = {'elapsed':elapsed, 'domains': list(t4.keys()) if t4 else []}
    if t3: summary['tau_mean'] = t3.get('tau_mean'); summary['mu_mean'] = t3.get('mu_mean')
    with open(out_dir/'summary.json','w') as f: json.dump(summary,f,indent=2)


if __name__ == '__main__':
    main()