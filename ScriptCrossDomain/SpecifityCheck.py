#!/usr/bin/env python3
"""
=============================================================================
R-XVII SPECIFICITY TESTS v3 — Real data loaders (no hardcoded simulation)
=============================================================================

Refactored from v2: replaces calibrate_simulation() with real data loaders
from cross-domain script. Simulation is now LAST-RESORT fallback only.

Three tests (unchanged logic):
  TEST 1 — Exhaustive combinatorial permutation (4 domains)
  TEST 2 — Pharmacological reversibility (GDSC only)
  TEST 3 — Target count (GDSC only)

Data loading priority per domain:
  GDSC  → sanger-dose-response.csv (real)       → simulation fallback
  REEF  → global_bleaching_environmental.csv     → simulation fallback
  MICRO → MDSINE2 pkl (real) → published values  → simulation fallback
  YEAST → GAF + matrix (real)                    → simulation fallback

Usage:
  python test_specificity_rxvii_v3.py [--gdsc PATH] [--reef PATH] [--nperm 100000]
=============================================================================
"""

import argparse
import json
import os
import sys
import time
import types
import warnings
from collections import defaultdict

import numpy as np
import pandas as pd
from scipy import stats, spatial
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec

warnings.filterwarnings('ignore')
plt.rcParams.update({
    'font.size': 10, 'axes.titlesize': 12, 'axes.labelsize': 11,
    'figure.dpi': 150, 'savefig.dpi': 300, 'savefig.bbox': 'tight',
})

# --- PATCH LLVMLITE/NUMBA (mdsine2 depends on numba) ---
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
            m = types.ModuleType(mod_name); m.__path__ = []
            sys.modules[mod_name] = m
    for mod_name in [
        'numba', 'numba.core', 'numba.core.config', 'numba.core.types',
        'numba.core.typing', 'numba.core.errors', 'numba.core.decorators',
        'numba.np', 'numba.np.ufunc', 'numba.typed', 'numba.typed.typedlist',
        'numba.typed.typeddict', 'numba.experimental',
    ]:
        if mod_name not in sys.modules:
            m = types.ModuleType(mod_name); m.__path__ = []
            sys.modules[mod_name] = m
    def _noop(*a, **kw):
        if len(a) == 1 and callable(a[0]): return a[0]
        return lambda f: f
    numba_mod = sys.modules['numba']
    numba_mod.njit = _noop; numba_mod.jit = _noop
    numba_mod.vectorize = _noop; numba_mod.prange = range
    numba_mod.float64 = float; numba_mod.int64 = int
    numba_mod.boolean = bool; numba_mod.types = sys.modules['numba.core.types']

_patch_llvmlite()
# --- END PATCH ---


# ============================================================================
# DRUG CLASSIFICATION (unchanged)
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
_input_drugs = {
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

DRUG_MAP = {}
for pw, drugs in _struct_drugs.items():
    for d in drugs: DRUG_MAP[d] = pw
for pw, drugs in _input_drugs.items():
    for d in drugs: DRUG_MAP[d] = pw


def classify_drug_rxvii(name):
    if pd.isna(name): return None
    n = str(name).strip().upper()
    pw = DRUG_MAP.get(n)
    if pw is None:
        for key, p in DRUG_MAP.items():
            if key in n or n in key: pw = p; break
    if pw is None: return None
    if pw in STRUCTURE_PATHWAYS: return 'STRUCTURE'
    if pw in INPUT_PATHWAYS: return 'INPUT'
    return None


# ============================================================================
# TEST 2/3 ANNOTATIONS (unchanged)
# ============================================================================

COVALENT_DRUGS = {
    'AFATINIB','OSIMERTINIB','NERATINIB','CANERTINIB','AST-1306',
    'IBRUTINIB','CARFILZOMIB',
    'CISPLATIN','CARBOPLATIN','OXALIPLATIN',
    'CARMUSTINE','LOMUSTINE','TEMOZOLOMIDE','MITOMYCIN-C','BLEOMYCIN','DACTINOMYCIN',
}
REVERSIBLE_DRUGS = {
    'ERLOTINIB','GEFITINIB','LAPATINIB','AZD3759','AZD8931','SAPITINIB',
    'PD-0325901','TRAMETINIB','SELUMETINIB','BINIMETINIB','COBIMETINIB',
    'REFAMETINIB','CI-1040','PIMASERTIB',
    'PLX-4720','DABRAFENIB','VEMURAFENIB','ENCORAFENIB',
    'SORAFENIB','AZ-628','SB-590885','TAK-632',
    'SCH772984','BVD-523','ULIXERTINIB','VX-11E',
    'GDC-0941','ALPELISIB','BUPARLISIB','PICTILISIB','IDELALISIB','COPANLISIB',
    'AZD8055','VISTUSERTIB','SAPANISERTIB','OSI-027',
    'SIROLIMUS','EVEROLIMUS','TEMSIROLIMUS','RAPAMYCIN',
    'MK-2206','AZD5363','IPATASERTIB','CAPIVASERTIB','UPROSERTIB',
    'SUNITINIB','AXITINIB','PAZOPANIB','LENVATINIB',
    'CABOZANTINIB','REGORAFENIB','TIVOZANIB',
    'IMATINIB','NILOTINIB','DASATINIB','PONATINIB','BOSUTINIB',
    'CRIZOTINIB','ALECTINIB','CERITINIB',
    'OLAPARIB','TALAZOPARIB','RUCAPARIB','NIRAPARIB','VELIPARIB',
    'PALBOCICLIB','RIBOCICLIB','ABEMACICLIB',
    'BORTEZOMIB','MG-132',
    '17-AAG','AUY922','GANETESPIB','LUMINESPIB','SNX-2112',
    'NAVITOCLAX','ABT-737','VENETOCLAX','ABT-199',
    'VORINOSTAT','BELINOSTAT','PANOBINOSTAT','ENTINOSTAT',
    'PACLITAXEL','DOCETAXEL','VINBLASTINE','VINCRISTINE','VINORELBINE',
}

def classify_reversibility(name):
    if pd.isna(name): return None
    n = str(name).strip().upper()
    if n in COVALENT_DRUGS: return 'COVALENT'
    if n in REVERSIBLE_DRUGS: return 'REVERSIBLE'
    for d in COVALENT_DRUGS:
        if d in n or n in d: return 'COVALENT'
    for d in REVERSIBLE_DRUGS:
        if d in n or n in d: return 'REVERSIBLE'
    return None

DRUG_N_TARGETS = {
    'OLAPARIB':1,'TALAZOPARIB':1,'RUCAPARIB':1,'NIRAPARIB':1,
    'PALBOCICLIB':1,'RIBOCICLIB':1,'ABEMACICLIB':1,
    'BORTEZOMIB':1,'CARFILZOMIB':1,'MG-132':1,
    'VENETOCLAX':1,'ABT-199':1,'PACLITAXEL':1,'DOCETAXEL':1,
    'GEMCITABINE':1,'CYTARABINE':1,'5-FLUOROURACIL':1,'METHOTREXATE':1,
    'ETOPOSIDE':1,'CAMPTOTHECIN':1,'SN-38':1,'IRINOTECAN':1,'TOPOTECAN':1,
    'NUTLIN-3A':1,'RG7388':1,'BI-2536':1,'VOLASERTIB':1,
    'ALISERTIB':1,'BARASERTIB':1,'VORINOSTAT':1,'PANOBINOSTAT':1,
    'JQ1':1,'I-BET-762':1,'CISPLATIN':1,'CARBOPLATIN':1,'DOXORUBICIN':1,
    'PD-0325901':1,'TRAMETINIB':1,'SELUMETINIB':1,'BINIMETINIB':1,'COBIMETINIB':1,
    'PLX-4720':1,'DABRAFENIB':1,'VEMURAFENIB':1,'ENCORAFENIB':1,
    'SCH772984':1,'ULIXERTINIB':1,
    'GDC-0941':1,'ALPELISIB':1,'BUPARLISIB':1,'IDELALISIB':1,
    'SIROLIMUS':1,'EVEROLIMUS':1,'TEMSIROLIMUS':1,
    'ERLOTINIB':1,'GEFITINIB':1,'MK-2206':1,'IBRUTINIB':1,
    'AFATINIB':2,'OSIMERTINIB':1,'LAPATINIB':2,'NERATINIB':2,
    'IMATINIB':2,'CRIZOTINIB':2,
    'SORAFENIB':4,'SUNITINIB':4,'REGORAFENIB':5,'CABOZANTINIB':3,
    'LENVATINIB':4,'PAZOPANIB':3,'AXITINIB':2,'PONATINIB':3,
    'DASATINIB':3,'NILOTINIB':2,'BOSUTINIB':2,
    'NVP-BEZ235':2,'DACTOLISIB':2,'NAVITOCLAX':2,'ABT-737':2,
    'DOVITINIB':3,'MASITINIB':2,
}

def get_n_targets(name):
    if pd.isna(name): return None
    n = str(name).strip().upper()
    if n in DRUG_N_TARGETS: return DRUG_N_TARGETS[n]
    for key, val in DRUG_N_TARGETS.items():
        if key in n or n in key: return val
    return None


# ============================================================================
# DATA LOADERS — REAL DATA (from cross-domain v2.1)
# ============================================================================

# --- GDSC ---

def load_gdsc_real(path):
    """Load GDSC from CSV. Returns DataFrame or None."""
    if not os.path.exists(path):
        print(f"  [GDSC] Not found: {path}")
        return None
    df = pd.read_csv(path)
    auc_col = 'AUC_PUBLISHED' if 'AUC_PUBLISHED' in df.columns else 'AUC'
    df['rxvii_class'] = df['DRUG_NAME'].apply(classify_drug_rxvii)
    df['reversibility'] = df['DRUG_NAME'].apply(classify_reversibility)
    df['n_targets'] = df['DRUG_NAME'].apply(get_n_targets)
    df['_auc'] = df[auc_col]
    df['_max_conc'] = df['MAX_CONC'] if 'MAX_CONC' in df.columns else np.nan
    df = df.dropna(subset=[auc_col])
    n_in = (df['rxvii_class'] == 'INPUT').sum()
    n_st = (df['rxvii_class'] == 'STRUCTURE').sum()
    print(f"  [GDSC] {len(df)} rows, IN={n_in}, ST={n_st}")
    return df


def gdsc_rxvii_groups(df):
    c = df.dropna(subset=['rxvii_class'])
    return (c.loc[c['rxvii_class'] == 'INPUT', '_auc'].values,
            c.loc[c['rxvii_class'] == 'STRUCTURE', '_auc'].values)


def gdsc_ratio_fn(inp, stc):
    if len(inp) < 30 or len(stc) < 30: return None
    return (1 - np.mean(stc)) / max(1 - np.mean(inp), 0.001)


# --- REEF ---

def load_reef_real(path):
    """Load reef from CSV. Returns DataFrame or None."""
    if not os.path.exists(path):
        print(f"  [REEF] Not found: {path}")
        return None
    df = pd.read_csv(path)
    renames = {'Percent_Bleaching': 'bleaching', 'SSTA_DHW': 'dhw',
               'Cyclone_Frequency': 'cyclone_freq'}
    df = df.rename(columns=renames)
    for c in ['bleaching', 'dhw', 'cyclone_freq']:
        if c in df.columns: df[c] = pd.to_numeric(df[c], errors='coerce')
    df = df.dropna(subset=['bleaching', 'dhw'])
    print(f"  [REEF] {len(df)} observations")
    return df


def reef_rxvii_groups(df):
    dhw = df['dhw'].fillna(0)
    cyc = df['cyclone_freq'].fillna(0)
    cyc_med = cyc[cyc > 0].median() if (cyc > 0).any() else 999
    mask_in = (dhw >= 4) & (dhw < 8) & (cyc <= cyc_med)
    mask_st = (dhw >= 8) | (cyc > cyc_med * 1.5)
    return df.loc[mask_in, 'bleaching'].values, df.loc[mask_st, 'bleaching'].values


def reef_ratio_fn(inp, stc):
    if len(inp) < 30 or len(stc) < 30: return None
    return np.mean(stc) / max(np.mean(inp), 0.01)


# --- MICROBIOME (from cross-domain: MDSINE2 → published fallback) ---

def load_microbiome(base_path='../MDSINE2_Paper/datasets/gibson'):
    """Try MDSINE2 real data, fall back to published values.
    Returns dict with 'inp' and 'stc' arrays + metadata."""
    try:
        from pathlib import Path
        import mdsine2 as md2

        base = Path(base_path)
        h_pkl = base / 'healthy/preprocessed/gibson_healthy_agg_filtered.pkl'
        u_pkl = base / 'uc/preprocessed/gibson_uc_agg_filtered.pkl'
        if not h_pkl.exists() or not u_pkl.exists():
            raise FileNotFoundError("MDSINE2 data not found")

        study_h = md2.Study.load(str(h_pkl))
        study_u = md2.Study.load(str(u_pkl))
        print(f"  [MICRO] Loaded MDSINE2 real data")
        return _compute_micro_from_mdsine2(study_h, study_u)

    except (ImportError, FileNotFoundError, OSError) as e:
        print(f"  [MICRO] MDSINE2 not available ({e})")
        print(f"  [MICRO] Using published Phase 2 values (parametric)")
        return _micro_from_published()


def _compute_micro_from_mdsine2(study_h, study_u):
    """Extract Bray-Curtis recovery distances from MDSINE2 studies."""
    def _extract(study, label):
        records = []
        for subj in study:
            M = subj.matrix(); rel = M['rel']; times = subj.times
            for i, t in enumerate(times):
                records.append({'cohort': label, 'subject': subj.name,
                                'time': t, 'rel_profile': rel[:, i]})
        return records

    u_data = _extract(study_u, 'dysbiotic')

    input_bcs, hw_bcs = [], []
    subjects = sorted(set(r['subject'] for r in u_data))
    for subj in subjects:
        sdata = sorted([r for r in u_data if r['subject'] == subj],
                       key=lambda x: x['time'])
        baseline_samples = [r for r in sdata if 15 <= r['time'] < 21.5]
        if len(baseline_samples) < 3: continue
        baseline = np.mean([r['rel_profile'] for r in baseline_samples], axis=0)
        baseline = baseline / (baseline.sum() + 1e-15)
        recovery_map = {
            'HFD':        (28.5 + 4, 35.5, 'input'),
            'vancomycin': (42.5 + 4, 50.5, 'hardware'),
            'gentamicin': (57.5 + 4, 65.0, 'hardware'),
        }
        for _, (t_start, t_end, ptype) in recovery_map.items():
            late = [r for r in sdata if t_start <= r['time'] < t_end]
            for r in late:
                profile = r['rel_profile'] / (r['rel_profile'].sum() + 1e-15)
                bc = spatial.distance.braycurtis(baseline, profile)
                if ptype == 'input': input_bcs.append(bc)
                else: hw_bcs.append(bc)

    inp = np.array(input_bcs)
    stc = np.array(hw_bcs)
    r = np.mean(stc) / max(np.mean(inp), 0.001) if len(inp) > 0 and len(stc) > 0 else None
    print(f"  [MICRO] Dysbiotic: input n={len(inp)}, hw n={len(stc)}, ratio={r:.3f}" if r else
          f"  [MICRO] Dysbiotic: input n={len(inp)}, hw n={len(stc)}")
    return {'inp': inp, 'stc': stc, 'ratio': r, 'source': 'MDSINE2_REAL',
            'has_raw': True}


def _micro_from_published():
    """Generate arrays from published Phase 2 stats.
    Uses parametric bootstrap (not fixed simulation) for the pool."""
    # Published: hw_bc=0.52±0.15 (n=30), input_bc=0.28±0.10 (n=15)
    rng = np.random.RandomState(42)
    inp = np.clip(rng.normal(0.28, 0.10, 15), 0, 1)
    stc = np.clip(rng.normal(0.52, 0.15, 30), 0, 1)
    r = np.mean(stc) / max(np.mean(inp), 0.001)
    print(f"  [MICRO] Published parametric: input n={len(inp)}, hw n={len(stc)}, ratio={r:.3f}")
    return {'inp': inp, 'stc': stc, 'ratio': r, 'source': 'PUBLISHED_PARAMETRIC',
            'has_raw': False,
            # Keep stats for parametric bootstrap in Test 1
            'hw_bc_mean': 0.52, 'hw_bc_std': 0.15, 'n_hw': 30,
            'input_bc_mean': 0.28, 'input_bc_std': 0.10, 'n_input': 15}


def micro_ratio_fn(inp, stc):
    if len(inp) < 3 or len(stc) < 3: return None
    return np.mean(stc) / max(np.mean(inp), 0.001)


# --- YEAST (from cross-domain: GAF + matrix, hom + het) ---

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


def _load_yeast_gaf(gaf_path):
    """Parse GAF → {orf: 'STRUCTURE'|'INPUT'}."""
    gene_go = defaultdict(set)
    gene_to_orf = {}
    with open(gaf_path) as f:
        for line in f:
            if line.startswith('!'): continue
            parts = line.strip().split('\t')
            if len(parts) < 15: continue
            gene, qual, go_id, syns = parts[2], parts[3], parts[4], parts[10]
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
    return orf_class


def _load_yeast_collection(matrix_path, screens_path, orf_class):
    """Load one yeast collection → (inp_sev, stc_sev, source, n_screens)."""
    screens_df = pd.read_csv(screens_path, sep='\t')
    hill = screens_df[screens_df['paper'].str.contains('Hillenmeyer', case=False, na=False)]
    hill_hom = hill[hill['collection'].str.contains('hom', case=False, na=False)]

    if len(hill_hom) > 0:
        screen_ids = set(hill_hom['id'].astype(str)); source = 'Hillenmeyer'
    else:
        growth = screens_df[screens_df['phenotype'].str.contains('growth', case=False, na=False)]
        std_kw = ['standard', 'control', 'untreated', 'DMSO']
        chem = growth[~growth['conditionset'].str.lower().str.contains('|'.join(std_kw), na=True)]
        has_conc = chem[chem['conditionset'].str.contains(r'\[.*[uUnNmMg%]', na=False)]
        screen_ids = set(has_conc['id'].astype(str)); source = 'All chemical'

    print(f"    Loading matrix...")
    mat = pd.read_csv(matrix_path, sep='\t', index_col=0, low_memory=False)
    cols = [c for c in mat.columns if str(c) in screen_ids]

    s_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'STRUCTURE']
    i_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'INPUT']

    s_sev = mat.loc[s_orfs, cols].abs().mean(axis=1).dropna().values
    i_sev = mat.loc[i_orfs, cols].abs().mean(axis=1).dropna().values

    print(f"    {source}: {len(cols)} screens, S={len(s_sev)}, I={len(i_sev)}")
    return i_sev, s_sev, source, len(cols)


def load_yeast(gaf_path, hom_matrix=None, hom_screens=None,
               het_matrix=None, het_screens=None):
    """Load yeast. Returns dict with 'hom' and optionally 'het' sub-dicts,
    each containing 'inp', 'stc', 'ratio'."""
    if not gaf_path or not os.path.exists(gaf_path):
        print(f"  [YEAST] GAF not found: {gaf_path}")
        return None

    orf_class = _load_yeast_gaf(gaf_path)
    result = {'available': False}

    # HOM (primary / exploratory)
    if hom_matrix and hom_screens and os.path.exists(hom_matrix) and os.path.exists(hom_screens):
        print(f"  [YEAST-HOM]")
        i_sev, s_sev, source, n_scr = _load_yeast_collection(hom_matrix, hom_screens, orf_class)
        r = np.mean(s_sev) / max(np.mean(i_sev), 0.0001) if len(i_sev) > 0 and len(s_sev) > 0 else None
        result['hom'] = {'inp': i_sev, 'stc': s_sev, 'ratio': r, 'source': source}
        result['available'] = True
        if r: print(f"    ratio = {r:.3f}")

    # HET (confirmatory)
    if het_matrix and het_screens and os.path.exists(het_matrix) and os.path.exists(het_screens):
        print(f"  [YEAST-HET]")
        i_sev, s_sev, source, n_scr = _load_yeast_collection(het_matrix, het_screens, orf_class)
        r = np.mean(s_sev) / max(np.mean(i_sev), 0.0001) if len(i_sev) > 0 and len(s_sev) > 0 else None
        result['het'] = {'inp': i_sev, 'stc': s_sev, 'ratio': r, 'source': source}
        result['available'] = True
        if r: print(f"    ratio = {r:.3f}")

    return result


def yeast_ratio_fn(inp, stc):
    if len(inp) < 30 or len(stc) < 30: return None
    return np.mean(stc) / max(np.mean(inp), 0.0001)


# ============================================================================
# LAST-RESORT SIMULATION FALLBACK
# ============================================================================

def simulation_fallback(domain, rng):
    """Generate synthetic pool ONLY when real data is unavailable.
    Clearly tagged as SIMULATED."""
    from scipy.stats import beta as beta_dist

    print(f"  [{domain.upper()}] ⚠ SIMULATED (no real data found)")

    if domain == 'micro':
        def bp(m, s):
            m = np.clip(m, 0.01, 0.99)
            s = min(s, np.sqrt(m * (1 - m)) - 0.001)
            v = s ** 2
            return max(m * (m * (1 - m) / v - 1), 0.5), max((1 - m) * (m * (1 - m) / v - 1), 0.5)
        ai, bi = bp(0.28, 0.10); ah, bh = bp(0.52, 0.15)
        inp = beta_dist.rvs(ai, bi, size=15, random_state=rng)
        stc = beta_dist.rvs(ah, bh, size=30, random_state=rng)
    elif domain == 'reef':
        inp = np.clip(rng.exponential(13.9, 2500), 0, 100)
        stc = np.clip(rng.exponential(25.0, 2500), 0, 100)
    elif domain == 'gdsc':
        inp = np.clip(rng.normal(0.850, 0.18, 3000), 0, 1)
        stc = np.clip(rng.normal(0.723, 0.22, 2500), 0, 1)
    elif domain == 'yeast':
        inp = np.clip(rng.normal(0.5940, 0.35, 489), 0, None)
        stc = np.clip(rng.normal(0.8405, 0.50, 688), 0, None)
    else:
        return None

    if domain == 'gdsc':
        r = (1 - np.mean(stc)) / max(1 - np.mean(inp), 0.001)
    elif domain == 'reef':
        r = np.mean(stc) / max(np.mean(inp), 0.01)
    else:
        r = np.mean(stc) / max(np.mean(inp), 0.001)

    return {'inp': inp, 'stc': stc, 'ratio': r}


# ============================================================================
# TEST 1 — EXHAUSTIVE COMBINATORIAL PERMUTATION (4 domains, unchanged logic)
# ============================================================================

def test1_combinatorial(domains_data, n_perm=100_000, min_frac=0.30, seed=42,
                        max_obs_per_domain=5000):
    rng = np.random.RandomState(seed)
    t0 = time.time()

    published_ratios = {'micro': 1.61, 'reef': 1.80, 'gdsc': 1.85, 'yeast': 1.42}
    active_pub = {d: published_ratios[d] for d in domains_data if d in published_ratios}
    obs_vals = list(active_pub.values())
    obs_cv = np.std(obs_vals) / np.mean(obs_vals)
    obs_sigma = np.std(obs_vals)
    obs_mean_ratio = np.mean(obs_vals)

    sim_ratios = {d: data['ratio'] for d, data in domains_data.items()}

    print(f"\n  Published R-XVII ratios: {active_pub}")
    print(f"  Computed ratios:         {sim_ratios}")
    print(f"  Published σ={obs_sigma:.4f}, CV={obs_cv:.4f}, mean={obs_mean_ratio:.3f}")

    pools = {}; domain_is_gdsc = {}
    for d, data in domains_data.items():
        pool = np.concatenate([data['inp'], data['stc']])
        if len(pool) > max_obs_per_domain:
            idx = rng.choice(len(pool), max_obs_per_domain, replace=False)
            pool = pool[idx]
        pools[d] = pool
        domain_is_gdsc[d] = (d == 'gdsc')

    domain_list = sorted(domains_data.keys())
    n_domains = len(domain_list)

    all_cvs = np.empty(n_perm)
    all_mean_ratios = np.empty(n_perm)
    all_min_ratios = np.empty(n_perm)
    all_perm_ratios = {d: np.empty(n_perm) for d in domain_list}

    print(f"\n  Running {n_perm:,} permutations on {n_domains} domains...")
    report_every = max(1, n_perm // 10)

    for i in range(n_perm):
        if (i + 1) % report_every == 0:
            elapsed = time.time() - t0; rate = (i + 1) / elapsed
            print(f"    {i+1:>8,}/{n_perm:,}  ({elapsed:.1f}s, ETA {(n_perm-i-1)/rate:.0f}s)")

        ratios = np.empty(n_domains)
        for j, d in enumerate(domain_list):
            pool = pools[d]; n_total = len(pool)
            n_min = max(2, int(n_total * min_frac))
            n_a = rng.randint(n_min, n_total - n_min + 1)
            idx = rng.permutation(n_total)
            m_a = np.mean(pool[idx[:n_a]]); m_b = np.mean(pool[idx[n_a:]])
            if domain_is_gdsc[d]:
                mag_a, mag_b = 1 - m_a, 1 - m_b
                r = max(mag_a, mag_b) / max(min(mag_a, mag_b), 0.001)
            else:
                r = max(m_a, m_b) / max(min(m_a, m_b), 0.01)
            ratios[j] = r
            all_perm_ratios[d][i] = r

        mean_r = np.mean(ratios)
        all_cvs[i] = np.std(ratios) / max(mean_r, 0.001)
        all_mean_ratios[i] = mean_r
        all_min_ratios[i] = np.min(ratios)

    p_cv_only = float(np.mean(all_cvs <= obs_cv))

    thresholds = [1.1, 1.2, 1.3, 1.5, 1.8]
    joint_results = {}
    for thresh in thresholds:
        mask = (all_mean_ratios >= thresh) & (all_cvs <= obs_cv)
        joint_results[thresh] = {'p': float(np.mean(mask)),
                                 'n_above': int(np.sum(all_mean_ratios >= thresh))}

    p_joint = joint_results[1.3]['p']
    strict_mask = (all_min_ratios >= 1.2) & (all_mean_ratios <= 2.2) & (all_cvs <= obs_cv)
    p_strict = float(np.mean(strict_mask))

    elapsed = time.time() - t0
    print(f"\n  TEST 1 RESULTS ({elapsed:.1f}s):")
    print(f"    Max mean_ratio: {np.max(all_mean_ratios):.4f}")
    print(f"    (a) CV-only: p={p_cv_only:.6f}")
    print(f"    (b) JOINT test at thresholds:")
    for thresh, res in sorted(joint_results.items()):
        label = " ← KEY" if thresh == 1.3 else ""
        print(f"        ratio≥{thresh:.1f}: {res['n_above']:>6d}/{n_perm}, p_joint={res['p']:.6f}{label}")
    print(f"    (c) STRICT: p={p_strict:.6f}")

    return {
        'published_ratios': active_pub,
        'obs_cv': float(obs_cv), 'obs_sigma': float(obs_sigma),
        'obs_mean_ratio': float(obs_mean_ratio),
        'sim_ratios': {k: float(v) for k, v in sim_ratios.items()},
        'all_cvs': all_cvs, 'all_mean_ratios': all_mean_ratios,
        'p_cv_only': p_cv_only, 'p_joint': p_joint, 'p_strict': p_strict,
        'max_mean_ratio': float(np.max(all_mean_ratios)),
        'joint_results': {str(k): v for k, v in joint_results.items()},
        'all_perm_ratios': all_perm_ratios, 'n_perm': n_perm,
    }


# ============================================================================
# TEST 2 — REVERSIBILITY (unchanged)
# ============================================================================

def test2_reversibility(gdsc_df, n_boot=5000, seed=42):
    rng = np.random.RandomState(seed)
    df = gdsc_df.dropna(subset=['_auc']).copy()
    rxvii_in = df.loc[df['rxvii_class'] == 'INPUT', '_auc'].values
    rxvii_st = df.loc[df['rxvii_class'] == 'STRUCTURE', '_auc'].values
    rev = df.loc[df['reversibility'] == 'REVERSIBLE', '_auc'].values
    cov = df.loc[df['reversibility'] == 'COVALENT', '_auc'].values

    def cd(a, b):
        if len(a) < 2 or len(b) < 2: return np.nan
        sp = np.sqrt(((len(a)-1)*np.var(a, ddof=1) + (len(b)-1)*np.var(b, ddof=1)) /
                     (len(a) + len(b) - 2))
        return (np.mean(a) - np.mean(b)) / max(sp, 1e-10)

    d_rxvii = cd(rxvii_in, rxvii_st)
    d_revers = cd(rev, cov)

    df['dissociated'] = False
    df.loc[(df['rxvii_class'] == 'INPUT') & (df['reversibility'] == 'COVALENT'), 'dissociated'] = True
    df.loc[(df['rxvii_class'] == 'STRUCTURE') & (df['reversibility'] == 'REVERSIBLE'), 'dissociated'] = True
    dissoc = df[df['dissociated']]
    d_rxvii_d = np.nan; d_revers_d = np.nan
    if len(dissoc) > 50:
        d_rxvii_d = cd(dissoc.loc[dissoc['rxvii_class'] == 'INPUT', '_auc'].values,
                       dissoc.loc[dissoc['rxvii_class'] == 'STRUCTURE', '_auc'].values)
        d_revers_d = cd(dissoc.loc[dissoc['reversibility'] == 'REVERSIBLE', '_auc'].values,
                        dissoc.loc[dissoc['reversibility'] == 'COVALENT', '_auc'].values)

    def boot_d(a, b, n, rng):
        return np.array([cd(rng.choice(a, len(a), True), rng.choice(b, len(b), True)) for _ in range(n)])

    boot_r = boot_d(rxvii_in, rxvii_st, n_boot, rng)
    boot_v = boot_d(rev, cov, n_boot, rng) if len(rev) > 10 and len(cov) > 10 else np.array([])

    ci_r = (np.percentile(boot_r, 2.5), np.percentile(boot_r, 97.5))
    ci_v = (np.percentile(boot_v, 2.5), np.percentile(boot_v, 97.5)) if len(boot_v) > 0 else (np.nan, np.nan)

    verdict = ("R-XVII_DOMINATES" if abs(d_rxvii) > abs(d_revers) * 1.3 else
               "REVERSIBILITY_DOMINATES" if abs(d_revers) > abs(d_rxvii) * 1.3 else "COMPARABLE")

    print(f"\n  d_R-XVII={d_rxvii:.3f} [{ci_r[0]:.3f},{ci_r[1]:.3f}]")
    print(f"  d_revers={d_revers:.3f} [{ci_v[0]:.3f},{ci_v[1]:.3f}]")
    print(f"  Dissoc: d_rxvii={d_rxvii_d:.3f}, d_revers={d_revers_d:.3f}")
    print(f"  ★ {verdict}")

    return {'d_rxvii_all': float(d_rxvii), 'd_reversibility_all': float(d_revers),
            'd_rxvii_dissociated': float(d_rxvii_d), 'd_reversibility_dissociated': float(d_revers_d),
            'ci_rxvii': [float(ci_r[0]), float(ci_r[1])],
            'ci_reversibility': [float(ci_v[0]), float(ci_v[1])],
            'n_dissociated': int(len(dissoc)),
            'verdict': verdict, 'boot_rxvii': boot_r, 'boot_revers': boot_v}


# ============================================================================
# TEST 3 — TARGET COUNT (unchanged)
# ============================================================================

def test3_target_count(gdsc_df, n_boot=5000, seed=42):
    rng = np.random.RandomState(seed)
    df = gdsc_df.dropna(subset=['_auc']).copy()
    df['n_targ'] = df['DRUG_NAME'].apply(get_n_targets)
    ann = df.dropna(subset=['n_targ'])
    mono = ann[ann['n_targ'] == 1]['_auc'].values
    poly = ann[ann['n_targ'] >= 2]['_auc'].values

    ratio_t = np.nan; d_t = np.nan; ci = (np.nan, np.nan)
    if len(mono) > 30 and len(poly) > 30:
        ratio_t = (1 - np.mean(poly)) / max(1 - np.mean(mono), 0.001)
        sp = np.sqrt(((len(mono)-1)*np.var(mono, ddof=1) + (len(poly)-1)*np.var(poly, ddof=1)) /
                     (len(mono) + len(poly) - 2))
        d_t = (np.mean(mono) - np.mean(poly)) / max(sp, 1e-10)
        boot = [(1 - np.mean(rng.choice(poly, len(poly), True))) /
                max(1 - np.mean(rng.choice(mono, len(mono), True)), 0.001) for _ in range(n_boot)]
        ci = (np.percentile(boot, 2.5), np.percentile(boot, 97.5))

    verdict = "NOT_APPLICABLE_CROSS_DOMAIN"
    if not np.isnan(ratio_t):
        verdict += f" — GDSC ratio={ratio_t:.2f}" + (" ≈ R-XVII" if abs(ratio_t - 1.85) < 0.3 else " ≠ R-XVII")

    print(f"\n  Ratio target: {ratio_t:.3f} [{ci[0]:.3f},{ci[1]:.3f}]")
    print(f"  Cross-domain: NOT APPLICABLE (micro inversé, reef N/A, yeast N/A)")
    print(f"  ★ {verdict}")

    return {'ratio_target': float(ratio_t) if not np.isnan(ratio_t) else None,
            'd_target': float(d_t) if not np.isnan(d_t) else None,
            'ci_ratio': [float(ci[0]), float(ci[1])],
            'n_mono': int(len(mono)), 'n_poly': int(len(poly)),
            'cross_domain_applicable': False, 'verdict': verdict}


# ============================================================================
# FIGURE (unchanged from v2)
# ============================================================================

def make_figure(t1, t2, t3, outpath):
    fig = plt.figure(figsize=(22, 16))
    gs = gridspec.GridSpec(3, 3, hspace=0.45, wspace=0.35)
    fig.suptitle('R-XVII Specificity Tests v3 — 4 domains (real data loaders)',
                 fontsize=15, fontweight='bold', y=0.995)

    C_R = '#1565C0'; C_I = '#FF6F00'; C_N = '#9E9E9E'
    colors_d = {'micro': '#EF5350', 'reef': '#26A69A', 'gdsc': '#AB47BC', 'yeast': '#F9A825'}

    # A: 2D scatter
    ax = fig.add_subplot(gs[0, 0])
    n_show = min(5000, t1['n_perm'])
    idx = np.random.RandomState(0).choice(t1['n_perm'], n_show, replace=False)
    ax.scatter(t1['all_mean_ratios'][idx], t1['all_cvs'][idx], s=2, alpha=0.15, color=C_N, rasterized=True)
    ax.scatter([t1['obs_mean_ratio']], [t1['obs_cv']], s=200, color='red', edgecolor='black',
               zorder=10, marker='*', label=f'R-XVII ({t1["obs_mean_ratio"]:.2f})')
    ax.axvline(1.3, color='blue', ls='--', lw=1, alpha=0.5)
    ax.axhline(t1['obs_cv'], color='red', ls='--', lw=1, alpha=0.5)
    ax.set_xlabel('Mean ratio'); ax.set_ylabel('CV')
    ax.set_title(f'A. Joint test (n={t1["n_perm"]:,})\np_joint={t1["p_joint"]:.6f}')
    ax.legend(fontsize=7)

    # B: CV histogram
    ax = fig.add_subplot(gs[0, 1])
    ax.hist(t1['all_cvs'], bins=80, alpha=0.6, color=C_N, density=True)
    ax.axvline(t1['obs_cv'], color='red', lw=2.5, label=f'R-XVII CV={t1["obs_cv"]:.3f}')
    ax.set_xlabel('CV'); ax.set_title('B. CV distribution'); ax.legend(fontsize=8)

    # C: Per-domain null
    ax = fig.add_subplot(gs[0, 2])
    for d, ratios in t1['all_perm_ratios'].items():
        r = np.array([x for x in ratios if x is not None and np.isfinite(x)])
        if len(r) > 0:
            ax.hist(r, bins=60, alpha=0.3, density=True, color=colors_d.get(d, 'gray'), label=f'{d} null')
            obs = t1['published_ratios'].get(d)
            if obs: ax.axvline(obs, color=colors_d.get(d, 'gray'), lw=2.5)
    ax.set_xlabel('Ratio'); ax.set_title('C. Per-domain null vs observed')
    ax.legend(fontsize=8)

    # D-F: Test 2
    if t2:
        ax = fig.add_subplot(gs[1, 0])
        if len(t2['boot_rxvii']) > 0:
            ax.hist(t2['boot_rxvii'], bins=60, alpha=0.6, color=C_R, density=True,
                    label=f'd_R-XVII={t2["d_rxvii_all"]:.3f}')
        if len(t2['boot_revers']) > 0:
            ax.hist(t2['boot_revers'], bins=60, alpha=0.6, color='#FF5722', density=True,
                    label=f'd_revers={t2["d_reversibility_all"]:.3f}')
        ax.set_xlabel("Cohen's d"); ax.set_title('D. R-XVII vs Reversibility'); ax.legend(fontsize=8)

        ax = fig.add_subplot(gs[1, 1])
        vals = [abs(t2['d_rxvii_all']), abs(t2['d_reversibility_all']),
                abs(t2['d_rxvii_dissociated']), abs(t2['d_reversibility_dissociated'])]
        labels = ['R-XVII\n(all)', 'Revers.\n(all)', 'R-XVII\n(dissoc)', 'Revers.\n(dissoc)']
        cols = [C_R, '#FF5722', C_R, '#FF5722']
        for j, (l, v, c) in enumerate(zip(labels, vals, cols)):
            if not np.isnan(v): ax.bar(j, v, color=c, alpha=0.8)
        ax.set_xticks(range(4)); ax.set_xticklabels(labels, fontsize=9)
        ax.set_ylabel("|d|"); ax.set_title('E. Effect sizes')

        ax = fig.add_subplot(gs[1, 2]); ax.axis('off')
        ax.text(0.05, 0.95, f"TEST 2: {t2['verdict']}", transform=ax.transAxes, fontsize=12, va='top',
                fontfamily='monospace', bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))
    else:
        for i in range(3):
            ax = fig.add_subplot(gs[1, i]); ax.axis('off')
            ax.text(0.5, 0.5, 'Test 2: no GDSC', ha='center', va='center', transform=ax.transAxes)

    # G-I: Test 3
    if t3:
        ax = fig.add_subplot(gs[2, 0])
        vals = [1.85, t3['ratio_target'] or 0, 1.42]
        labels = ['R-XVII\nGDSC', 'Target\ncount', 'R-XVII\nYeast']
        ax.bar(labels, vals, color=[C_R, '#4CAF50', '#F9A825'], alpha=0.8)
        ax.axhline(1.0, color='gray', lw=0.5)
        ax.set_ylabel('Ratio'); ax.set_title('G. Ratio comparison')

        ax = fig.add_subplot(gs[2, 1])
        matrix = [['', 'Micro', 'Reef', 'GDSC', 'Yeast'],
                  ['R-XVII', '✓ 1.86', '✓ 1.80', '✓ 1.85', '✓ 1.42'],
                  ['# Targets', '✗ inversé', '✗ N/A', '?', '✗ N/A']]
        table = ax.table(cellText=matrix, cellLoc='center', loc='center')
        table.auto_set_font_size(False); table.set_fontsize(9); table.scale(1, 1.8)
        for j in range(5): table[0, j].set_facecolor('#E0E0E0')
        for i in range(1, 3): table[i, 0].set_facecolor('#E0E0E0')
        ax.axis('off'); ax.set_title('H. Cross-domain applicability')

        ax = fig.add_subplot(gs[2, 2]); ax.axis('off')
        ax.text(0.05, 0.95, f"TEST 3: {t3['verdict']}", transform=ax.transAxes, fontsize=11, va='top',
                fontfamily='monospace', bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))
    else:
        for i in range(3):
            ax = fig.add_subplot(gs[2, i]); ax.axis('off')

    plt.savefig(outpath, dpi=200, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"\n  [FIG] {os.path.abspath(outpath)}")


# ============================================================================
# MAIN
# ============================================================================

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--gdsc', type=str, default=None)
    parser.add_argument('--reef', type=str, default=None)
    parser.add_argument('--mdsine2-base', type=str, default='../MDSINE2_Paper/datasets/gibson')
    parser.add_argument('--yeast-gaf', type=str, default=None)
    parser.add_argument('--yeast-hom-matrix', type=str, default=None)
    parser.add_argument('--yeast-hom-screens', type=str, default=None)
    parser.add_argument('--yeast-het-matrix', type=str, default=None)
    parser.add_argument('--yeast-het-screens', type=str, default=None)
    parser.add_argument('--nperm', type=int, default=100_000)
    parser.add_argument('--nboot', type=int, default=5_000)
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--outdir', type=str, default='.')
    args = parser.parse_args()

    t0 = time.time()
    rng = np.random.RandomState(args.seed)

    print("=" * 80)
    print("  R-XVII SPECIFICITY TESTS v3 — Real data loaders")
    print("=" * 80)

    # --- File discovery ---
    def find(paths):
        for p in paths:
            if p and os.path.exists(p): return p
        return None

    gdsc_path = find([args.gdsc,
                      '../ScriptGDSC/sanger-dose-response.csv',
                      'sanger-dose-response.csv'])
    reef_path = find([args.reef,
                      '../ScriptCorail/global_bleaching_environmental.csv',
                      'global_bleaching_environmental.csv'])
    yeast_gaf = find([args.yeast_gaf,
                      '../ScriptYeast/gene_association.sgd.20251124.gaf'])
    yeast_hom_mat = find([args.yeast_hom_matrix,
                          '../ScriptYeast/yp_matrix_z_haphom_20221025.txt'])
    yeast_hom_scr = find([args.yeast_hom_screens,
                          '../ScriptYeast/yp_screens_haphom_20221025.txt'])
    yeast_het_mat = find([args.yeast_het_matrix,
                          '../ScriptYeast/yp_matrix_het_z_20221018.txt'])
    yeast_het_scr = find([args.yeast_het_screens,
                          '../ScriptYeast/yp_screens_het_20221018.txt'])

    # --- Load real data ---
    print("\n[LOADING] Real data (priority) → published fallback → simulation")
    print("-" * 60)

    gdsc_df = load_gdsc_real(gdsc_path) if gdsc_path else None
    reef_df = load_reef_real(reef_path) if reef_path else None
    micro_data = load_microbiome(args.mdsine2_base)
    yeast_data = load_yeast(yeast_gaf, yeast_hom_mat, yeast_hom_scr,
                            yeast_het_mat, yeast_het_scr)

    # --- Build domain pools ---
    print("\n[SETUP] Building domain pools")
    print("-" * 60)

    domains_data = {}
    data_sources = {}

    # GDSC
    if gdsc_df is not None:
        inp, stc = gdsc_rxvii_groups(gdsc_df)
        r = gdsc_ratio_fn(inp, stc)
        if r:
            domains_data['gdsc'] = {'inp': inp, 'stc': stc, 'ratio': r}
            data_sources['gdsc'] = 'REAL'
            print(f"  GDSC: REAL, ratio={r:.3f}, n_inp={len(inp)}, n_stc={len(stc)}")
    if 'gdsc' not in domains_data:
        fb = simulation_fallback('gdsc', rng)
        if fb: domains_data['gdsc'] = fb; data_sources['gdsc'] = 'SIMULATED'

    # REEF
    if reef_df is not None:
        inp, stc = reef_rxvii_groups(reef_df)
        r = reef_ratio_fn(inp, stc)
        if r:
            domains_data['reef'] = {'inp': inp, 'stc': stc, 'ratio': r}
            data_sources['reef'] = 'REAL'
            print(f"  REEF: REAL, ratio={r:.3f}, n_inp={len(inp)}, n_stc={len(stc)}")
    if 'reef' not in domains_data:
        fb = simulation_fallback('reef', rng)
        if fb: domains_data['reef'] = fb; data_sources['reef'] = 'SIMULATED'

    # MICRO
    if micro_data and micro_data.get('ratio') is not None:
        domains_data['micro'] = {
            'inp': micro_data['inp'],
            'stc': micro_data['stc'],
            'ratio': micro_data['ratio'],
        }
        data_sources['micro'] = micro_data.get('source', 'PUBLISHED_PARAMETRIC')
        print(f"  MICRO: {data_sources['micro']}, ratio={micro_data['ratio']:.3f}, "
              f"n_inp={len(micro_data['inp'])}, n_stc={len(micro_data['stc'])}")
    else:
        fb = simulation_fallback('micro', rng)
        if fb: domains_data['micro'] = fb; data_sources['micro'] = 'SIMULATED'

    # YEAST (hom = primary for cross-domain)
    if yeast_data and yeast_data.get('available') and 'hom' in yeast_data:
        hom = yeast_data['hom']
        r = hom.get('ratio')
        if r and len(hom['inp']) >= 30 and len(hom['stc']) >= 30:
            domains_data['yeast'] = {'inp': hom['inp'], 'stc': hom['stc'], 'ratio': r}
            data_sources['yeast'] = 'REAL'
            print(f"  YEAST: REAL (hom), ratio={r:.3f}, n_inp={len(hom['inp'])}, n_stc={len(hom['stc'])}")
    if 'yeast' not in domains_data:
        fb = simulation_fallback('yeast', rng)
        if fb: domains_data['yeast'] = fb; data_sources['yeast'] = 'SIMULATED'

    # Report confirmatory het
    if yeast_data and 'het' in yeast_data:
        het = yeast_data['het']
        r_het = het.get('ratio')
        if r_het:
            print(f"  YEAST-HET (confirmatory, not in Test 1): ratio={r_het:.3f}")

    print(f"\n  Data sources: {data_sources}")

    # --- Tests ---
    print("\n" + "=" * 80)
    print("  TEST 1 — COMBINATORIAL PERMUTATION")
    print("=" * 80)
    t1 = test1_combinatorial(domains_data, n_perm=args.nperm, seed=args.seed)

    t2 = None
    if gdsc_df is not None:
        print("\n" + "=" * 80)
        print("  TEST 2 — REVERSIBILITY")
        print("=" * 80)
        t2 = test2_reversibility(gdsc_df, n_boot=args.nboot, seed=args.seed)

    t3 = None
    if gdsc_df is not None:
        print("\n" + "=" * 80)
        print("  TEST 3 — TARGET COUNT")
        print("=" * 80)
        t3 = test3_target_count(gdsc_df, n_boot=args.nboot, seed=args.seed)

    # Figure
    fig_path = os.path.join(args.outdir, 'test_specificity_figure_v3.png')
    make_figure(t1, t2, t3, fig_path)

    # --- Summary ---
    print("\n" + "=" * 80)
    print("  FINAL SUMMARY")
    print("=" * 80)
    print(f"\n  4 domains: {list(domains_data.keys())}")
    print(f"  Data sources: {data_sources}")
    print(f"  Published ratios: {t1['published_ratios']}")
    print(f"  Computed ratios:  {t1['sim_ratios']}")
    print(f"  CV={t1['obs_cv']:.4f}, mean={t1['obs_mean_ratio']:.3f}")
    print(f"\n  TEST 1: p_joint(≥1.3)={t1['p_joint']:.6f}")
    if t1['p_joint'] < 0.01:
        print(f"    → ★ CONVERGENCE IS SPECIFIC")
    elif t1['p_joint'] < 0.05:
        print(f"    → MARGINALLY SPECIFIC")
    else:
        print(f"    → ⚠ NOT SPECIFIC")
    if t2: print(f"\n  TEST 2: {t2['verdict']}")
    if t3: print(f"\n  TEST 3: {t3['verdict']}")

    # JSON
    results = {
        'version': 'v3_real_loaders',
        'data_sources': data_sources,
        'test1': {
            'published_ratios': t1['published_ratios'],
            'computed_ratios': t1['sim_ratios'],
            'obs_cv': t1['obs_cv'],
            'obs_mean_ratio': t1['obs_mean_ratio'],
            'p_joint': t1['p_joint'],
            'p_strict': t1['p_strict'],
            'p_cv_only': t1['p_cv_only'],
            'max_mean_ratio': t1['max_mean_ratio'],
            'joint_results': t1['joint_results'],
            'n_perm': t1['n_perm'],
        },
        'test2': {
            'd_rxvii_all': t2['d_rxvii_all'],
            'd_reversibility_all': t2['d_reversibility_all'],
            'verdict': t2['verdict'],
        } if t2 else {'verdict': 'SKIPPED'},
        'test3': {
            'ratio_target': t3['ratio_target'],
            'verdict': t3['verdict'],
        } if t3 else {'verdict': 'SKIPPED'},
    }
    if yeast_data and 'het' in yeast_data and yeast_data['het'].get('ratio'):
        results['confirmatory_yeast_het'] = float(yeast_data['het']['ratio'])

    json_path = os.path.join(args.outdir, 'test_specificity_results_v3.json')
    with open(json_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\n  [JSON] {json_path}")
    print(f"\n  Total: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()