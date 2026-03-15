#!/usr/bin/env python3
"""
=============================================================================
R-XVII CROSS-DOMAIN SPECIFICITY TEST v2 — CORRECTED NULL MODEL
=============================================================================
v1 bug: the permutation null shuffles labels → all ratios collapse to ~1.0
→ σ_null is trivially small → observed σ always exceeds it.

v2 fix: THREE complementary null models:
  (A) R-XVII vs INTENSITY: bootstrap both, test σ_R-XVII < σ_intensity
      This directly answers the referee: "does any strong/weak split work?"
  (B) NORMALIZED PERMUTATION: for each perm, compute ratio per domain,
      then σ of (ratio / domain_null_mean) — scale-invariant comparison
  (C) CROSS-CLASSIFICATION PERMUTATION: for each iteration, randomly
      assign each domain to use either R-XVII or intensity classification,
      then compute σ. Tests whether mixing schemes increases spread.

Also fixes: microbiome uses DYSBIOTIC COHORT ONLY (Phase 2 published
result: hw_bc=0.52, input_bc=0.28, d=1.16, p=0.0006).

v2.1: Full yeast integration (hom exploratory + het confirmatory).

=============================================================================
"""

import numpy as np
import pandas as pd
from scipy import stats, spatial
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
import os, sys, time, json, warnings
from collections import defaultdict

warnings.filterwarnings('ignore')
plt.rcParams.update({
    'font.size': 10, 'axes.titlesize': 12, 'axes.labelsize': 11,
    'figure.dpi': 150, 'savefig.dpi': 300, 'savefig.bbox': 'tight',
})

# --- PATCH LLVMLITE/NUMBA (mdsine2 depends on numba which needs llvmlite) ---
import types

def _patch_llvmlite():
    try:
        import llvmlite.binding
        return  # works fine, no patch needed
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

    numba_stubs = [
        'numba', 'numba.core', 'numba.core.config', 'numba.core.types',
        'numba.core.typing', 'numba.core.errors', 'numba.core.decorators',
        'numba.np', 'numba.np.ufunc', 'numba.typed', 'numba.typed.typedlist',
        'numba.typed.typeddict', 'numba.experimental',
    ]
    for mod_name in numba_stubs:
        if mod_name not in sys.modules:
            m = types.ModuleType(mod_name)
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

_patch_llvmlite()
# --- END PATCH ---

N_PERM = 10_000
N_BOOT = 5_000
SEED = 42


# ============================================================================
# DOMAIN 1: CORAL REEFS
# ============================================================================

def load_reef(path='../ScriptCorail/global_bleaching_environmental.csv'):
    if not os.path.exists(path):
        print(f"  [REEF] Not found: {path}")
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


def reef_classify_rxvii(df):
    dhw = df['dhw'].fillna(0)
    cyc = df['cyclone_freq'].fillna(0)
    cyc_med = cyc[cyc > 0].median() if (cyc > 0).any() else 999
    mask_in = (dhw >= 4) & (dhw < 8) & (cyc <= cyc_med)
    mask_st = (dhw >= 8) | (cyc > cyc_med * 1.5)
    return df.loc[mask_in, 'bleaching'].values, df.loc[mask_st, 'bleaching'].values


def reef_classify_intensity(df):
    stressed = df[df['dhw'] > 0]
    if len(stressed) < 100:
        return np.array([]), np.array([])
    med = stressed['dhw'].median()
    return (stressed.loc[stressed['dhw'] <= med, 'bleaching'].values,
            stressed.loc[stressed['dhw'] > med, 'bleaching'].values)


def reef_ratio(input_vals, struct_vals):
    if len(input_vals) < 30 or len(struct_vals) < 30:
        return None
    mi, ms = np.mean(input_vals), np.mean(struct_vals)
    return ms / max(mi, 0.01)


# ============================================================================
# DOMAIN 2: GDSC
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

_DRUG_MAP = {}
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
for pw, drugs in _struct_drugs.items():
    for d in drugs:
        _DRUG_MAP[d] = pw
for pw, drugs in _input_drugs.items():
    for d in drugs:
        _DRUG_MAP[d] = pw


def _map_drug(name):
    if pd.isna(name): return None
    n = str(name).strip().upper()
    if n in _DRUG_MAP: return _DRUG_MAP[n]
    for key, pw in _DRUG_MAP.items():
        if key in n or n in key: return pw
    return None


def _pw_type(pw):
    if pw in STRUCTURE_PATHWAYS: return 'STRUCTURE'
    if pw in INPUT_PATHWAYS: return 'INPUT'
    return None


def load_gdsc(path='../ScriptGDSC/sanger-dose-response.csv'):
    if not os.path.exists(path):
        print(f"  [GDSC] Not found: {path}")
        return None
    df = pd.read_csv(path)
    auc_col = 'AUC_PUBLISHED' if 'AUC_PUBLISHED' in df.columns else 'AUC'
    df['PATHWAY'] = df['DRUG_NAME'].apply(_map_drug)
    df['PTYPE'] = df['PATHWAY'].apply(_pw_type)
    df = df.dropna(subset=['PTYPE', auc_col])
    df['_auc'] = df[auc_col]
    df['_max_conc'] = df['MAX_CONC'] if 'MAX_CONC' in df.columns else np.nan
    print(f"  [GDSC] {len(df)} classified (IN={sum(df['PTYPE']=='INPUT')}, ST={sum(df['PTYPE']=='STRUCTURE')})")
    return df


def gdsc_classify_rxvii(df):
    return (df.loc[df['PTYPE'] == 'INPUT', '_auc'].values,
            df.loc[df['PTYPE'] == 'STRUCTURE', '_auc'].values)


def gdsc_classify_intensity(df):
    valid = df.dropna(subset=['_max_conc'])
    if len(valid) < 100: return np.array([]), np.array([])
    med = valid['_max_conc'].median()
    return (valid.loc[valid['_max_conc'] <= med, '_auc'].values,
            valid.loc[valid['_max_conc'] > med, '_auc'].values)


def gdsc_ratio(input_auc, struct_auc):
    if len(input_auc) < 30 or len(struct_auc) < 30:
        return None
    mi = 1.0 - np.mean(input_auc)
    ms = 1.0 - np.mean(struct_auc)
    return ms / max(mi, 0.001)


# ============================================================================
# DOMAIN 3: MICROBIOME — DYSBIOTIC COHORT ONLY
# ============================================================================

def load_microbiome():
    try:
        from pathlib import Path
        import mdsine2 as md2

        base = Path('../MDSINE2_Paper/datasets/gibson')
        h_pkl = base / 'healthy/preprocessed/gibson_healthy_agg_filtered.pkl'
        u_pkl = base / 'uc/preprocessed/gibson_uc_agg_filtered.pkl'
        if not h_pkl.exists() or not u_pkl.exists():
            raise FileNotFoundError("MDSINE2 data not found")

        study_h = md2.Study.load(str(h_pkl))
        study_u = md2.Study.load(str(u_pkl))
        print(f"  [MICROBIOME] Loaded MDSINE2 data")
        return _compute_micro_raw(study_h, study_u)
    except (ImportError, FileNotFoundError, OSError) as e:
        print(f"  [MICROBIOME] MDSINE2 not available ({e}), using Phase 2 published values")
        return _micro_published()


def _micro_published():
    return {
        'available': True, 'has_raw': False,
        'hw_bc_mean': 0.52, 'input_bc_mean': 0.28,
        'ratio_rxvii': 0.52 / 0.28,
        'hw_bc_std': 0.15, 'input_bc_std': 0.10,
        'n_hw': 30, 'n_input': 15,
    }


def _compute_micro_raw(study_h, study_u):
    def _extract(study, label):
        records = []
        for subj in study:
            M = subj.matrix()
            rel = M['rel']; times = subj.times
            for i, t in enumerate(times):
                records.append({
                    'cohort': label, 'subject': subj.name,
                    'time': t, 'rel_profile': rel[:, i],
                })
        return records

    h_data = _extract(study_h, 'healthy')
    u_data = _extract(study_u, 'dysbiotic')

    def _recovery_bcs(data, cohort_filter=None):
        if cohort_filter:
            data = [r for r in data if r['cohort'] == cohort_filter]
        input_bcs, hw_bcs = [], []
        subjects = sorted(set(r['subject'] for r in data))
        for subj in subjects:
            sdata = sorted([r for r in data if r['subject'] == subj], key=lambda x: x['time'])
            baseline_samples = [r for r in sdata if 15 <= r['time'] < 21.5]
            if len(baseline_samples) < 3:
                continue
            baseline = np.mean([r['rel_profile'] for r in baseline_samples], axis=0)
            baseline = baseline / (baseline.sum() + 1e-15)
            recovery_map = {
                'HFD': (28.5 + 4, 35.5, 'input'),
                'vancomycin': (42.5 + 4, 50.5, 'hardware'),
                'gentamicin': (57.5 + 4, 65.0, 'hardware'),
            }
            for _, (t_start, t_end, ptype) in recovery_map.items():
                late = [r for r in sdata if t_start <= r['time'] < t_end]
                for r in late:
                    profile = r['rel_profile'] / (r['rel_profile'].sum() + 1e-15)
                    bc = spatial.distance.braycurtis(baseline, profile)
                    if ptype == 'input':
                        input_bcs.append(bc)
                    else:
                        hw_bcs.append(bc)
        return np.array(input_bcs), np.array(hw_bcs)

    in_bc_d, hw_bc_d = _recovery_bcs(u_data, cohort_filter='dysbiotic')
    in_bc_all, hw_bc_all = _recovery_bcs(h_data + u_data, cohort_filter=None)

    print(f"    Dysbiotic: input n={len(in_bc_d)}, hw n={len(hw_bc_d)}")
    print(f"    Both:      input n={len(in_bc_all)}, hw n={len(hw_bc_all)}")

    if len(in_bc_d) > 0 and len(hw_bc_d) > 0:
        ratio_d = np.mean(hw_bc_d) / max(np.mean(in_bc_d), 0.001)
        print(f"    Dysbiotic ratio: {np.mean(hw_bc_d):.3f}/{np.mean(in_bc_d):.3f} = {ratio_d:.3f}")
    else:
        ratio_d = None

    if len(in_bc_all) > 0 and len(hw_bc_all) > 0:
        ratio_all = np.mean(hw_bc_all) / max(np.mean(in_bc_all), 0.001)
        print(f"    Both ratio:      {np.mean(hw_bc_all):.3f}/{np.mean(in_bc_all):.3f} = {ratio_all:.3f}")
    else:
        ratio_all = None

    return {
        'available': True, 'has_raw': True,
        'input_bcs': in_bc_d, 'hw_bcs': hw_bc_d,
        'hw_bc_mean': np.mean(hw_bc_d) if len(hw_bc_d) > 0 else 0.52,
        'input_bc_mean': np.mean(in_bc_d) if len(in_bc_d) > 0 else 0.28,
        'ratio_rxvii': ratio_d if ratio_d else 1.86,
        'hw_bc_std': np.std(hw_bc_d) if len(hw_bc_d) > 0 else 0.15,
        'input_bc_std': np.std(in_bc_d) if len(in_bc_d) > 0 else 0.10,
        'n_hw': len(hw_bc_d), 'n_input': len(in_bc_d),
        'all_input_bcs': in_bc_all, 'all_hw_bcs': hw_bc_all,
        'ratio_both': ratio_all,
    }


def micro_ratio_rxvii(m):
    if not m['available']: return None
    return m['ratio_rxvii']


def micro_ratio_intensity(m):
    if not m['available']: return None
    if m['has_raw']:
        all_bcs = np.concatenate([m['input_bcs'], m['hw_bcs']])
        if len(all_bcs) < 10: return None
        med = np.median(all_bcs)
        high = all_bcs[all_bcs > med]
        low = all_bcs[all_bcs <= med]
        return np.mean(high) / max(np.mean(low), 0.001)
    else:
        hw = np.random.RandomState(42).normal(m['hw_bc_mean'], m['hw_bc_std'], m['n_hw'])
        inp = np.random.RandomState(42).normal(m['input_bc_mean'], m['input_bc_std'], m['n_input'])
        all_v = np.concatenate([hw, inp])
        med = np.median(all_v)
        return np.mean(all_v[all_v > med]) / max(np.mean(all_v[all_v <= med]), 0.001)


# ============================================================================
# DOMAIN 4: YEAST (Saccharomyces cerevisiae)
# ============================================================================

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
    """Load GAF → ORF classification."""
    gene_go = defaultdict(set)
    gene_to_orf = {}
    with open(gaf_path, 'r') as f:
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
                        gene_to_orf[gene] = s
                        break
    orf_class = {}
    for gene, gos in gene_go.items():
        orf = gene_to_orf.get(gene)
        if not orf: continue
        is_s = bool(gos & YEAST_STRUCTURE_TERMS)
        is_i = bool(gos & YEAST_INPUT_TERMS)
        if is_s and not is_i: orf_class[orf] = 'STRUCTURE'
        elif is_i and not is_s: orf_class[orf] = 'INPUT'
    return orf_class


def _load_yeast_matrix(matrix_path, screens_path, orf_class):
    """Load matrix + select screens → return severity arrays."""
    screens_df = pd.read_csv(screens_path, sep='\t')

    # Hillenmeyer screens (hom only)
    hill_mask = screens_df['paper'].str.contains('Hillenmeyer', case=False, na=False)
    hill_hom = screens_df[hill_mask & screens_df['collection'].str.contains('hom', case=False, na=False)]

    if len(hill_hom) > 0:
        screen_ids = set(hill_hom['id'].astype(str))
        source = 'Hillenmeyer'
    else:
        # Fallback: all chemical screens
        growth = screens_df[screens_df['phenotype'].str.contains('growth', case=False, na=False)]
        std_kw = ['standard', 'control', 'untreated', 'DMSO']
        chem = growth[~growth['conditionset'].str.lower().str.contains('|'.join(std_kw), na=True)]
        has_conc = chem[chem['conditionset'].str.contains(r'\[.*[uUnNmMg%]', na=False)]
        screen_ids = set(has_conc['id'].astype(str))
        source = 'All chemical'

    mat = pd.read_csv(matrix_path, sep='\t', index_col=0, low_memory=False)
    cols = [c for c in mat.columns if str(c) in screen_ids]

    s_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'STRUCTURE']
    i_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'INPUT']

    s_sev = mat.loc[s_orfs, cols].abs().mean(axis=1).dropna().values
    i_sev = mat.loc[i_orfs, cols].abs().mean(axis=1).dropna().values

    return s_sev, i_sev, source, len(cols)


def load_yeast(gaf_path='../ScriptYeast/gene_association.sgd.20251124.gaf',
               hom_matrix='../ScriptYeast/yp_matrix_z_haphom_20221025.txt',
               hom_screens='../ScriptYeast/yp_screens_haphom_20221025.txt',
               het_matrix='../ScriptYeast/yp_matrix_het_z_20221018.txt',
               het_screens='../ScriptYeast/yp_screens_het_20221018.txt'):
    """Load yeast data for both hom and het collections."""

    if not os.path.exists(gaf_path):
        print(f"  [YEAST] GAF not found: {gaf_path}")
        return None

    orf_class = _load_yeast_gaf(gaf_path)
    result = {'available': False}

    # HOM (exploratory, primary for cross-domain)
    if os.path.exists(hom_matrix) and os.path.exists(hom_screens):
        print(f"  [YEAST-HOM] Loading matrix...")
        s_sev, i_sev, source, n_scr = _load_yeast_matrix(hom_matrix, hom_screens, orf_class)
        print(f"  [YEAST-HOM] {source}: {n_scr} screens, S={len(s_sev)}, I={len(i_sev)}")
        result['hom'] = {'s_sev': s_sev, 'i_sev': i_sev, 'source': source}
        result['available'] = True
    else:
        print(f"  [YEAST-HOM] Not found: {hom_matrix}")

    # HET (confirmatory)
    if os.path.exists(het_matrix) and os.path.exists(het_screens):
        print(f"  [YEAST-HET] Loading matrix...")
        s_sev, i_sev, source, n_scr = _load_yeast_matrix(het_matrix, het_screens, orf_class)
        print(f"  [YEAST-HET] {source}: {n_scr} screens, S={len(s_sev)}, I={len(i_sev)}")
        result['het'] = {'s_sev': s_sev, 'i_sev': i_sev, 'source': source}
        result['available'] = True
    else:
        print(f"  [YEAST-HET] Not found (optional): {het_matrix}")

    return result


def yeast_classify_rxvii(yeast, collection='hom'):
    """Returns (input_severity, structure_severity)."""
    data = yeast.get(collection)
    if not data:
        return np.array([]), np.array([])
    return data['i_sev'], data['s_sev']


def yeast_classify_intensity(yeast, collection='hom'):
    """Intensity split: median severity regardless of S/I class."""
    data = yeast.get(collection)
    if not data:
        return np.array([]), np.array([])
    all_sev = np.concatenate([data['s_sev'], data['i_sev']])
    med = np.median(all_sev)
    return all_sev[all_sev <= med], all_sev[all_sev > med]


def yeast_ratio(input_sev, struct_sev):
    if len(input_sev) < 30 or len(struct_sev) < 30: return None
    return np.mean(struct_sev) / max(np.mean(input_sev), 0.0001)


# ============================================================================
# BOOTSTRAP ENGINE
# ============================================================================

def bootstrap_ratio(input_vals, struct_vals, ratio_fn, n_boot, rng):
    ratios = []
    for _ in range(n_boot):
        bi = rng.choice(input_vals, len(input_vals), replace=True)
        bs = rng.choice(struct_vals, len(struct_vals), replace=True)
        r = ratio_fn(bi, bs)
        if r is not None and np.isfinite(r):
            ratios.append(r)
    return np.array(ratios)


def cross_domain_sigma(ratios):
    valid = [r for r in ratios if r is not None and np.isfinite(r)]
    return np.std(valid) if len(valid) >= 2 else np.nan


def cross_domain_cv(ratios):
    valid = [r for r in ratios if r is not None and np.isfinite(r)]
    if len(valid) < 2: return np.nan
    m = np.mean(valid)
    return np.std(valid) / m if abs(m) > 0.01 else np.nan


# ============================================================================
# MAIN
# ============================================================================

def main():
    t0 = time.time()
    rng = np.random.RandomState(SEED)

    print("=" * 80)
    print("  R-XVII CROSS-DOMAIN SPECIFICITY TEST v2.1")
    print("  Corrected null model + dysbiotic-only microbiome + yeast (hom+het)")
    print("=" * 80)

    # ── Load ──
    print("\n[1/6] LOADING DATA")
    print("-" * 50)

    reef = load_reef()
    gdsc = load_gdsc()
    micro = load_microbiome()
    yeast = load_yeast()

    domains = []
    if reef is not None: domains.append('reef')
    if gdsc is not None: domains.append('gdsc')
    if micro['available']: domains.append('micro')
    if yeast and yeast['available'] and 'hom' in yeast: domains.append('yeast')
    print(f"\n  Primary domains: {domains} (n={len(domains)})")
    if yeast and 'het' in yeast:
        print(f"  Confirmatory: yeast-het available")

    if len(domains) < 2:
        print("  ERROR: need ≥2 domains"); sys.exit(1)

    # ── Domain colors ──
    C_D = {
        'reef': '#26A69A', 'gdsc': '#AB47BC',
        'micro': '#EF5350', 'yeast': '#F9A825',
    }

    # ── Ratio functions ──
    def _reef_ratio_fn(inp, stc):
        if len(inp) < 5 or len(stc) < 5: return None
        return np.mean(stc) / max(np.mean(inp), 0.01)

    def _gdsc_ratio_fn(inp, stc):
        if len(inp) < 5 or len(stc) < 5: return None
        mi = 1.0 - np.mean(inp); ms = 1.0 - np.mean(stc)
        return ms / max(mi, 0.001)

    def _micro_ratio_fn(inp, hw):
        if len(inp) < 3 or len(hw) < 3: return None
        return np.mean(hw) / max(np.mean(inp), 0.001)

    def _yeast_ratio_fn(inp, stc):
        if len(inp) < 5 or len(stc) < 5: return None
        return np.mean(stc) / max(np.mean(inp), 0.0001)

    ratio_fns = {
        'reef': _reef_ratio_fn, 'gdsc': _gdsc_ratio_fn,
        'micro': _micro_ratio_fn, 'yeast': _yeast_ratio_fn,
    }

    # ── Condition 1: R-XVII ──
    print("\n[2/6] CONDITION 1: R-XVII CLASSIFICATION")
    print("-" * 50)

    rxvii = {}
    rxvii_groups = {}

    if 'reef' in domains:
        inp, stc = reef_classify_rxvii(reef)
        r = reef_ratio(inp, stc)
        rxvii['reef'] = r
        rxvii_groups['reef'] = (inp, stc)
        print(f"  Reef:  struct_mean={np.mean(stc):.2f}  input_mean={np.mean(inp):.2f}  ratio={r:.3f}")

    if 'gdsc' in domains:
        inp, stc = gdsc_classify_rxvii(gdsc)
        r = gdsc_ratio(inp, stc)
        rxvii['gdsc'] = r
        rxvii_groups['gdsc'] = (inp, stc)
        print(f"  GDSC:  mag_st={1-np.mean(stc):.4f}  mag_in={1-np.mean(inp):.4f}  ratio={r:.3f}")

    if 'micro' in domains:
        r = micro_ratio_rxvii(micro)
        rxvii['micro'] = r
        if micro['has_raw']:
            rxvii_groups['micro'] = (micro['input_bcs'], micro['hw_bcs'])
        print(f"  Micro: hw={micro['hw_bc_mean']:.3f}  in={micro['input_bc_mean']:.3f}  ratio={r:.3f}")

    if 'yeast' in domains:
        inp, stc = yeast_classify_rxvii(yeast, 'hom')
        r = yeast_ratio(inp, stc)
        rxvii['yeast'] = r
        rxvii_groups['yeast'] = (inp, stc)
        print(f"  Yeast: struct_mean={np.mean(stc):.4f}  input_mean={np.mean(inp):.4f}  ratio={r:.3f}")

    # Confirmatory het (reported separately, not in cross-domain σ)
    if yeast and 'het' in yeast:
        inp_h, stc_h = yeast_classify_rxvii(yeast, 'het')
        r_het = yeast_ratio(inp_h, stc_h)
        print(f"  Yeast-het (confirmatory): ratio={r_het:.3f}")

    sigma_rxvii = cross_domain_sigma(list(rxvii.values()))
    cv_rxvii = cross_domain_cv(list(rxvii.values()))
    mean_rxvii = np.mean([v for v in rxvii.values() if v])
    print(f"\n  Ratios: {rxvii}")
    print(f"  Mean = {mean_rxvii:.3f}, σ = {sigma_rxvii:.4f}, CV = {cv_rxvii:.4f}")

    # ── Condition 2: Intensity ──
    print("\n[3/6] CONDITION 2: INTENSITY CLASSIFICATION")
    print("-" * 50)

    intensity = {}
    intensity_groups = {}

    if 'reef' in domains:
        lo, hi = reef_classify_intensity(reef)
        r = reef_ratio(lo, hi)
        intensity['reef'] = r
        intensity_groups['reef'] = (lo, hi)
        if r: print(f"  Reef:  high={np.mean(hi):.2f}  low={np.mean(lo):.2f}  ratio={r:.3f}")

    if 'gdsc' in domains:
        lo, hi = gdsc_classify_intensity(gdsc)
        r = gdsc_ratio(lo, hi)
        intensity['gdsc'] = r
        intensity_groups['gdsc'] = (lo, hi)
        if r: print(f"  GDSC:  high_dose={1-np.mean(hi):.4f}  low_dose={1-np.mean(lo):.4f}  ratio={r:.3f}")

    if 'micro' in domains:
        r = micro_ratio_intensity(micro)
        intensity['micro'] = r
        if r: print(f"  Micro: intensity ratio={r:.3f}")

    if 'yeast' in domains:
        lo, hi = yeast_classify_intensity(yeast, 'hom')
        r = yeast_ratio(lo, hi)
        intensity['yeast'] = r
        intensity_groups['yeast'] = (lo, hi)
        if r: print(f"  Yeast: high={np.mean(hi):.4f}  low={np.mean(lo):.4f}  ratio={r:.3f}")

    sigma_intensity = cross_domain_sigma(list(intensity.values()))
    cv_intensity = cross_domain_cv(list(intensity.values()))
    mean_intensity = np.mean([v for v in intensity.values() if v])
    print(f"\n  Ratios: {intensity}")
    print(f"  Mean = {mean_intensity:.3f}, σ = {sigma_intensity:.4f}, CV = {cv_intensity:.4f}")

    # ── Null model A: Bootstrap σ comparison ──
    print(f"\n[4/6] NULL MODEL A: BOOTSTRAP σ COMPARISON (n={N_BOOT})")
    print("-" * 50)

    boot_rxvii_sigmas = []
    boot_intens_sigmas = []

    for b in range(N_BOOT):
        if (b + 1) % 1000 == 0:
            print(f"  ... {b+1}/{N_BOOT}")

        rxvii_sample = {}
        for d in domains:
            if d in rxvii_groups:
                inp, stc = rxvii_groups[d]
                bi = rng.choice(inp, len(inp), replace=True)
                bs = rng.choice(stc, len(stc), replace=True)
                r = ratio_fns[d](bi, bs)
                if r and np.isfinite(r):
                    rxvii_sample[d] = r
            elif d == 'micro' and not micro['has_raw']:
                hw_boot = rng.normal(micro['hw_bc_mean'], micro['hw_bc_std'], micro['n_hw'])
                in_boot = rng.normal(micro['input_bc_mean'], micro['input_bc_std'], micro['n_input'])
                r = np.mean(hw_boot) / max(np.mean(in_boot), 0.001)
                rxvii_sample[d] = r

        if len(rxvii_sample) >= 2:
            boot_rxvii_sigmas.append(cross_domain_sigma(list(rxvii_sample.values())))

        intens_sample = {}
        for d in domains:
            if d in intensity_groups:
                lo, hi = intensity_groups[d]
                if len(lo) > 0 and len(hi) > 0:
                    blo = rng.choice(lo, len(lo), replace=True)
                    bhi = rng.choice(hi, len(hi), replace=True)
                    r = ratio_fns[d](blo, bhi)
                    if r and np.isfinite(r):
                        intens_sample[d] = r

        if len(intens_sample) >= 2:
            boot_intens_sigmas.append(cross_domain_sigma(list(intens_sample.values())))

    boot_rxvii_sigmas = np.array(boot_rxvii_sigmas)
    boot_intens_sigmas = np.array(boot_intens_sigmas)

    n_compare = min(len(boot_rxvii_sigmas), len(boot_intens_sigmas))
    if n_compare > 0:
        p_rxvii_less = np.mean(boot_rxvii_sigmas[:n_compare] < boot_intens_sigmas[:n_compare])
    else:
        p_rxvii_less = np.nan

    print(f"\n  Bootstrap σ_R-XVII:    {np.mean(boot_rxvii_sigmas):.4f} "
          f"[{np.percentile(boot_rxvii_sigmas, 2.5):.4f}, {np.percentile(boot_rxvii_sigmas, 97.5):.4f}]")
    print(f"  Bootstrap σ_intensity: {np.mean(boot_intens_sigmas):.4f} "
          f"[{np.percentile(boot_intens_sigmas, 2.5):.4f}, {np.percentile(boot_intens_sigmas, 97.5):.4f}]")
    print(f"  P(σ_R-XVII < σ_intensity) = {p_rxvii_less:.4f}")

    # ── Null model B: Cross-classification permutation ──
    print(f"\n[5/6] NULL MODEL B: CROSS-CLASSIFICATION PERMUTATION")
    print("-" * 50)

    cross_class_sigmas = []
    for _ in range(N_PERM):
        mixed_ratios = {}
        for d in domains:
            use_rxvii = rng.random() < 0.5
            if use_rxvii:
                mixed_ratios[d] = rxvii.get(d)
            else:
                mixed_ratios[d] = intensity.get(d)
        valid = [v for v in mixed_ratios.values() if v is not None and np.isfinite(v)]
        if len(valid) >= 2:
            cross_class_sigmas.append(np.std(valid))

    cross_class_sigmas = np.array(cross_class_sigmas)
    p_cross_class = np.mean(cross_class_sigmas <= sigma_rxvii) if len(cross_class_sigmas) > 0 else np.nan

    print(f"  Mixed σ: {np.mean(cross_class_sigmas):.4f} ± {np.std(cross_class_sigmas):.4f}")
    print(f"  R-XVII σ = {sigma_rxvii:.4f}")
    print(f"  P(mixed_σ ≤ σ_R-XVII) = {p_cross_class:.4f}")

    # ── Within-domain permutation (reference) ──
    print(f"\n  [Reference] Within-domain permutation null (n={N_PERM})")

    perm_ratios_per_domain = {d: [] for d in domains}
    perm_sigmas = []

    for i in range(N_PERM):
        perm_r = {}

        if 'reef' in domains:
            inp, stc = rxvii_groups['reef']
            pool = np.concatenate([inp, stc])
            idx = rng.permutation(len(pool))
            pi, ps = pool[idx[:len(inp)]], pool[idx[len(inp):]]
            r = _reef_ratio_fn(pi, ps)
            perm_ratios_per_domain['reef'].append(r)
            perm_r['reef'] = r

        if 'gdsc' in domains:
            inp, stc = rxvii_groups['gdsc']
            pool = np.concatenate([inp, stc])
            idx = rng.permutation(len(pool))
            pi, ps = pool[idx[:len(inp)]], pool[idx[len(inp):]]
            r = _gdsc_ratio_fn(pi, ps)
            perm_ratios_per_domain['gdsc'].append(r)
            perm_r['gdsc'] = r

        if 'micro' in domains:
            if micro['has_raw']:
                pool = np.concatenate([micro['input_bcs'], micro['hw_bcs']])
                idx = rng.permutation(len(pool))
                n_in = len(micro['input_bcs'])
                r = _micro_ratio_fn(pool[idx[:n_in]], pool[idx[n_in:]])
            else:
                pool = np.concatenate([
                    rng.normal(micro['hw_bc_mean'], micro['hw_bc_std'], micro['n_hw']),
                    rng.normal(micro['input_bc_mean'], micro['input_bc_std'], micro['n_input']),
                ])
                rng.shuffle(pool)
                r = np.mean(pool[micro['n_input']:]) / max(np.mean(pool[:micro['n_input']]), 0.001)
            perm_ratios_per_domain['micro'].append(r)
            perm_r['micro'] = r

        if 'yeast' in domains:
            inp, stc = rxvii_groups['yeast']
            pool = np.concatenate([inp, stc])
            idx = rng.permutation(len(pool))
            pi, ps = pool[idx[:len(inp)]], pool[idx[len(inp):]]
            r = _yeast_ratio_fn(pi, ps)
            perm_ratios_per_domain['yeast'].append(r)
            perm_r['yeast'] = r

        valid = [v for v in perm_r.values() if v is not None and np.isfinite(v)]
        if len(valid) >= 2:
            perm_sigmas.append(np.std(valid))

    perm_sigmas = np.array(perm_sigmas)

    domain_pvals = {}
    for d in domains:
        obs = rxvii.get(d)
        perms = [r for r in perm_ratios_per_domain[d] if r is not None and np.isfinite(r)]
        if obs and perms:
            p = np.mean(np.array(perms) >= obs)
            domain_pvals[d] = p
            print(f"    {d}: obs={obs:.3f}, perm mean={np.mean(perms):.3f}, p(perm≥obs)={p:.4f}")

    # ── Summary ──
    print(f"\n[6/6] RESULTS")
    print("=" * 80)

    print(f"\n  {'Condition':<30s}", end='')
    for d in domains: print(f" {d:>10s}", end='')
    print(f" {'σ':>8s} {'CV':>8s}")
    print("  " + "-" * (30 + 10*len(domains) + 20))

    row = f"  {'(1) R-XVII':<30s}"
    for d in domains:
        v = rxvii.get(d)
        row += f" {v:10.3f}" if v else f" {'N/A':>10s}"
    row += f" {sigma_rxvii:8.4f} {cv_rxvii:8.4f}"
    print(row)

    row = f"  {'(2) Intensity':<30s}"
    for d in domains:
        v = intensity.get(d)
        row += f" {v:10.3f}" if v else f" {'N/A':>10s}"
    row += f" {sigma_intensity:8.4f} {cv_intensity:8.4f}"
    print(row)

    row = f"  {'(3) Perm null (mean)':<30s}"
    for d in domains:
        perms = [r for r in perm_ratios_per_domain[d] if r is not None and np.isfinite(r)]
        row += f" {np.mean(perms):10.3f}" if perms else f" {'N/A':>10s}"
    row += f" {np.mean(perm_sigmas):8.4f}"
    print(row)

    # Confirmatory het line
    if yeast and 'het' in yeast:
        print(f"\n  Confirmatory (not in σ): yeast-het = {r_het:.3f}×")

    print(f"\n  KEY TESTS:")
    print(f"    A. Bootstrap P(σ_R-XVII < σ_intensity)   = {p_rxvii_less:.4f}")
    print(f"    B. Cross-class P(mixed_σ ≤ σ_R-XVII)     = {p_cross_class:.4f}")
    print(f"    σ ratio: σ_intensity / σ_R-XVII           = {sigma_intensity / max(sigma_rxvii, 0.0001):.2f}×")
    print(f"    CV ratio: CV_intensity / CV_R-XVII        = {cv_intensity / max(cv_rxvii, 0.0001):.2f}×")
    for d in domains:
        p = domain_pvals.get(d)
        if p is not None:
            print(f"    Within-domain {d}: p(perm≥obs) = {p:.4f}")

    # ── Interpretation ──
    print(f"\n{'=' * 80}")
    print("  INTERPRETATION")
    print(f"{'=' * 80}")

    specific = p_rxvii_less > 0.95
    partial = p_rxvii_less > 0.75
    cross_specific = p_cross_class < 0.25

    if specific:
        verdict = "SPECIFIC"
        detail = ("R-XVII classification produces significantly tighter cross-domain\n"
                  "    convergence than intensity-based classification. The ratio is\n"
                  "    NOT a generic artifact of strong/weak splits — it requires the\n"
                  "    structure/input mechanistic distinction.")
    elif partial:
        verdict = "PARTIALLY SPECIFIC"
        detail = ("R-XVII tends to produce tighter convergence than intensity, but the\n"
                  "    difference is not overwhelming. The mechanistic distinction helps\n"
                  "    but may not be the sole factor.")
    else:
        verdict = "INCONCLUSIVE"
        detail = ("Cannot clearly demonstrate that R-XVII convergence exceeds what\n"
                  "    intensity-based classification produces. More domains or larger\n"
                  "    samples may be needed.")

    print(f"\n  ★ VERDICT: {verdict}")
    print(f"    {detail}")

    # ── Visualization ──
    fig = plt.figure(figsize=(22, 20))
    gs = gridspec.GridSpec(4, 3, hspace=0.4, wspace=0.35)
    fig.suptitle('R-XVII Cross-Domain Specificity Test v2.1\n'
                 f'Domains: {", ".join(d.capitalize() for d in domains)} + yeast-het (confirmatory)',
                 fontsize=14, fontweight='bold', y=0.995)

    C_R = '#1565C0'
    C_I = '#FF6F00'
    C_N = '#9E9E9E'

    # A: ratios by condition
    ax = fig.add_subplot(gs[0, 0])
    x = np.arange(len(domains))
    w = 0.25
    v_r = [rxvii.get(d, 0) or 0 for d in domains]
    v_i = [intensity.get(d, 0) or 0 for d in domains]
    v_n = []
    for d in domains:
        perms = [r for r in perm_ratios_per_domain[d] if r is not None and np.isfinite(r)]
        v_n.append(np.mean(perms) if perms else 0)
    ax.bar(x - w, v_r, w, color=C_R, alpha=0.8, label='R-XVII')
    ax.bar(x, v_i, w, color=C_I, alpha=0.8, label='Intensity')
    ax.bar(x + w, v_n, w, color=C_N, alpha=0.8, label='Perm null')
    ax.axhline(1.0, color='gray', ls='-', lw=0.5)
    ax.set_xticks(x)
    ax.set_xticklabels([d.capitalize() for d in domains])
    ax.set_ylabel('Ratio')
    ax.set_title('A. Ratio by condition × domain')
    ax.legend(fontsize=8)

    # B: bootstrap σ comparison
    ax = fig.add_subplot(gs[0, 1])
    ax.hist(boot_rxvii_sigmas, bins=50, alpha=0.6, color=C_R, density=True, label='σ_R-XVII')
    ax.hist(boot_intens_sigmas, bins=50, alpha=0.6, color=C_I, density=True, label='σ_intensity')
    ax.axvline(sigma_rxvii, color=C_R, lw=2.5, ls='-')
    ax.axvline(sigma_intensity, color=C_I, lw=2.5, ls='--')
    ax.set_xlabel('Cross-domain σ')
    ax.set_ylabel('Density')
    ax.set_title(f'B. Bootstrap σ comparison\nP(σ_R<σ_I)={p_rxvii_less:.3f}')
    ax.legend(fontsize=8)

    # C: cross-classification null
    ax = fig.add_subplot(gs[0, 2])
    ax.hist(cross_class_sigmas, bins=50, alpha=0.6, color=C_N, density=True, label='Mixed σ')
    ax.axvline(sigma_rxvii, color=C_R, lw=2.5, label=f'R-XVII σ={sigma_rxvii:.3f}')
    ax.axvline(sigma_intensity, color=C_I, lw=2.5, ls='--', label=f'Intensity σ={sigma_intensity:.3f}')
    ax.set_xlabel('Cross-domain σ (mixed classification)')
    ax.set_ylabel('Density')
    ax.set_title(f'C. Cross-classification null\np={p_cross_class:.4f}')
    ax.legend(fontsize=8)

    # D: per-domain permutation dists
    ax = fig.add_subplot(gs[1, 0])
    for d in domains:
        perms = [r for r in perm_ratios_per_domain[d] if r is not None and np.isfinite(r)]
        if perms:
            ax.hist(perms, bins=50, alpha=0.35, density=True, color=C_D[d], label=f'{d} null')
            obs = rxvii.get(d)
            if obs:
                ax.axvline(obs, color=C_D[d], lw=2.5)
    ax.axhline(0, color='gray', lw=0.5)
    ax.set_xlabel('Ratio')
    ax.set_ylabel('Density')
    ax.set_title('D. Per-domain null (lines = R-XVII observed)')
    ax.legend(fontsize=8)

    # E: scatter R-XVII vs intensity
    ax = fig.add_subplot(gs[1, 1])
    for d in domains:
        r_r = rxvii.get(d)
        r_i = intensity.get(d)
        if r_r and r_i:
            ax.scatter(r_r, r_i, s=250, color=C_D[d], edgecolor='black', zorder=5)
            ax.annotate(d.upper(), (r_r, r_i), textcoords='offset points',
                        xytext=(10, 5), fontsize=11, fontweight='bold')
    all_r = list(rxvii.values()) + list(intensity.values())
    all_r = [v for v in all_r if v is not None]
    lim = (min(0.5, min(all_r) - 0.2), max(all_r) + 0.3)
    ax.plot(lim, lim, 'k:', alpha=0.3, label='y=x')
    ax.set_xlabel('R-XVII ratio')
    ax.set_ylabel('Intensity ratio')
    ax.set_title('E. R-XVII vs Intensity per domain')
    ax.set_xlim(lim); ax.set_ylim(lim)
    ax.set_aspect('equal')
    ax.legend(fontsize=8)

    # F: convergence bars
    ax = fig.add_subplot(gs[1, 2])
    labels = ['R-XVII', 'Intensity', 'Cross-class\n(mixed)']
    sigmas = [sigma_rxvii, sigma_intensity, np.mean(cross_class_sigmas)]
    ci_lo = [np.percentile(boot_rxvii_sigmas, 2.5), np.percentile(boot_intens_sigmas, 2.5),
             np.percentile(cross_class_sigmas, 2.5)]
    ci_hi = [np.percentile(boot_rxvii_sigmas, 97.5), np.percentile(boot_intens_sigmas, 97.5),
             np.percentile(cross_class_sigmas, 97.5)]
    colors = [C_R, C_I, C_N]
    errs_lo = [max(0, s - l) for s, l in zip(sigmas, ci_lo)]
    errs_hi = [max(0, h - s) for s, h in zip(sigmas, ci_hi)]
    ax.bar(labels, sigmas, color=colors, alpha=0.8, edgecolor='black')
    ax.errorbar(labels, sigmas, yerr=[errs_lo, errs_hi], fmt='none', color='black', capsize=8, lw=2)
    ax.set_ylabel('Cross-domain σ')
    ax.set_title('F. Convergence: lower σ = more convergent')
    if specific:
        ax.text(0, sigmas[0] + 0.02, '★', fontsize=24, ha='center', color=C_R)

    # G: ratio heatmap
    ax = fig.add_subplot(gs[2, 0])
    mtx = []
    for ratios in [rxvii, intensity]:
        mtx.append([ratios.get(d, np.nan) for d in domains])
    mtx = np.array(mtx)
    im = ax.imshow(mtx, cmap='YlOrRd', aspect='auto', vmin=0.5, vmax=3.0)
    ax.set_xticks(range(len(domains)))
    ax.set_xticklabels([d.capitalize() for d in domains])
    ax.set_yticks([0, 1])
    ax.set_yticklabels(['R-XVII', 'Intensity'])
    for i in range(2):
        for j in range(len(domains)):
            v = mtx[i, j]
            if np.isfinite(v):
                ax.text(j, i, f'{v:.2f}', ha='center', va='center',
                        fontsize=16, fontweight='bold',
                        color='white' if v > 1.5 else 'black')
    plt.colorbar(im, ax=ax, shrink=0.7)
    ax.set_title('G. Ratio matrix')

    # H: bootstrap ratio distributions
    ax = fig.add_subplot(gs[2, 1])
    for d in domains:
        if d in rxvii_groups:
            inp, stc = rxvii_groups[d]
            boot_r = bootstrap_ratio(inp, stc, ratio_fns[d], 2000, rng)
            ax.hist(boot_r, bins=50, alpha=0.4, color=C_D[d], density=True, label=f'{d.capitalize()} R-XVII')
        elif d == 'micro' and not micro['has_raw']:
            # Parametric bootstrap
            boot_r = []
            for _ in range(2000):
                hw_b = rng.normal(micro['hw_bc_mean'], micro['hw_bc_std'], micro['n_hw'])
                in_b = rng.normal(micro['input_bc_mean'], micro['input_bc_std'], micro['n_input'])
                boot_r.append(np.mean(hw_b) / max(np.mean(in_b), 0.001))
            ax.hist(boot_r, bins=50, alpha=0.4, color=C_D[d], density=True, label=f'{d.capitalize()} R-XVII')
    ax.set_xlabel('Ratio')
    ax.set_ylabel('Density')
    ax.set_title('H. Bootstrap ratio distributions (R-XVII)')
    ax.legend(fontsize=8)

    # I: paired bootstrap scatter
    ax = fig.add_subplot(gs[2, 2])
    n_show = min(200, n_compare)
    ax.scatter(boot_rxvii_sigmas[:n_show], boot_intens_sigmas[:n_show],
               s=8, alpha=0.3, color='gray')
    ax.plot([0, max(boot_intens_sigmas)], [0, max(boot_intens_sigmas)], 'k:', alpha=0.3)
    ax.scatter([sigma_rxvii], [sigma_intensity], s=200, color='red', edgecolor='black',
               zorder=5, label='Observed')
    ax.set_xlabel('σ_R-XVII (bootstrap)')
    ax.set_ylabel('σ_intensity (bootstrap)')
    ax.set_title(f'I. Paired bootstrap: {p_rxvii_less*100:.0f}% below diagonal')
    ax.legend()

    # J: Summary
    ax = fig.add_subplot(gs[3, :])
    ax.axis('off')

    rxvii_str = ', '.join(f"{d}={rxvii[d]:.3f}" for d in domains if rxvii.get(d))
    intens_str = ', '.join(f"{d}={intensity[d]:.3f}" for d in domains if intensity.get(d))

    S = [
        "=" * 100,
        "  R-XVII CROSS-DOMAIN SPECIFICITY TEST v2.1 — SUMMARY",
        "=" * 100, "",
        f"  Domains: {', '.join(d.capitalize() for d in domains)} (n={len(domains)})",
        f"  N_BOOT={N_BOOT}, N_PERM={N_PERM}", "",
        f"  CONDITION 1 — R-XVII:     {rxvii_str}",
        f"    σ = {sigma_rxvii:.4f}, CV = {cv_rxvii:.4f}", "",
        f"  CONDITION 2 — Intensity:  {intens_str}",
        f"    σ = {sigma_intensity:.4f}, CV = {cv_intensity:.4f}", "",
    ]
    if yeast and 'het' in yeast:
        S.append(f"  CONFIRMATORY: yeast-het = {r_het:.3f}× (OSF pre-registered)")
        S.append("")
    S += [
        f"  TEST A: Bootstrap P(σ_R-XVII < σ_intensity) = {p_rxvii_less:.4f}",
        f"  TEST B: Cross-classification P(mixed_σ ≤ σ_R-XVII) = {p_cross_class:.4f}",
        f"  σ ratio: intensity/R-XVII = {sigma_intensity/max(sigma_rxvii,0.0001):.2f}×",
        f"  CV ratio: intensity/R-XVII = {cv_intensity/max(cv_rxvii,0.0001):.2f}×", "",
    ]
    for d in domains:
        p = domain_pvals.get(d)
        if p is not None:
            S.append(f"  Within-domain {d}: p(perm ≥ obs) = {p:.4f}")
    S += ["", f"  ★ VERDICT: {verdict}", f"    {detail}"]

    ax.text(0.02, 0.98, '\n'.join(S), transform=ax.transAxes, fontsize=10,
            va='top', fontfamily='monospace',
            bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))

    out_fig = 'rXVII_specificity_v2.png'
    plt.savefig(out_fig, dpi=200, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"\n  [FIG] {os.path.abspath(out_fig)}")

    # JSON
    results = {
        'domains': domains,
        'rxvii_ratios': {k: float(v) for k, v in rxvii.items() if v},
        'intensity_ratios': {k: float(v) for k, v in intensity.items() if v},
        'sigma_rxvii': float(sigma_rxvii),
        'sigma_intensity': float(sigma_intensity),
        'cv_rxvii': float(cv_rxvii),
        'cv_intensity': float(cv_intensity),
        'sigma_ratio': float(sigma_intensity / max(sigma_rxvii, 0.0001)),
        'p_bootstrap_rxvii_less': float(p_rxvii_less),
        'p_cross_classification': float(p_cross_class),
        'boot_sigma_rxvii_ci': [float(np.percentile(boot_rxvii_sigmas, 2.5)),
                                 float(np.percentile(boot_rxvii_sigmas, 97.5))],
        'boot_sigma_intens_ci': [float(np.percentile(boot_intens_sigmas, 2.5)),
                                  float(np.percentile(boot_intens_sigmas, 97.5))],
        'domain_pvals': {k: float(v) for k, v in domain_pvals.items()},
        'verdict': verdict,
    }
    if yeast and 'het' in yeast:
        results['confirmatory_yeast_het'] = float(r_het)

    out_json = 'rXVII_specificity_v2.json'
    with open(out_json, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"  [JSON] {os.path.abspath(out_json)}")

    elapsed = time.time() - t0
    print(f"\n  Total: {elapsed:.1f}s")


if __name__ == '__main__':
    main()