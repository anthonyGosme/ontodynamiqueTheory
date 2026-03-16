#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════
  PREPRINT FIGURES — R-XVII cross-domain analysis
  Ontodynamique — A. Gosme, 2026

  Self-contained script: duplicates loading/classification logic
  from each domain script, extracts individual S/I distributions,
  then produces:
    --extract   : extract raw distributions → preprint_data.json
    --meta      : forest plot (Task 1)
    --distrib   : distribution histograms (Task 3)
    --all       : everything

  Usage examples:
    # Extract all domains (run once, then meta/distrib are fast)
    python3 preprint_figures.py --extract \
      --reef-csv ScriptCorail/global_bleaching_environmental.csv \
      --gdsc-csv ScriptGDSC/sanger-dose-response.csv \
      --yeast-matrix yp_matrix_z_haphom_20221025.txt \
      --yeast-screens yp_screens_haphom_20221025.txt \
      --yeast-gaf gene_association.sgd.20251124.gaf \
      --mdsine2-paper ./MDSINE2_Paper

    # Figures only (from cached preprint_data.json)
    python3 preprint_figures.py --meta --distrib

═══════════════════════════════════════════════════════════════
"""

import argparse, json, os, sys, collections, warnings, time
from pathlib import Path
import numpy as np
import pandas as pd
from scipy import stats, spatial
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

warnings.filterwarnings('ignore')

DATA_FILE = 'preprint_data.json'

# ════════════════════════════════════════════════════════════════
#  DOMAIN 1: REEF (GCBD)
#  Source: ScriptCorail/corail.py — load() + classify_clean()
# ════════════════════════════════════════════════════════════════

def extract_reef(csv_path):
    """Load GCBD, classify by DHW/cyclone, return individual bleaching values."""
    print("\n" + "=" * 60)
    print("  REEF — Loading GCBD")
    print("=" * 60)

    df = pd.read_csv(csv_path)
    rn = {'Latitude_Degrees': 'lat', 'Longitude_Degrees': 'lon', 'Date_Year': 'year',
          'Percent_Bleaching': 'bleaching', 'SSTA_DHW': 'dhw',
          'Cyclone_Frequency': 'cyclone_freq'}
    df = df.rename(columns=rn)
    for c in ['bleaching', 'dhw', 'cyclone_freq']:
        if c in df.columns:
            df[c] = pd.to_numeric(df[c], errors='coerce')
    df = df.dropna(subset=['bleaching', 'dhw'])
    print(f"  {len(df)} observations loaded")

    # Classification — identical to corail.py lines 73-79
    dhw = df['dhw'].fillna(0)
    cyc = df['cyclone_freq'].fillna(0)
    cyc_med = cyc[cyc > 0].median() if (cyc > 0).any() else 999

    pt = pd.Series('baseline', index=df.index)
    pt[(dhw >= 4) & (dhw < 8) & (cyc <= cyc_med)] = 'input'
    pt[(dhw >= 8) | (cyc > cyc_med * 1.5)] = 'structure'
    df['ptype'] = pt

    df_i = df.loc[df['ptype'] == 'input'].dropna(subset=['bleaching'])
    df_s = df.loc[df['ptype'] == 'structure'].dropna(subset=['bleaching'])
    inp = df_i['bleaching'].values
    stc = df_s['bleaching'].values

    # Cluster IDs for cluster bootstrap (Site_ID)
    site_col = 'Site_ID' if 'Site_ID' in df.columns else 'site_id'
    if site_col not in df.columns:
        site_col = [c for c in df.columns if 'site' in c.lower() and 'id' in c.lower()]
        site_col = site_col[0] if site_col else None

    ci_i = df_i[site_col].values.tolist() if site_col else None
    ci_s = df_s[site_col].values.tolist() if site_col else None

    n_clusters_i = len(set(ci_i)) if ci_i else len(inp)
    n_clusters_s = len(set(ci_s)) if ci_s else len(stc)

    print(f"  Input: n={len(inp)}, mean={np.mean(inp):.2f}, clusters={n_clusters_i}")
    print(f"  Structure: n={len(stc)}, mean={np.mean(stc):.2f}, clusters={n_clusters_s}")
    ratio = np.mean(stc) / np.mean(inp)
    print(f"  Ratio (means): {ratio:.4f}×")

    return {
        'domain': 'Reef (GCBD)',
        'response_var': 'Percent bleaching',
        'i_values': inp.tolist(),
        's_values': stc.tolist(),
        'cluster_ids_i': ci_i,
        'cluster_ids_s': ci_s,
    }


# ════════════════════════════════════════════════════════════════
#  DOMAIN 2: CANCER (GDSC)
#  Source: ScriptGDSC/GDSC1.py — DRUG_PATHWAY + classify_perturbation()
# ════════════════════════════════════════════════════════════════

# --- Drug → pathway mapping (duplicated from GDSC1.py lines 42-224) ---

_DRUG_PATHWAY = {}
def _add(drugs, pw):
    for d in drugs:
        _DRUG_PATHWAY[d] = pw

_add(['OLAPARIB','TALAZOPARIB','RUCAPARIB','NIRAPARIB','VELIPARIB',
      'MIRIN','KU-55933','KU-60019','KU-57788','NU-7441',
      'AZD6738','VE-821','VE-822','AZD7762','CHIR-124','MK-8776',
      'BLEOMYCIN','CISPLATIN','CARBOPLATIN','OXALIPLATIN',
      'CARMUSTINE','LOMUSTINE','TEMOZOLOMIDE','MITOMYCIN-C',
      'ETOPOSIDE','CAMPTOTHECIN','SN-38','IRINOTECAN','TOPOTECAN',
      'DOXORUBICIN','DACTINOMYCIN','EPIRUBICIN','MITOXANTRONE'], 'Genome integrity')
_add(['GEMCITABINE','CYTARABINE','5-FLUOROURACIL','METHOTREXATE',
      'FLUDARABINE','CLOFARABINE','HYDROXYUREA','PEMETREXED','CLADRIBINE'], 'DNA replication')
_add(['PALBOCICLIB','RIBOCICLIB','ABEMACICLIB','RO-3306',
      'ALVOCIDIB','DINACICLIB','CGP-60474',
      'NUTLIN-3A (-)','NUTLIN-3A','APR-246','RG7388','IDASANUTLIN','681640'], 'Cell cycle')
_add(['PACLITAXEL','DOCETAXEL','VINBLASTINE','VINCRISTINE','VINORELBINE',
      'EPOTHILONE-B','ALISERTIB','ZM-447439','BARASERTIB','TOZASERTIB',
      'BI-2536','VOLASERTIB','GSK461364',
      'S-TRITYL-L-CYSTEINE','ISPINESIB','MPS1-IN-1'], 'Mitosis')
_add(['BORTEZOMIB','CARFILZOMIB','MG-132','PEVONEDISTAT',
      '17-AAG','TANESPIMYCIN','AUY922','GANETESPIB','LUMINESPIB','SNX-2112'],
     'Protein stability and degradation')
_add(['NAVITOCLAX','ABT-737','VENETOCLAX','ABT-199',
      'AZD5582','BIRINAPANT','EMBELIN','LCL-161','YM-155','OBATOCLAX'], 'Apoptosis regulation')
_add(['VORINOSTAT','BELINOSTAT','PANOBINOSTAT','ENTINOSTAT',
      'AR-42','CAY10603','ACY-1215','TUBASTATIN A','TRICHOSTATIN A',
      'JQ1','I-BET-762','OTX015','APABETALONE',
      'EPZ-5676','PINOMETOSTAT','GSK343','EPZ004777','EI1',
      'UNC0638','CHAETOCIN','DECITABINE','AZACYTIDINE','PFI-3'], 'Chromatin histone acetylation')
_add(['PD-0325901','TRAMETINIB','SELUMETINIB','BINIMETINIB','COBIMETINIB',
      'REFAMETINIB','CI-1040','PIMASERTIB',
      'PLX-4720','DABRAFENIB','VEMURAFENIB','ENCORAFENIB',
      'SORAFENIB','AZ-628','SB-590885','TAK-632',
      'SCH772984','BVD-523','ULIXERTINIB','VX-11E'], 'ERK MAPK signaling')
_add(['GDC-0941','ALPELISIB','BUPARLISIB','PICTILISIB',
      'IDELALISIB','COPANLISIB','APITOLISIB','AMG-319','TASELISIB',
      'NVP-BEZ235','DACTOLISIB',
      'AZD8055','VISTUSERTIB','SAPANISERTIB','OSI-027',
      'SIROLIMUS','EVEROLIMUS','TEMSIROLIMUS','RAPAMYCIN',
      'MK-2206','AZD5363','IPATASERTIB','CAPIVASERTIB','UPROSERTIB',
      'AT13148','AZD6482','BX-795'], 'PI3K/MTOR signaling')
_add(['ERLOTINIB','GEFITINIB','LAPATINIB','NERATINIB',
      'AFATINIB','OSIMERTINIB','AZD3759',
      'AZD8931','CANERTINIB','SAPITINIB','AST-1306','CETUXIMAB'], 'EGFR signaling')
_add(['SUNITINIB','AXITINIB','PAZOPANIB','LENVATINIB',
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
      'PF-4708671'], 'RTK signaling')
_add(['TAMOXIFEN','BICALUTAMIDE','FULVESTRANT','DEXAMETHASONE','BEXAROTENE'], 'Hormone-related')
_add(['XAV-939','IWP-2','LGK-974','WNTC59',
      'CYCLOPAMINE','VISMODEGIB','SONIDEGIB',
      'SB-216763','CHIR-99021'], 'WNT signaling')
_add(['DORAMAPIMOD','AS601245','(5Z)-7-OXOZEAENOL','JNK INHIBITOR VIII'], 'JNK and p38 signaling')
_add(['AICAR','METFORMIN','AGI-5198','AGI-6780',
      'APO866','APO866, FK866','CAY10566','C-75','AR-12','PHENFORMIN'], 'Metabolism')
_add(['LENALIDOMIDE','THALIDOMIDE','POMALIDOMIDE',
      'RUXOLITINIB','TOFACITINIB','IBRUTINIB','BMS-345541'], 'Immune response')


def _map_drug_to_pathway(drug_name):
    """Duplicated from GDSC1.py map_drug_to_pathway()."""
    if pd.isna(drug_name):
        return None
    name = str(drug_name).strip().upper()
    if name in _DRUG_PATHWAY:
        return _DRUG_PATHWAY[name]
    for key, pw in _DRUG_PATHWAY.items():
        if key in name or name in key:
            return pw
    nl = name.lower()
    patterns = [
        (['parp','olaparib','talazoparib','rucaparib'], 'Genome integrity'),
        (['taxel','taxol','vincrist','vinblast'], 'Mitosis'),
        (['platin'], 'Genome integrity'),
        (['bortezomib','carfilzomib'], 'Protein stability and degradation'),
        (['vorinostat','panobinostat','hdac'], 'Chromatin histone acetylation'),
        (['palbociclib','ribociclib'], 'Cell cycle'),
        (['nutlin','mdm2'], 'Cell cycle'),
        (['venetoclax','navitoclax'], 'Apoptosis regulation'),
        (['hsp90','ganetespib'], 'Protein stability and degradation'),
        (['topotecan','camptothecin','etoposide'], 'Genome integrity'),
        (['mek','trametinib','selumetinib'], 'ERK MAPK signaling'),
        (['braf','dabrafenib','vemurafenib'], 'ERK MAPK signaling'),
        (['pi3k','mtor','rapamycin','everolimus'], 'PI3K/MTOR signaling'),
        (['egfr','erlotinib','gefitinib','afatinib'], 'EGFR signaling'),
        (['sunitinib','axitinib','imatinib','nilotinib'], 'RTK signaling'),
        (['tamoxifen','bicalutamide'], 'Hormone-related'),
        (['wnt','hedgehog','vismodegib'], 'WNT signaling'),
    ]
    for keywords, pw in patterns:
        if any(k in nl for k in keywords):
            return pw
    return None


_STRUCTURE_PW = {
    'Genome integrity', 'DNA replication', 'Cell cycle',
    'Protein stability and degradation', 'Mitosis',
    'Apoptosis regulation', 'Chromatin histone acetylation',
    'Chromatin histone methylation', 'Chromatin other',
}
_INPUT_PW = {
    'ERK MAPK signaling', 'PI3K/MTOR signaling', 'RTK signaling',
    'IGF1R signaling', 'EGFR signaling', 'Hormone-related',
    'Metabolism', 'WNT signaling', 'ABL signaling',
    'JNK and p38 signaling', 'Immune response',
}


def _classify_gdsc_pathway_only(pathway):
    """Pathway-only classification (matches GDSC2.py / briefing's 1.84×).
    No dose-based reclassification — purely on mechanism of action."""
    if pathway in _STRUCTURE_PW:
        return 'STRUCTURE'
    if pathway in _INPUT_PW:
        return 'INPUT'
    return None


def extract_gdsc(csv_path):
    """Load GDSC, classify by pathway only, return individual AUC values."""
    print("\n" + "=" * 60)
    print("  GDSC — Loading sanger-dose-response")
    print("=" * 60)

    df = pd.read_csv(csv_path)
    print(f"  {len(df):,} observations")

    auc_col = 'AUC_PUBLISHED' if 'AUC_PUBLISHED' in df.columns else 'AUC'

    df['PATHWAY_NAME'] = df['DRUG_NAME'].apply(_map_drug_to_pathway)
    df['PERTURBATION_TYPE'] = df['PATHWAY_NAME'].apply(_classify_gdsc_pathway_only)

    df_i = df.loc[df['PERTURBATION_TYPE'] == 'INPUT'].dropna(subset=[auc_col])
    df_s = df.loc[df['PERTURBATION_TYPE'] == 'STRUCTURE'].dropna(subset=[auc_col])

    # For GDSC, perturbation magnitude = 1 - AUC (AUC=1 means no effect)
    i_mag = (1.0 - df_i[auc_col].values)
    s_mag = (1.0 - df_s[auc_col].values)

    # Cluster IDs for cluster bootstrap (COSMIC_ID = cell line)
    ci_i = df_i['COSMIC_ID'].values.tolist()
    ci_s = df_s['COSMIC_ID'].values.tolist()
    n_clusters_i = len(set(ci_i))
    n_clusters_s = len(set(ci_s))

    print(f"  Input: n={len(i_mag):,}, mean mag={np.mean(i_mag):.4f}, clusters(cell lines)={n_clusters_i}")
    print(f"  Structure: n={len(s_mag):,}, mean mag={np.mean(s_mag):.4f}, clusters(cell lines)={n_clusters_s}")
    ratio = np.mean(s_mag) / np.mean(i_mag)
    print(f"  Ratio (mag means): {ratio:.4f}×")

    return {
        'domain': 'Cancer (GDSC)',
        'response_var': '1 - AUC (perturbation magnitude)',
        'i_values': i_mag.tolist(),
        's_values': s_mag.tolist(),
        'cluster_ids_i': ci_i,
        'cluster_ids_s': ci_s,
    }


# ════════════════════════════════════════════════════════════════
#  DOMAIN 3: YEAST (Yeast Phenome)
#  Source: ScriptYeast/RXVII.py — load_gaf() + select_chemical_screens()
# ════════════════════════════════════════════════════════════════

# GO terms — duplicated from RXVII.py lines 29-44
_YEAST_STRUCTURE_GO = {
    'GO:0006281','GO:0043161','GO:0006457','GO:0030433',
    'GO:0000278','GO:0000280','GO:0000281','GO:0051726','GO:0007346',
    'GO:0000082','GO:0000086','GO:0051301','GO:0006260','GO:0006261',
    'GO:0009272','GO:0071555','GO:0007005',
    'GO:0042254','GO:0042273','GO:0042274',
    'GO:0006325','GO:0006265','GO:0007059',
}
_YEAST_INPUT_GO = {
    'GO:0007165','GO:0000165','GO:0007264','GO:0007186',
    'GO:0031929','GO:0032008','GO:0038202','GO:0006468',
    'GO:0055085','GO:0006811','GO:0006812','GO:0006813','GO:0006814',
    'GO:0006826','GO:0006865','GO:0015078','GO:0034220','GO:0055072',
    'GO:0006970','GO:0009408','GO:0034599',
    'GO:0071470','GO:0071472','GO:0071474',
}


def _load_gaf(path):
    """Duplicated from RXVII.py load_gaf(). Returns ORF → class mapping."""
    gene_go = collections.defaultdict(set)
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
    orf_class = {}
    for gene, gos in gene_go.items():
        orf = gene_to_orf.get(gene)
        if not orf:
            continue
        is_s = bool(gos & _YEAST_STRUCTURE_GO)
        is_i = bool(gos & _YEAST_INPUT_GO)
        if is_s and not is_i:
            orf_class[orf] = 'STRUCTURE'
        elif is_i and not is_s:
            orf_class[orf] = 'INPUT'
    return orf_class


def _select_hillenmeyer(screens_path):
    """Duplicated from RXVII.py select_chemical_screens() — Hillenmeyer subset."""
    df = pd.read_csv(screens_path, sep='\t')
    hillen = df[df['paper'].str.contains('Hillenmeyer', na=False)]
    hillen_hom = hillen[hillen['collection'].str.contains('hom', na=False)]
    return set(hillen_hom['id'].astype(str))


def extract_yeast(matrix_path, screens_path, gaf_path):
    """Load Yeast Phenome, classify by GO, return individual severity values."""
    print("\n" + "=" * 60)
    print("  YEAST — Loading Yeast Phenome (hom, Hillenmeyer)")
    print("=" * 60)

    # 1. GO partition
    orf_class = _load_gaf(gaf_path)
    n_s = sum(1 for v in orf_class.values() if v == 'STRUCTURE')
    n_i = sum(1 for v in orf_class.values() if v == 'INPUT')
    print(f"  GO partition: {n_s} STRUCTURE, {n_i} INPUT")

    # 2. Hillenmeyer screen IDs
    hillen_ids = _select_hillenmeyer(screens_path)
    print(f"  Hillenmeyer screens: {len(hillen_ids)}")

    # 3. Load z-score matrix
    print(f"  Loading z-score matrix (this may take a few minutes)...")
    mat = pd.read_csv(matrix_path, sep='\t', index_col=0, low_memory=False)
    print(f"  Matrix: {mat.shape[0]} genes × {mat.shape[1]} screens")

    # 4. Match
    s_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'STRUCTURE']
    i_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'INPUT']
    hillen_cols = [c for c in mat.columns if str(c) in hillen_ids]
    print(f"  Matched: S={len(s_orfs)}, I={len(i_orfs)}, screens={len(hillen_cols)}")

    # 5. Severity = mean |z-score| across Hillenmeyer screens per gene
    s_severity = mat.loc[s_orfs, hillen_cols].abs().mean(axis=1).dropna().values
    i_severity = mat.loc[i_orfs, hillen_cols].abs().mean(axis=1).dropna().values

    ratio = np.mean(s_severity) / np.mean(i_severity)
    print(f"  Mean severity: S={np.mean(s_severity):.4f}, I={np.mean(i_severity):.4f}")
    print(f"  Ratio (means): {ratio:.4f}×")

    return {
        'domain': 'Yeast hom (Phenome)',
        'response_var': 'Mean |z-score| (Hillenmeyer)',
        'i_values': i_severity.tolist(),
        's_values': s_severity.tolist(),
    }


def _select_all_chemical_screens(screens_path):
    """Duplicated from RXVII.py select_chemical_screens() — all chemical subset."""
    df = pd.read_csv(screens_path, sep='\t')
    growth = df[df['phenotype'].str.contains('growth', case=False, na=False)]
    std_kw = ['standard', 'control', 'untreated', 'DMSO']
    chem = growth[~growth['conditionset'].str.lower().str.contains('|'.join(std_kw), na=True)]
    has_conc = chem[chem['conditionset'].str.contains(r'\[.*[uUnNmMg%]', na=False)]
    return set(has_conc['id'].astype(str))


def extract_yeast_het(matrix_path, screens_path, gaf_path):
    """Load Yeast Phenome het, classify by GO, return individual severity values.
    Confirmatory test (pre-registered OSF DOI: 10.17605/OSF.IO/S7CN9).
    No Hillenmeyer screens in het → uses all chemical screens."""
    print("\n" + "=" * 60)
    print("  YEAST HET — Loading Yeast Phenome (het, all chemical)")
    print("=" * 60)

    # 1. GO partition (same as hom)
    orf_class = _load_gaf(gaf_path)
    n_s = sum(1 for v in orf_class.values() if v == 'STRUCTURE')
    n_i = sum(1 for v in orf_class.values() if v == 'INPUT')
    print(f"  GO partition: {n_s} STRUCTURE, {n_i} INPUT")

    # 2. All chemical screen IDs (no Hillenmeyer in het collection)
    chem_ids = _select_all_chemical_screens(screens_path)
    print(f"  All chemical screens: {len(chem_ids)}")

    # 3. Load z-score matrix
    print(f"  Loading z-score matrix (this may take a few minutes)...")
    mat = pd.read_csv(matrix_path, sep='\t', index_col=0, low_memory=False)
    print(f"  Matrix: {mat.shape[0]} genes × {mat.shape[1]} screens")

    # 4. Match
    s_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'STRUCTURE']
    i_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'INPUT']
    chem_cols = [c for c in mat.columns if str(c) in chem_ids]
    print(f"  Matched: S={len(s_orfs)}, I={len(i_orfs)}, screens={len(chem_cols)}")

    # 5. Severity = mean |z-score| across all-chemical screens per gene
    s_severity = mat.loc[s_orfs, chem_cols].abs().mean(axis=1).dropna().values
    i_severity = mat.loc[i_orfs, chem_cols].abs().mean(axis=1).dropna().values

    ratio = np.mean(s_severity) / np.mean(i_severity)
    print(f"  Mean severity: S={np.mean(s_severity):.4f}, I={np.mean(i_severity):.4f}")
    print(f"  Ratio (means): {ratio:.4f}×")

    return {
        'domain': 'Yeast het (Phenome)',
        'response_var': 'Mean |z-score| (all chemical)',
        'i_values': i_severity.tolist(),
        's_values': s_severity.tolist(),
        'confirmatory': True,
    }


# ════════════════════════════════════════════════════════════════
#  DOMAIN 4: MICROBIOME (MDSINE2)
#  Source: ScriptMDSINE2/04_robustness_metrics.py
#  Needs: llvmlite patch + mdsine2 + MDSINE2_Paper pkl files
# ════════════════════════════════════════════════════════════════

def _patch_llvmlite():
    """Duplicated from ScriptMDSINE2/04_robustness_metrics.py lines 50-86."""
    import types
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


def extract_microbiome(mdsine2_paper_path):
    """Load MDSINE2, compute per-sample BC from global baseline, return individual values."""
    print("\n" + "=" * 60)
    print("  MICROBIOME — Loading MDSINE2 (dysbiotic cohort)")
    print("=" * 60)

    _patch_llvmlite()

    try:
        import mdsine2 as md2
    except ImportError:
        print("  ERROR: mdsine2 not installed. Skipping.")
        return None

    data_base = Path(mdsine2_paper_path) / 'datasets' / 'gibson'
    h_pkl = data_base / 'healthy' / 'preprocessed' / 'gibson_healthy_agg_filtered.pkl'
    u_pkl = data_base / 'uc' / 'preprocessed' / 'gibson_uc_agg_filtered.pkl'

    for p in [h_pkl, u_pkl]:
        if not p.exists():
            print(f"  ERROR: {p} not found. Skipping microbiome.")
            return None

    study_u = md2.Study.load(str(u_pkl))
    print(f"  Dysbiotic: {len(study_u.taxa)} taxa, {sum(1 for _ in study_u)} subjects")

    phases = {
        'equilibration': (0, 21.5), 'HFD': (21.5, 28.5),
        'recovery_1': (28.5, 35.5), 'vancomycin': (35.5, 42.5),
        'recovery_2': (42.5, 50.5), 'gentamicin': (50.5, 57.5),
        'recovery_3': (57.5, 65.0),
    }

    # Extract data — duplicated from 04_robustness_metrics.py extract_data()
    data = []
    for subj in study_u:
        M = subj.matrix()
        rel_m = M['rel']
        times = subj.times
        for i, t in enumerate(times):
            data.append({
                'subject': subj.name, 'time': t,
                'rel_profile': rel_m[:, i],
            })

    # Compute BC from global baseline — duplicated from compute_rxvii_all_metrics()
    subjects = sorted(set(r['subject'] for r in data))
    input_bc = []
    hw_bc = []

    recovery_map = {
        'HFD':        ('input',    28.5, 35.5),
        'vancomycin': ('hardware', 42.5, 50.5),
        'gentamicin': ('hardware', 57.5, 65.0),
    }

    for subj in subjects:
        sdata = sorted([r for r in data if r['subject'] == subj], key=lambda x: x['time'])

        # Global baseline: late equilibration (t=15 to 21.5)
        baseline_samples = [r for r in sdata if 15 <= r['time'] < 21.5]
        if len(baseline_samples) < 3:
            continue
        baseline_rel = np.mean([r['rel_profile'] for r in baseline_samples], axis=0)
        baseline_rel = baseline_rel / (baseline_rel.sum() + 1e-15)

        for pert_name, (ptype, pert_end, phase_end) in recovery_map.items():
            # Late recovery only (t_since_pert >= 4)
            late_samples = [r for r in sdata if pert_end + 4 <= r['time'] < phase_end]
            for r in late_samples:
                profile = r['rel_profile']
                profile = profile / (profile.sum() + 1e-15)
                bc = spatial.distance.braycurtis(baseline_rel, profile)
                if ptype == 'input':
                    input_bc.append(bc)
                else:
                    hw_bc.append(bc)

    input_bc = np.array(input_bc)
    hw_bc = np.array(hw_bc)

    print(f"  Input (HFD late recovery): n={len(input_bc)}, mean BC={np.mean(input_bc):.4f}")
    print(f"  Structure (abx late recovery): n={len(hw_bc)}, mean BC={np.mean(hw_bc):.4f}")
    ratio = np.mean(hw_bc) / np.mean(input_bc)
    print(f"  Ratio (means): {ratio:.4f}×")

    return {
        'domain': 'Microbiome (MDSINE2)',
        'response_var': 'Bray-Curtis from baseline',
        'i_values': input_bc.tolist(),
        's_values': hw_bc.tolist(),
    }


# ════════════════════════════════════════════════════════════════
#  EXTRACTION ORCHESTRATOR
# ════════════════════════════════════════════════════════════════

def _cluster_bootstrap_ratio(sv, iv, cluster_ids_s=None, cluster_ids_i=None,
                              n_boot=10000, seed=42):
    """Bootstrap CI on ratio of means, with optional cluster resampling.
    When cluster_ids are provided, resamples at the cluster level (e.g. cell lines,
    sites) to account for intra-cluster correlation. Otherwise, standard iid bootstrap."""
    rng = np.random.RandomState(seed)
    boot = []

    if cluster_ids_s is not None and cluster_ids_i is not None:
        # Group values by cluster
        from collections import defaultdict
        groups_s = defaultdict(list)
        for val, cid in zip(sv, cluster_ids_s):
            groups_s[cid].append(val)
        groups_i = defaultdict(list)
        for val, cid in zip(iv, cluster_ids_i):
            groups_i[cid].append(val)

        ckeys_s = list(groups_s.keys())
        ckeys_i = list(groups_i.keys())
        cvals_s = [np.array(groups_s[k]) for k in ckeys_s]
        cvals_i = [np.array(groups_i[k]) for k in ckeys_i]

        for _ in range(n_boot):
            # Resample clusters with replacement
            idx_s = rng.choice(len(ckeys_s), len(ckeys_s), replace=True)
            idx_i = rng.choice(len(ckeys_i), len(ckeys_i), replace=True)
            sb = np.concatenate([cvals_s[j] for j in idx_s])
            ib = np.concatenate([cvals_i[j] for j in idx_i])
            if np.mean(ib) > 0:
                boot.append(np.mean(sb) / np.mean(ib))
    else:
        # Standard iid bootstrap
        for _ in range(n_boot):
            sb = rng.choice(sv, len(sv), replace=True)
            ib = rng.choice(iv, len(iv), replace=True)
            if np.mean(ib) > 0:
                boot.append(np.mean(sb) / np.mean(ib))

    boot = np.array(boot)
    ci = np.percentile(boot, [2.5, 97.5])
    return ci, boot


def run_extract(args):
    """Extract individual distributions from all available domains."""
    domains = []

    if args.reef_csv:
        domains.append(extract_reef(args.reef_csv))
    else:
        print("\n  [SKIP] Reef: --reef-csv not provided")

    if args.gdsc_csv:
        domains.append(extract_gdsc(args.gdsc_csv))
    else:
        print("\n  [SKIP] GDSC: --gdsc-csv not provided")

    if args.yeast_matrix and args.yeast_screens and args.yeast_gaf:
        domains.append(extract_yeast(args.yeast_matrix, args.yeast_screens, args.yeast_gaf))
    else:
        print("\n  [SKIP] Yeast hom: --yeast-matrix/--yeast-screens/--yeast-gaf not all provided")

    if args.yeast_het_matrix and args.yeast_het_screens and args.yeast_gaf:
        domains.append(extract_yeast_het(args.yeast_het_matrix, args.yeast_het_screens, args.yeast_gaf))
    else:
        print("\n  [SKIP] Yeast het: --yeast-het-matrix/--yeast-het-screens not provided")

    if args.mdsine2_paper:
        r = extract_microbiome(args.mdsine2_paper)
        if r:
            domains.append(r)
    else:
        print("\n  [SKIP] Microbiome: --mdsine2-paper not provided")

    # Add computed stats to each domain
    for d in domains:
        iv = np.array(d['i_values'])
        sv = np.array(d['s_values'])

        ratio_mean = np.mean(sv) / np.mean(iv)
        ratio_median = np.median(sv) / np.median(iv)

        # Bootstrap CI on ratio of means — cluster bootstrap when cluster_ids available
        ci_ids_s = d.get('cluster_ids_s')
        ci_ids_i = d.get('cluster_ids_i')
        has_clusters = ci_ids_s is not None and ci_ids_i is not None
        ci, boot = _cluster_bootstrap_ratio(sv, iv, ci_ids_s, ci_ids_i)
        bootstrap_type = 'cluster' if has_clusters else 'iid'

        if has_clusters:
            n_cl_i = len(set(ci_ids_i))
            n_cl_s = len(set(ci_ids_s))
            print(f"  {d['domain']}: cluster bootstrap ({n_cl_s} S clusters, {n_cl_i} I clusters)")
        else:
            print(f"  {d['domain']}: iid bootstrap (n_S={len(sv)}, n_I={len(iv)})")

        # Mann-Whitney
        U, p = stats.mannwhitneyu(sv, iv, alternative='greater')
        pooled_std = np.sqrt((np.var(sv) + np.var(iv)) / 2)
        d_cohen = (np.mean(sv) - np.mean(iv)) / pooled_std if pooled_std > 0 else 0

        d['ratio_mean'] = ratio_mean
        d['ratio_median'] = ratio_median
        d['ci_95'] = [float(ci[0]), float(ci[1])]
        d['bootstrap_type'] = bootstrap_type
        d['confirmatory'] = d.get('confirmatory', False)
        d['p'] = float(p)
        d['cohen_d'] = float(d_cohen)
        d['n_i'] = len(iv)
        d['n_s'] = len(sv)
        d['skew_i'] = float(stats.skew(iv))
        d['skew_s'] = float(stats.skew(sv))
        d['kurtosis_i'] = float(stats.kurtosis(iv))
        d['kurtosis_s'] = float(stats.kurtosis(sv))

        print(f"    → ratio={ratio_mean:.3f}× CI [{ci[0]:.3f}, {ci[1]:.3f}] ({bootstrap_type})")

        # Drop cluster_ids before JSON serialization (too large)
        d.pop('cluster_ids_i', None)
        d.pop('cluster_ids_s', None)

    # Verification against reference values
    print("\n" + "=" * 60)
    print("  VERIFICATION — ratios vs reference table")
    print("=" * 60)
    ref = {
        'Microbiome (MDSINE2)': 1.61,
        'Reef (GCBD)': 1.80,
        'Cancer (GDSC)': 1.84,
        'Yeast hom (Phenome)': 1.42,
        'Yeast het (Phenome)': 1.18,
    }
    for d in domains:
        r = d['ratio_mean']
        expected = ref.get(d['domain'])
        if expected:
            delta = abs(r - expected)
            status = "OK" if delta < 0.05 else f"ECART {delta:.3f}"
            print(f"  {d['domain']:<25s}  computed={r:.3f}×  expected≈{expected:.2f}×  [{status}]")
        else:
            print(f"  {d['domain']:<25s}  computed={r:.3f}×  (no reference)")

    # Save
    # Strip raw values for a lighter summary, keep them in full file
    with open(DATA_FILE, 'w') as f:
        json.dump(domains, f, indent=2)
    print(f"\n  Saved to {DATA_FILE}")
    return domains


# ════════════════════════════════════════════════════════════════
#  TASK 1: META-ANALYSIS + FOREST PLOT
# ════════════════════════════════════════════════════════════════

def run_meta(data):
    """Random-effects meta-analysis on log-ratio, produce forest plot."""
    print("\n" + "=" * 60)
    print("  TASK 1 — Meta-analysis (random-effects, DerSimonian-Laird)")
    print("=" * 60)

    # Work in log-ratio space
    names = []
    yi = []      # log(ratio)
    sei = []     # SE of log(ratio), derived from bootstrap CI
    is_confirmatory = []

    for d in data:
        ln_r = np.log(d['ratio_mean'])
        ci_lo, ci_hi = d['ci_95']
        ln_lo, ln_hi = np.log(ci_lo), np.log(ci_hi)
        se = (ln_hi - ln_lo) / (2 * 1.96)

        names.append(d['domain'])
        yi.append(ln_r)
        sei.append(se)
        is_confirmatory.append(d.get('confirmatory', False))

    yi = np.array(yi)
    sei = np.array(sei)
    wi = 1.0 / sei**2    # inverse-variance weights (fixed-effects)
    k = len(yi)

    # Q statistic (Cochran)
    mu_fe = np.sum(wi * yi) / np.sum(wi)
    Q = np.sum(wi * (yi - mu_fe)**2)
    df_Q = k - 1
    p_Q = 1.0 - stats.chi2.cdf(Q, df_Q)

    # I² (Higgins)
    I2 = max(0, (Q - df_Q) / Q) * 100 if Q > 0 else 0

    # tau² (DerSimonian-Laird)
    C = np.sum(wi) - np.sum(wi**2) / np.sum(wi)
    tau2 = max(0, (Q - df_Q) / C)

    # Random-effects weights
    wi_re = 1.0 / (sei**2 + tau2)
    mu_re = np.sum(wi_re * yi) / np.sum(wi_re)
    se_re = 1.0 / np.sqrt(np.sum(wi_re))

    re_lo = mu_re - 1.96 * se_re
    re_hi = mu_re + 1.96 * se_re

    # Prediction interval: PI = μ_RE ± t_{k-2, 0.975} × √(τ² + SE²_pooled)
    if k > 2:
        t_val = stats.t.ppf(0.975, df=k - 2)
        pi_se = np.sqrt(tau2 + se_re**2)
        pi_lo = mu_re - t_val * pi_se
        pi_hi = mu_re + t_val * pi_se
    else:
        pi_lo = pi_hi = np.nan

    print(f"\n  Studies: {k}")
    for i in range(k):
        bt = data[i].get('bootstrap_type', 'iid')
        conf_tag = ' [CONFIRMATORY]' if is_confirmatory[i] else ''
        print(f"    {names[i]}: ln(r)={yi[i]:.4f}, SE={sei[i]:.4f} ({bt}){conf_tag}")
    print(f"\n  Q = {Q:.2f}, df = {df_Q}, p = {p_Q:.4f}")
    print(f"  I² = {I2:.1f}%")
    print(f"  τ² = {tau2:.6f}")
    print(f"  Pooled ratio (RE): {np.exp(mu_re):.3f}× [{np.exp(re_lo):.3f}, {np.exp(re_hi):.3f}]")
    if not np.isnan(pi_lo):
        print(f"  Prediction interval: {np.exp(pi_lo):.3f}× to {np.exp(pi_hi):.3f}× "
              f"(t_{{{k-2}}} = {t_val:.3f})")
        print(f"    PI {'excludes' if pi_lo > 0 else 'INCLUDES'} 1.0 (ln=0)")

    # ── Forest plot ──
    fig, ax = plt.subplots(figsize=(8, 0.6 * k + 3.0))

    y_pos = np.arange(k, 0, -1)
    ci_lo_plot = yi - 1.96 * sei
    ci_hi_plot = yi + 1.96 * sei

    # Determine right margin for text
    text_x = max(ci_hi_plot) + 0.05
    if not np.isnan(pi_hi):
        text_x = max(text_x, pi_hi + 0.05)

    # Individual studies
    for i in range(k):
        marker = 's' if is_confirmatory[i] else 'o'
        color = '#2E7D32' if is_confirmatory[i] else '#1565C0'
        ax.plot(yi[i], y_pos[i], marker, color=color, markersize=8, zorder=3)
        ax.plot([ci_lo_plot[i], ci_hi_plot[i]], [y_pos[i], y_pos[i]],
                '-', color=color, linewidth=2, zorder=2)
        # Label
        conf_tag = ' ■' if is_confirmatory[i] else ''
        ratio_str = f"{np.exp(yi[i]):.2f}× [{np.exp(ci_lo_plot[i]):.2f}, {np.exp(ci_hi_plot[i]):.2f}]{conf_tag}"
        ax.text(text_x, y_pos[i], ratio_str,
                va='center', fontsize=9, color='#333')

    # Diamond for pooled estimate
    diamond_y = -0.2
    diamond_x = [re_lo, mu_re, re_hi, mu_re]
    diamond_dy = [diamond_y, diamond_y - 0.25, diamond_y, diamond_y + 0.25]
    ax.fill(diamond_x, diamond_dy, color='#E53935', alpha=0.7, zorder=3)
    ax.text(text_x, diamond_y,
            f"Pooled: {np.exp(mu_re):.2f}× [{np.exp(re_lo):.2f}, {np.exp(re_hi):.2f}]",
            va='center', fontsize=9, fontweight='bold', color='#B71C1C')

    # Prediction interval bar
    pi_y = -0.8
    if not np.isnan(pi_lo):
        ax.plot([pi_lo, pi_hi], [pi_y, pi_y], '-', color='#FF6F00', linewidth=3, alpha=0.6, zorder=2)
        ax.plot(mu_re, pi_y, 'D', color='#FF6F00', markersize=6, zorder=3)
        pi_str = f"PI: {np.exp(pi_lo):.2f}× to {np.exp(pi_hi):.2f}×"
        ax.text(text_x, pi_y, pi_str,
                va='center', fontsize=9, color='#E65100')

    ax.axvline(0, color='grey', linestyle=':', linewidth=1, zorder=1)

    # Y-axis labels
    all_y = list(y_pos) + [diamond_y]
    all_labels = names + ['Pooled (RE)']
    if not np.isnan(pi_lo):
        all_y.append(pi_y)
        all_labels.append('Prediction')
    ax.set_yticks(all_y)
    ax.set_yticklabels(all_labels, fontsize=10)

    ax.set_xlabel('ln(Structure / Input)', fontsize=11)
    ax.set_title(f'Forest plot — R-XVII ratio (I² = {I2:.0f}%, p_het = {p_Q:.3f})', fontsize=12)

    # Secondary x-axis: ratio scale
    ax2 = ax.twiny()
    ticks_ratio = [0.8, 1.0, 1.2, 1.4, 1.6, 1.8, 2.0, 2.5, 3.0]
    ax2.set_xlim([np.exp(x) for x in ax.get_xlim()])
    ax2.set_xscale('log')
    ax2.set_xticks(ticks_ratio)
    ax2.set_xticklabels([f'{t:.1f}×' for t in ticks_ratio], fontsize=9)
    ax2.set_xlabel('Ratio S/I', fontsize=10)

    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    plt.tight_layout()
    plt.savefig('forest_plot.png', dpi=300, bbox_inches='tight')
    plt.savefig('forest_plot.svg', bbox_inches='tight')
    print(f"\n  Saved: forest_plot.png, forest_plot.svg")
    plt.close()

    result = {'Q': Q, 'df': df_Q, 'p_het': p_Q, 'I2': I2, 'tau2': tau2,
              'pooled_ratio': np.exp(mu_re), 'pooled_ci': [np.exp(re_lo), np.exp(re_hi)]}
    if not np.isnan(pi_lo):
        result['prediction_interval'] = [np.exp(pi_lo), np.exp(pi_hi)]
    return result


# ════════════════════════════════════════════════════════════════
#  TASK 3: DISTRIBUTION HISTOGRAMS (ρ_means vs ρ_medians)
# ════════════════════════════════════════════════════════════════

def run_distrib(data):
    """Panel of I vs S distributions for each domain."""
    print("\n" + "=" * 60)
    print("  TASK 3 — Distribution histograms")
    print("=" * 60)

    n = len(data)
    cols = 2
    rows = (n + 1) // 2
    fig, axes = plt.subplots(rows, cols, figsize=(7 * cols, 4.5 * rows))
    if n == 1:
        axes = np.array([[axes]])
    axes = axes.flatten()

    for idx, d in enumerate(data):
        ax = axes[idx]
        iv = np.array(d['i_values'])
        sv = np.array(d['s_values'])

        # Determine bins adaptively
        all_vals = np.concatenate([iv, sv])
        lo, hi = np.percentile(all_vals, [0.5, 99.5])
        bins = np.linspace(lo, hi, 60)

        ax.hist(iv, bins=bins, alpha=0.5, density=True,
                color='#1565C0', label=f'Input (n={len(iv):,})')
        ax.hist(sv, bins=bins, alpha=0.5, density=True,
                color='#C62828', label=f'Structure (n={len(sv):,})')

        # Means
        ax.axvline(np.mean(iv), color='#0D47A1', ls='--', lw=1.5, label=f'μ_I={np.mean(iv):.3f}')
        ax.axvline(np.mean(sv), color='#B71C1C', ls='--', lw=1.5, label=f'μ_S={np.mean(sv):.3f}')

        # Medians
        ax.axvline(np.median(iv), color='#0D47A1', ls=':', lw=1.5, label=f'med_I={np.median(iv):.3f}')
        ax.axvline(np.median(sv), color='#B71C1C', ls=':', lw=1.5, label=f'med_S={np.median(sv):.3f}')

        ax.set_title(d['domain'], fontsize=11, fontweight='bold')
        ax.set_xlabel(d['response_var'], fontsize=9)
        ax.set_ylabel('Density', fontsize=9)
        ax.legend(fontsize=7, loc='upper right')

        # Annotate ratios
        r_mean = d['ratio_mean']
        r_med = d['ratio_median']
        ax.text(0.02, 0.95, f'ρ_means={r_mean:.2f}×  ρ_medians={r_med:.2f}×',
                transform=ax.transAxes, fontsize=8, va='top',
                bbox=dict(boxstyle='round,pad=0.3', facecolor='wheat', alpha=0.7))

        # Annotate skewness
        ax.text(0.02, 0.85, f'skew(S)={d["skew_s"]:.2f}  skew(I)={d["skew_i"]:.2f}',
                transform=ax.transAxes, fontsize=7, va='top', color='#555')

    # Hide unused axes
    for j in range(n, len(axes)):
        axes[j].set_visible(False)

    plt.suptitle('Distributions: Input vs Structure per domain\n'
                 '(dashed = mean, dotted = median)',
                 fontsize=13, fontweight='bold', y=1.01)
    plt.tight_layout()
    plt.savefig('distributions_panel.png', dpi=300, bbox_inches='tight')
    plt.savefig('distributions_panel.svg', bbox_inches='tight')
    print(f"\n  Saved: distributions_panel.png, distributions_panel.svg")
    plt.close()

    # Summary paragraph
    print("\n  DISTRIBUTION SUMMARY:")
    for d in data:
        print(f"    {d['domain']}: skew(S)={d['skew_s']:.2f}, skew(I)={d['skew_i']:.2f}, "
              f"kurtosis(S)={d['kurtosis_s']:.2f}, kurtosis(I)={d['kurtosis_i']:.2f}")
        delta_skew = d['skew_s'] - d['skew_i']
        print(f"      → S {'more' if delta_skew > 0 else 'less'} right-skewed than I "
              f"(Δskew={delta_skew:+.2f})")
        print(f"      → ρ_means={d['ratio_mean']:.3f}×, ρ_medians={d['ratio_median']:.3f}× "
              f"(divergence={abs(d['ratio_mean'] - d['ratio_median']):.3f})")


# ════════════════════════════════════════════════════════════════
#  GRADIENT TESTS — Intra-domain severity stratification
# ════════════════════════════════════════════════════════════════

def _bootstrap_ratio(s_vals, i_vals, n_boot=10000, seed=42):
    """Quick iid bootstrap CI on ratio of means."""
    rng = np.random.RandomState(seed)
    boot = []
    for _ in range(n_boot):
        sb = rng.choice(s_vals, len(s_vals), replace=True)
        ib = rng.choice(i_vals, len(i_vals), replace=True)
        if np.mean(ib) > 0:
            boot.append(np.mean(sb) / np.mean(ib))
    return np.percentile(boot, [2.5, 97.5])


def _gradient_barplot(rows, title, ylabel, filename):
    """Generic barplot for gradient results. rows = list of dicts with
    'label', 'ratio', 'ci_lo', 'ci_hi'. First row = INPUT (reference)."""
    fig, ax = plt.subplots(figsize=(6, 4))
    labels = [r['label'] for r in rows]
    ratios = [r['ratio'] for r in rows]
    ci_lo = [r['ci_lo'] for r in rows]
    ci_hi = [r['ci_hi'] for r in rows]
    errs = [[r - lo for r, lo in zip(ratios, ci_lo)],
            [hi - r for r, hi in zip(ratios, ci_hi)]]
    colors = ['#1565C0'] + ['#C62828'] * (len(rows) - 1)
    x = np.arange(len(rows))
    ax.bar(x, ratios, yerr=errs, color=colors, alpha=0.8,
           edgecolor='black', linewidth=0.5, capsize=4)
    ax.axhline(1.0, color='grey', ls=':', lw=1)
    ax.set_xticks(x)
    ax.set_xticklabels(labels, fontsize=9)
    ax.set_ylabel(ylabel, fontsize=10)
    ax.set_title(title, fontsize=11)
    for i, r in enumerate(rows):
        n_label = f"n={r['n']:,}" if r['n'] < 100000 else f"n={r['n']//1000}k"
        ax.text(i, ratios[i] + errs[1][i] + 0.02, n_label,
                ha='center', va='bottom', fontsize=8, color='#555')
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    plt.tight_layout()
    plt.savefig(filename, dpi=300, bbox_inches='tight')
    print(f"  Saved: {filename}")
    plt.close()


def gradient_reef(csv_path):
    """Test A — Reef: gradient by DHW severity strata."""
    print("\n" + "=" * 60)
    print("  GRADIENT A — Reef (DHW strata)")
    print("=" * 60)

    df = pd.read_csv(csv_path)
    rn = {'Percent_Bleaching': 'bleaching', 'SSTA_DHW': 'dhw',
          'Cyclone_Frequency': 'cyclone_freq'}
    df = df.rename(columns=rn)
    for c in ['bleaching', 'dhw', 'cyclone_freq']:
        if c in df.columns:
            df[c] = pd.to_numeric(df[c], errors='coerce')
    df = df.dropna(subset=['bleaching', 'dhw'])

    dhw = df['dhw'].fillna(0)
    cyc = df['cyclone_freq'].fillna(0)
    cyc_med = cyc[cyc > 0].median() if (cyc > 0).any() else 999

    # INPUT (unchanged)
    inp = df.loc[(dhw >= 4) & (dhw < 8) & (cyc <= cyc_med), 'bleaching'].values

    # Structure strata
    strata = {
        'S_low (8≤DHW<12)':  df.loc[(dhw >= 8) & (dhw < 12) & (cyc <= cyc_med * 1.5), 'bleaching'].values,
        'S_mid (12≤DHW<16)': df.loc[((dhw >= 12) & (dhw < 16)) | (cyc > cyc_med * 1.5), 'bleaching'].values,
        'S_high (DHW≥16)':   df.loc[dhw >= 16, 'bleaching'].values,
    }

    rows = [{'label': 'INPUT', 'n': len(inp), 'mean': np.mean(inp),
             'ratio': 1.0, 'ci_lo': 1.0, 'ci_hi': 1.0}]

    print(f"\n  {'Stratum':<22s} {'n':>6s} {'mean%':>8s} {'ratio':>8s} {'CI 95%':>18s}")
    print("  " + "-" * 66)
    print(f"  {'INPUT':<22s} {len(inp):>6d} {np.mean(inp):>8.2f} {'(ref)':>8s}")

    for label, sv in strata.items():
        if len(sv) < 5:
            print(f"  {label:<22s} {len(sv):>6d}  [TOO FEW]")
            continue
        ratio = np.mean(sv) / np.mean(inp)
        ci = _bootstrap_ratio(sv, inp)
        fragile = ' ⚠' if len(sv) < 30 else ''
        print(f"  {label:<22s} {len(sv):>6d} {np.mean(sv):>8.2f} {ratio:>8.3f}  [{ci[0]:.3f}, {ci[1]:.3f}]{fragile}")
        rows.append({'label': label, 'n': len(sv), 'mean': float(np.mean(sv)),
                     'ratio': float(ratio), 'ci_lo': float(ci[0]), 'ci_hi': float(ci[1])})

    _gradient_barplot(rows, 'Gradient A — Reef: ratio by DHW stratum',
                      'Ratio vs INPUT', 'gradient_reef.png')

    with open('gradient_reef.json', 'w') as f:
        json.dump(rows, f, indent=2)
    return rows


def gradient_gdsc(csv_path):
    """Test B — GDSC: gradient by drug potency terciles."""
    print("\n" + "=" * 60)
    print("  GRADIENT B — GDSC (drug potency strata)")
    print("=" * 60)

    df = pd.read_csv(csv_path)
    auc_col = 'AUC_PUBLISHED' if 'AUC_PUBLISHED' in df.columns else 'AUC'
    df['PATHWAY_NAME'] = df['DRUG_NAME'].apply(_map_drug_to_pathway)
    df['PERTURBATION_TYPE'] = df['PATHWAY_NAME'].apply(_classify_gdsc_pathway_only)

    # INPUT arm (full)
    df_inp = df.loc[df['PERTURBATION_TYPE'] == 'INPUT'].dropna(subset=[auc_col])
    inp_mag = (1.0 - df_inp[auc_col].values)
    inp_clusters = df_inp['COSMIC_ID'].values

    # STRUCTURE drugs: compute per-drug median AUC
    df_str = df.loc[df['PERTURBATION_TYPE'] == 'STRUCTURE'].dropna(subset=[auc_col])
    drug_median_auc = df_str.groupby('DRUG_NAME')[auc_col].median()

    # Terciles of drug potency (low AUC = potent)
    t1, t2 = np.percentile(drug_median_auc.values, [33.33, 66.67])
    drugs_potent = set(drug_median_auc[drug_median_auc <= t1].index)
    drugs_mid = set(drug_median_auc[(drug_median_auc > t1) & (drug_median_auc <= t2)].index)
    drugs_weak = set(drug_median_auc[drug_median_auc > t2].index)

    print(f"  Drug potency terciles: potent(med AUC≤{t1:.3f}): {len(drugs_potent)}, "
          f"mid({t1:.3f}<AUC≤{t2:.3f}): {len(drugs_mid)}, "
          f"weak(AUC>{t2:.3f}): {len(drugs_weak)}")

    strata = {
        'S_weak':   df_str[df_str['DRUG_NAME'].isin(drugs_weak)],
        'S_mid':    df_str[df_str['DRUG_NAME'].isin(drugs_mid)],
        'S_potent': df_str[df_str['DRUG_NAME'].isin(drugs_potent)],
    }

    rows = [{'label': 'INPUT', 'n': len(inp_mag), 'n_drugs': df_inp['DRUG_NAME'].nunique(),
             'mean': float(np.mean(inp_mag)), 'ratio': 1.0, 'ci_lo': 1.0, 'ci_hi': 1.0}]

    print(f"\n  {'Stratum':<12s} {'n_obs':>8s} {'n_drugs':>8s} {'mean_mag':>10s} {'ratio':>8s} {'CI 95%':>18s}")
    print("  " + "-" * 68)
    print(f"  {'INPUT':<12s} {len(inp_mag):>8,d} {df_inp['DRUG_NAME'].nunique():>8d} "
          f"{np.mean(inp_mag):>10.4f} {'(ref)':>8s}")

    for label, df_s in strata.items():
        sv = (1.0 - df_s[auc_col].values)
        n_drugs = df_s['DRUG_NAME'].nunique()
        ratio = np.mean(sv) / np.mean(inp_mag)

        # Cluster bootstrap by cell line
        ci, _ = _cluster_bootstrap_ratio(
            sv, inp_mag,
            df_s['COSMIC_ID'].values.tolist(),
            inp_clusters.tolist())

        fragile = ' ⚠' if len(sv) < 30 else ''
        print(f"  {label:<12s} {len(sv):>8,d} {n_drugs:>8d} {np.mean(sv):>10.4f} "
              f"{ratio:>8.3f}  [{ci[0]:.3f}, {ci[1]:.3f}]{fragile}")
        rows.append({'label': label, 'n': len(sv), 'n_drugs': n_drugs,
                     'mean': float(np.mean(sv)),
                     'ratio': float(ratio), 'ci_lo': float(ci[0]), 'ci_hi': float(ci[1])})

    _gradient_barplot(rows, 'Gradient B — GDSC: STRUCTURE by drug potency',
                      'Ratio vs INPUT', 'gradient_gdsc.png')

    # ── CONTROL: same stratification on INPUT drugs ──
    print(f"\n  CONTROL — INPUT drugs stratified by potency:")
    inp_drug_median = df_inp.groupby('DRUG_NAME')[auc_col].median()
    it1, it2 = np.percentile(inp_drug_median.values, [33.33, 66.67])
    inp_potent = set(inp_drug_median[inp_drug_median <= it1].index)
    inp_mid_d = set(inp_drug_median[(inp_drug_median > it1) & (inp_drug_median <= it2)].index)
    inp_weak = set(inp_drug_median[inp_drug_median > it2].index)

    print(f"  INPUT terciles: potent(≤{it1:.3f}): {len(inp_potent)}, "
          f"mid({it1:.3f}–{it2:.3f}): {len(inp_mid_d)}, weak(>{it2:.3f}): {len(inp_weak)}")

    inp_strata = {
        'I_weak':   df_inp[df_inp['DRUG_NAME'].isin(inp_weak)],
        'I_mid':    df_inp[df_inp['DRUG_NAME'].isin(inp_mid_d)],
        'I_potent': df_inp[df_inp['DRUG_NAME'].isin(inp_potent)],
    }

    ctrl_rows = []
    print(f"  {'Stratum':<12s} {'n_obs':>8s} {'n_drugs':>8s} {'mean_mag':>10s} {'ratio':>8s} {'CI 95%':>18s}")
    print("  " + "-" * 68)

    for label, df_i in inp_strata.items():
        iv = (1.0 - df_i[auc_col].values)
        n_drugs = df_i['DRUG_NAME'].nunique()
        ratio = np.mean(iv) / np.mean(inp_mag)
        ci = _bootstrap_ratio(iv, inp_mag)
        print(f"  {label:<12s} {len(iv):>8,d} {n_drugs:>8d} {np.mean(iv):>10.4f} "
              f"{ratio:>8.3f}  [{ci[0]:.3f}, {ci[1]:.3f}]")
        ctrl_rows.append({'label': label, 'n': len(iv), 'n_drugs': n_drugs,
                          'mean': float(np.mean(iv)),
                          'ratio': float(ratio), 'ci_lo': float(ci[0]), 'ci_hi': float(ci[1])})

    # Compare gradients
    s_range = rows[-1]['ratio'] - rows[1]['ratio']  # S_potent - S_weak
    i_range = ctrl_rows[-1]['ratio'] - ctrl_rows[0]['ratio']  # I_potent - I_weak
    print(f"\n  Gradient range: STRUCTURE = {s_range:.3f}  |  INPUT = {i_range:.3f}  "
          f"| S/I range ratio = {s_range / i_range:.1f}× {'← SPECIFIC' if s_range > 3 * i_range else ''}")

    rows_all = {'structure': rows, 'input_control': ctrl_rows}

    with open('gradient_gdsc.json', 'w') as f:
        json.dump(rows_all, f, indent=2)
    return rows


def gradient_yeast(het_matrix_path, het_screens_path, gaf_path, hom_matrix_path):
    """Test C — Yeast: gradient by gene essentiality.
    Essential genes = STRUCTURE genes present in het but absent from hom matrix.
    Uses het collection where essentials are measurable (haploinsufficiency)."""
    print("\n" + "=" * 60)
    print("  GRADIENT C — Yeast (essentiality strata, het collection)")
    print("=" * 60)

    # 1. GO partition
    orf_class = _load_gaf(gaf_path)

    # 2. Load hom matrix index to identify essentials
    #    Essential = STRUCTURE gene present in het but ABSENT from hom
    #    (couldn't survive homozygous deletion → essential)
    print("  Loading hom matrix index (for essentiality)...")
    hom_first_col = pd.read_csv(hom_matrix_path, sep='\t', usecols=[0],
                                low_memory=False)
    hom_genes = set(hom_first_col.iloc[:, 0].values)
    print(f"  Hom matrix: {len(hom_genes)} genes")

    # 3. Load het matrix + screens
    chem_ids = _select_all_chemical_screens(het_screens_path)
    print(f"  Loading het z-score matrix...")
    mat = pd.read_csv(het_matrix_path, sep='\t', index_col=0, low_memory=False)
    chem_cols = [c for c in mat.columns if str(c) in chem_ids]
    print(f"  Het matrix: {mat.shape[0]} genes × {mat.shape[1]} screens, {len(chem_cols)} chemical")

    # 4. Classify structure genes as essential / non-essential
    s_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'STRUCTURE']
    i_orfs = [o for o in mat.index if o in orf_class and orf_class[o] == 'INPUT']

    s_essential = [o for o in s_orfs if o not in hom_genes]
    s_non_essential = [o for o in s_orfs if o in hom_genes]

    print(f"  STRUCTURE genes in het: {len(s_orfs)} total")
    print(f"    Essential (absent from hom): {len(s_essential)}")
    print(f"    Non-essential (in hom):      {len(s_non_essential)}")
    print(f"  INPUT genes in het: {len(i_orfs)}")

    # 5. Compute severity per gene
    i_sev = mat.loc[i_orfs, chem_cols].abs().mean(axis=1).dropna().values
    s_ess_sev = mat.loc[s_essential, chem_cols].abs().mean(axis=1).dropna().values if s_essential else np.array([])
    s_ne_sev = mat.loc[s_non_essential, chem_cols].abs().mean(axis=1).dropna().values

    rows = [{'label': 'INPUT', 'n': len(i_sev), 'mean': float(np.mean(i_sev)),
             'ratio': 1.0, 'ci_lo': 1.0, 'ci_hi': 1.0}]

    print(f"\n  {'Stratum':<20s} {'n_genes':>8s} {'mean|z|':>10s} {'ratio':>8s} {'CI 95%':>18s}")
    print("  " + "-" * 68)
    print(f"  {'INPUT':<20s} {len(i_sev):>8d} {np.mean(i_sev):>10.4f} {'(ref)':>8s}")

    for label, sv in [('S_non_essential', s_ne_sev), ('S_essential', s_ess_sev)]:
        if len(sv) < 5:
            print(f"  {label:<20s} {len(sv):>8d}  [TOO FEW]")
            continue
        ratio = np.mean(sv) / np.mean(i_sev)
        ci = _bootstrap_ratio(sv, i_sev)
        fragile = ' ⚠' if len(sv) < 30 else ''
        print(f"  {label:<20s} {len(sv):>8d} {np.mean(sv):>10.4f} "
              f"{ratio:>8.3f}  [{ci[0]:.3f}, {ci[1]:.3f}]{fragile}")
        rows.append({'label': label, 'n': len(sv), 'mean': float(np.mean(sv)),
                     'ratio': float(ratio), 'ci_lo': float(ci[0]), 'ci_hi': float(ci[1])})

    _gradient_barplot(rows, 'Gradient C — Yeast: ratio by essentiality (het)',
                      'Ratio vs INPUT', 'gradient_yeast.png')

    with open('gradient_yeast.json', 'w') as f:
        json.dump(rows, f, indent=2)
    return rows


def run_gradient(args):
    """Run all available gradient tests."""
    print("\n" + "=" * 60)
    print("  GRADIENT TESTS — Intra-domain severity strata")
    print("=" * 60)

    results = {}

    if args.reef_csv:
        results['reef'] = gradient_reef(args.reef_csv)
    else:
        print("\n  [SKIP] Gradient A (reef): --reef-csv not provided")

    if args.gdsc_csv:
        results['gdsc'] = gradient_gdsc(args.gdsc_csv)
    else:
        print("\n  [SKIP] Gradient B (GDSC): --gdsc-csv not provided")

    if (args.yeast_het_matrix and args.yeast_het_screens
            and args.yeast_gaf and args.yeast_matrix):
        results['yeast'] = gradient_yeast(
            args.yeast_het_matrix, args.yeast_het_screens,
            args.yeast_gaf, args.yeast_matrix)
    else:
        print("\n  [SKIP] Gradient C (yeast): need --yeast-het-matrix, "
              "--yeast-het-screens, --yeast-gaf, --yeast-matrix")

    # Summary
    print("\n" + "=" * 60)
    print("  GRADIENT SUMMARY")
    print("=" * 60)
    for domain, rows in results.items():
        ratios = [r['ratio'] for r in rows if r['label'] != 'INPUT']
        if len(ratios) >= 2:
            monotone = all(ratios[i] <= ratios[i+1] for i in range(len(ratios)-1))
            print(f"  {domain}: ratios = {['%.3f' % r for r in ratios]} — "
                  f"{'monotone ✓' if monotone else 'non-monotone'}")
        elif len(ratios) == 1:
            print(f"  {domain}: single stratum, ratio = {ratios[0]:.3f}")

    return results


# ════════════════════════════════════════════════════════════════
#  MAIN
# ════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description='Preprint figures: meta-analysis + distributions for R-XVII',
        formatter_class=argparse.RawDescriptionHelpFormatter)

    # Actions
    parser.add_argument('--extract', action='store_true', help='Extract raw distributions from data files')
    parser.add_argument('--meta', action='store_true', help='Task 1: forest plot + meta-analysis')
    parser.add_argument('--distrib', action='store_true', help='Task 3: distribution histograms')
    parser.add_argument('--gradient', action='store_true', help='Gradient tests: intra-domain severity strata')
    parser.add_argument('--all', action='store_true', help='Run everything')

    # Data paths
    parser.add_argument('--reef-csv', type=str, help='Path to global_bleaching_environmental.csv')
    parser.add_argument('--gdsc-csv', type=str, help='Path to sanger-dose-response.csv')
    parser.add_argument('--yeast-matrix', type=str, help='Path to yp_matrix_z_haphom_20221025.txt')
    parser.add_argument('--yeast-screens', type=str, help='Path to yp_screens_haphom_20221025.txt')
    parser.add_argument('--yeast-gaf', type=str, help='Path to gene_association.sgd.20251124.gaf')
    parser.add_argument('--yeast-het-matrix', type=str, help='Path to yp_matrix_het_z_20221018.txt')
    parser.add_argument('--yeast-het-screens', type=str, help='Path to yp_screens_het_20221018.txt')
    parser.add_argument('--mdsine2-paper', type=str, help='Path to MDSINE2_Paper/ clone')

    # Output
    parser.add_argument('--data-file', type=str, default=DATA_FILE, help='Path to cached data JSON')

    args = parser.parse_args()

    if args.all:
        args.extract = args.meta = args.distrib = args.gradient = True

    if not (args.extract or args.meta or args.distrib or args.gradient):
        parser.print_help()
        sys.exit(1)

    data = None

    if args.extract:
        data = run_extract(args)
    elif args.meta or args.distrib:
        # Load cached data
        df_path = args.data_file
        if not os.path.exists(df_path):
            print(f"ERROR: {df_path} not found. Run --extract first.")
            sys.exit(1)
        with open(df_path) as f:
            data = json.load(f)
        print(f"Loaded {len(data)} domains from {df_path}")

    if args.meta:
        run_meta(data)

    if args.distrib:
        run_distrib(data)

    if args.gradient:
        run_gradient(args)


if __name__ == '__main__':
    main()