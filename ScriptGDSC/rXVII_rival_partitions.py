#!/usr/bin/env python3
"""
=============================================================================
R-XVII RIVAL PARTITION TEST — GDSC
=============================================================================
Tests whether the ontodynamic structure/input partition is specifically
discriminant, or whether ANY reasonable binary partition of drugs produces
a similar cross-domain convergence.

PARTITIONS TESTED:
  (1) ONTODYNAMIC   — structure (maintenance) vs input (signaling)
                      This is the baseline from v2.
  (2) PPI DEGREE    — hub (target degree >100 in STRING) vs peripheral
                      Rationale: network centrality as alternative organizer
  (3) SELECTIVITY   — selective (≤3 molecular targets) vs promiscuous (>3)
                      Rationale: polypharmacology as alternative explanation
  (4) RANDOM        — 1000 random binary splits of the drug list
                      Control: establishes null distribution of CV

For each partition, we compute:
  - Global ratio (class_A magnitude / class_B magnitude)
  - Per-cancer-type ratio
  - CV of per-cancer-type ratios
  - Cohen's d and p-value

The critical comparison: if ONLY the ontodynamic partition yields low CV
across cancer types, the accommodance objection is weakened.

Usage:
  python3 rXVII_rival_partitions.py [path/to/sanger-dose-response.csv]
=============================================================================
"""

import sys, os, time, warnings, json
from pathlib import Path
import numpy as np
import pandas as pd
from scipy import stats
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

warnings.filterwarnings('ignore')

OUT_DIR = Path('output_rival_partitions')
OUT_DIR.mkdir(exist_ok=True)

N_RANDOM = 1000
MIN_OBS_PER_CANCER = 200  # minimum obs per cancer type to include
MIN_N_PER_ARM = 30        # minimum obs per arm (A or B) within a cancer type

# ============================================================================
# SECTION 1: DRUG → PATHWAY MAPPING (from v2, unchanged)
# ============================================================================

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


# ============================================================================
# SECTION 2: RIVAL PARTITION CLASSIFICATIONS
# ============================================================================
# Each dict maps DRUG_NAME (uppercase) → class label.
# Sources and rationale documented per partition.
# ============================================================================

# --- PARTITION 2: PPI DEGREE ---
# Criterion: approximate degree of PRIMARY target in STRING (>0.7 confidence)
# HUB = target has >100 high-confidence interactions
# PERIPHERAL = target has ≤100 interactions
# Sources: STRING v12 (https://string-db.org), manually curated
#
# Key discordances with ontodynamic partition:
#   - EGFR, PI3K, AKT, MTOR: INPUT in ontodynamic → HUB in PPI
#   - Aurora, PLK, KSP: STRUCTURE in ontodynamic → PERIPHERAL in PPI
#   - BET bromodomains: STRUCTURE in ontodynamic → PERIPHERAL in PPI
#   - CHK1: STRUCTURE in ontodynamic → PERIPHERAL in PPI

PPI_DEGREE = {}

# --- HUB targets (degree > 100) ---
# PARP1 (~200+ interactions: DNA repair complex, chromatin, transcription)
for d in ['OLAPARIB', 'TALAZOPARIB', 'RUCAPARIB', 'NIRAPARIB', 'VELIPARIB']:
    PPI_DEGREE[d] = 'HUB'

# ATM (~250+), ATR (~200+), DNA-PKcs (~200+): DNA damage signaling hubs
for d in ['KU-55933', 'KU-60019', 'AZD6738', 'VE-821', 'VE-822', 'KU-57788', 'NU-7441']:
    PPI_DEGREE[d] = 'HUB'

# DNA-damaging agents: activate TP53/ATM/ATR hubs, DNA is universal target
for d in ['BLEOMYCIN', 'CISPLATIN', 'CARBOPLATIN', 'OXALIPLATIN',
          'CARMUSTINE', 'LOMUSTINE', 'TEMOZOLOMIDE', 'MITOMYCIN-C',
          'DACTINOMYCIN']:
    PPI_DEGREE[d] = 'HUB'

# TOP1 (~150+), TOP2A (~200+): highly connected in chromatin/replication complexes
for d in ['ETOPOSIDE', 'CAMPTOTHECIN', 'SN-38', 'IRINOTECAN', 'TOPOTECAN',
          'DOXORUBICIN', 'EPIRUBICIN', 'MITOXANTRONE']:
    PPI_DEGREE[d] = 'HUB'

# CDK1/2 (~200+), CDK4/6 (~150+): cell cycle hubs
for d in ['PALBOCICLIB', 'RIBOCICLIB', 'ABEMACICLIB', 'RO-3306',
          'DINACICLIB', 'CGP-60474', '681640']:
    PPI_DEGREE[d] = 'HUB'

# TP53 (~500+) via MDM2 inhibition
for d in ['NUTLIN-3A (-)', 'NUTLIN-3A', 'APR-246', 'RG7388', 'IDASANUTLIN']:
    PPI_DEGREE[d] = 'HUB'

# Proteasome (PSMB5 complex ~300+): degrades thousands of substrates
for d in ['BORTEZOMIB', 'CARFILZOMIB', 'MG-132']:
    PPI_DEGREE[d] = 'HUB'

# HSP90 (~400+): chaperone for >200 client proteins
for d in ['17-AAG', 'TANESPIMYCIN', 'AUY922', 'GANETESPIB', 'LUMINESPIB', 'SNX-2112']:
    PPI_DEGREE[d] = 'HUB'

# HDAC1/2/3 (~200+): broadly connected in chromatin/transcription complexes
for d in ['VORINOSTAT', 'BELINOSTAT', 'PANOBINOSTAT', 'ENTINOSTAT',
          'AR-42', 'CAY10603', 'TRICHOSTATIN A']:
    PPI_DEGREE[d] = 'HUB'

# BCL2 (~120), BCL-XL (~100): apoptosis hub
for d in ['NAVITOCLAX', 'ABT-737', 'VENETOCLAX', 'ABT-199']:
    PPI_DEGREE[d] = 'HUB'

# EGFR (~300+): major signaling hub
for d in ['ERLOTINIB', 'GEFITINIB', 'LAPATINIB', 'NERATINIB',
          'AFATINIB', 'OSIMERTINIB', 'AZD3759',
          'AZD8931', 'CANERTINIB', 'SAPITINIB', 'AST-1306', 'CETUXIMAB']:
    PPI_DEGREE[d] = 'HUB'

# AKT1 (~250+), MTOR (~200+), PI3K (~150+)
for d in ['GDC-0941', 'ALPELISIB', 'BUPARLISIB', 'PICTILISIB',
          'IDELALISIB', 'COPANLISIB', 'APITOLISIB', 'AMG-319', 'TASELISIB',
          'NVP-BEZ235', 'DACTOLISIB',
          'AZD8055', 'VISTUSERTIB', 'SAPANISERTIB', 'OSI-027',
          'SIROLIMUS', 'EVEROLIMUS', 'TEMSIROLIMUS', 'RAPAMYCIN',
          'MK-2206', 'AZD5363', 'IPATASERTIB', 'CAPIVASERTIB', 'UPROSERTIB',
          'AT13148', 'AZD6482', 'BX-795']:
    PPI_DEGREE[d] = 'HUB'

# SRC (~200+), ABL1 (~200+): via dasatinib, bosutinib etc
for d in ['DASATINIB', 'BOSUTINIB', 'SARACATINIB', 'PONATINIB']:
    PPI_DEGREE[d] = 'HUB'

# Tubulin alpha/beta (~150+ in complex): structural hub
for d in ['PACLITAXEL', 'DOCETAXEL', 'VINBLASTINE', 'VINCRISTINE',
          'VINORELBINE', 'EPOTHILONE-B']:
    PPI_DEGREE[d] = 'HUB'

# JAK1/2 (~150+): cytokine signaling hub
for d in ['RUXOLITINIB', 'TOFACITINIB']:
    PPI_DEGREE[d] = 'HUB'

# --- PERIPHERAL targets (degree ≤ 100) ---
# CHK1 (~80): checkpoint kinase, moderate connectivity
for d in ['AZD7762', 'CHIR-124', 'MK-8776']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# MIRIN target MRE11 (~80)
PPI_DEGREE['MIRIN'] = 'PERIPHERAL'

# Antimetabolites: TYMS (~50), DHFR (~50), RRM1/2 (~60)
for d in ['GEMCITABINE', 'CYTARABINE', '5-FLUOROURACIL', 'METHOTREXATE',
          'FLUDARABINE', 'CLOFARABINE', 'HYDROXYUREA', 'PEMETREXED', 'CLADRIBINE']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# CDK9 (~80): less connected than CDK1/2
PPI_DEGREE['ALVOCIDIB'] = 'PERIPHERAL'

# NEDD8/NAE (~70)
PPI_DEGREE['PEVONEDISTAT'] = 'PERIPHERAL'

# Aurora A/B (~80): mitotic kinases
for d in ['ALISERTIB', 'ZM-447439', 'BARASERTIB', 'TOZASERTIB']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# PLK1 (~80)
for d in ['BI-2536', 'VOLASERTIB', 'GSK461364']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# KSP/KIF11 (~30), TTK/MPS1 (~40)
for d in ['S-TRITYL-L-CYSTEINE', 'ISPINESIB', 'MPS1-IN-1']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# HDAC6-selective (~60) and specific chromatin modifiers
for d in ['ACY-1215', 'TUBASTATIN A']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# BET bromodomains BRD2/3/4 (~80)
for d in ['JQ1', 'I-BET-762', 'OTX015', 'APABETALONE']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# DOT1L (~40), EZH2 (~60), other methyltransferases
for d in ['EPZ-5676', 'PINOMETOSTAT', 'GSK343', 'EPZ004777', 'EI1',
          'UNC0638', 'CHAETOCIN', 'PFI-3']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# DNMT1/3 (~80)
for d in ['DECITABINE', 'AZACYTIDINE']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# IAP/XIAP (~60), survivin (~50)
for d in ['AZD5582', 'BIRINAPANT', 'EMBELIN', 'LCL-161', 'YM-155', 'OBATOCLAX']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# MEK1/2 (MAP2K1 ~80): moderate connectivity
for d in ['PD-0325901', 'TRAMETINIB', 'SELUMETINIB', 'BINIMETINIB', 'COBIMETINIB',
          'REFAMETINIB', 'CI-1040', 'PIMASERTIB']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# BRAF (~80-100): borderline, classified peripheral
for d in ['PLX-4720', 'DABRAFENIB', 'VEMURAFENIB', 'ENCORAFENIB',
          'AZ-628', 'SB-590885', 'TAK-632']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# ERK1/2 (~100): borderline, classified peripheral
for d in ['SCH772984', 'BVD-523', 'ULIXERTINIB', 'VX-11E']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# Sorafenib is multi-target including BRAF → peripheral for primary target
PPI_DEGREE['SORAFENIB'] = 'PERIPHERAL'

# RTKs with moderate degree
# ALK (~50), MET (~80), FGFR (~80), IGF1R (~80), FLT3 (~60)
for d in ['CRIZOTINIB', 'ALECTINIB', 'CERITINIB', 'NVP-TAE684']:
    PPI_DEGREE[d] = 'PERIPHERAL'  # ALK
for d in ['PHA-665752', 'SAVOLITINIB', 'FORETINIB']:
    PPI_DEGREE[d] = 'PERIPHERAL'  # MET
for d in ['PD-173074', 'AZD4547', 'BGJ398', 'BRIVANIB']:
    PPI_DEGREE[d] = 'PERIPHERAL'  # FGFR
for d in ['BMS-536924', 'BMS-754807', 'LINSITINIB', 'GSK1904529A']:
    PPI_DEGREE[d] = 'PERIPHERAL'  # IGF1R
for d in ['GW 441756', 'LESTAURTINIB', 'MIDOSTAURIN']:
    PPI_DEGREE[d] = 'PERIPHERAL'  # FLT3/NTRK

# Multi-kinase inhibitors — primary targets are moderate degree RTKs
for d in ['SUNITINIB', 'AXITINIB', 'PAZOPANIB', 'LENVATINIB',
          'CABOZANTINIB', 'REGORAFENIB', 'TIVOZANIB',
          'IMATINIB', 'NILOTINIB',
          'AMUVATINIB', 'GNF-2', 'MASITINIB', 'DOVITINIB']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# SB 505124 (TGFBR1 ~80), AVAGACESTAT (gamma-secretase ~60)
for d in ['SB 505124', 'SB-505124', 'AVAGACESTAT']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# ROCK (GSK269962A): ~70
PPI_DEGREE['GSK269962A'] = 'PERIPHERAL'

# Hormone receptors: ER (~150+ but nuclear), AR (~100)
for d in ['TAMOXIFEN', 'FULVESTRANT']:
    PPI_DEGREE[d] = 'HUB'  # ER is a transcriptional hub
for d in ['BICALUTAMIDE']:
    PPI_DEGREE[d] = 'PERIPHERAL'  # AR ~100
for d in ['DEXAMETHASONE']:
    PPI_DEGREE[d] = 'HUB'  # GR → many transcriptional targets
PPI_DEGREE['BEXAROTENE'] = 'PERIPHERAL'  # RXR ~80

# WNT/Hedgehog: TNKS (~50), SMO (~30), GSK3B (~150+)
for d in ['XAV-939', 'IWP-2', 'LGK-974', 'WNTC59']:
    PPI_DEGREE[d] = 'PERIPHERAL'
for d in ['CYCLOPAMINE', 'VISMODEGIB', 'SONIDEGIB']:
    PPI_DEGREE[d] = 'PERIPHERAL'
for d in ['SB-216763', 'CHIR-99021']:
    PPI_DEGREE[d] = 'HUB'  # GSK3B ~150+

# JNK/p38: MAP kinases (~80)
for d in ['DORAMAPIMOD', 'AS601245', '(5Z)-7-OXOZEAENOL', 'JNK INHIBITOR VIII']:
    PPI_DEGREE[d] = 'PERIPHERAL'

# Metabolism: AMPK (~60), IDH (~40), NAMPT (~50)
for d in ['AICAR', 'METFORMIN', 'PHENFORMIN']:
    PPI_DEGREE[d] = 'PERIPHERAL'
for d in ['AGI-5198', 'AGI-6780']:
    PPI_DEGREE[d] = 'PERIPHERAL'
for d in ['APO866', 'APO866, FK866']:
    PPI_DEGREE[d] = 'PERIPHERAL'
for d in ['CAY10566', 'C-75', 'AR-12']:
    PPI_DEGREE[d] = 'PERIPHERAL'
PPI_DEGREE['PF-4708671'] = 'PERIPHERAL'  # S6K1 (~70)

# Immune: CRBN (~50), BTK (~60)
for d in ['LENALIDOMIDE', 'THALIDOMIDE', 'POMALIDOMIDE']:
    PPI_DEGREE[d] = 'PERIPHERAL'
PPI_DEGREE['IBRUTINIB'] = 'PERIPHERAL'
PPI_DEGREE['BMS-345541'] = 'PERIPHERAL'  # IKKβ ~80


# --- PARTITION 3: SELECTIVITY ---
# Criterion: number of distinct molecular targets at clinically relevant concentrations
# SELECTIVE = ≤3 specific protein targets
# PROMISCUOUS = >3 targets, or non-specific mechanism (DNA damage, tubulin, pan-enzyme)
# Sources: ChEMBL, DrugBank, published selectivity profiles (KINOMEscan etc.)
#
# Key discordances with ontodynamic partition:
#   - DNA-damaging agents: STRUCTURE in ontodynamic → PROMISCUOUS in selectivity
#   - PARP inhibitors: STRUCTURE in ontodynamic → SELECTIVE in selectivity
#   - Multi-kinase inhibitors: INPUT in ontodynamic → PROMISCUOUS in selectivity
#   - MEK/BRAF specific: INPUT in ontodynamic → SELECTIVE in selectivity

SELECTIVITY = {}

# --- PROMISCUOUS (>3 targets or non-specific mechanism) ---

# DNA alkylators/crosslinkers: react with DNA non-specifically
for d in ['CISPLATIN', 'CARBOPLATIN', 'OXALIPLATIN',
          'CARMUSTINE', 'LOMUSTINE', 'TEMOZOLOMIDE', 'MITOMYCIN-C',
          'BLEOMYCIN']:
    SELECTIVITY[d] = 'PROMISCUOUS'

# Intercalators and TOP2 poisons: multiple DNA-binding modes
for d in ['DOXORUBICIN', 'DACTINOMYCIN', 'EPIRUBICIN', 'MITOXANTRONE']:
    SELECTIVITY[d] = 'PROMISCUOUS'

# Tubulin binders: bind tubulin but affect many cellular processes
for d in ['PACLITAXEL', 'DOCETAXEL', 'VINBLASTINE', 'VINCRISTINE',
          'VINORELBINE', 'EPOTHILONE-B']:
    SELECTIVITY[d] = 'PROMISCUOUS'

# Proteasome inhibitors: degrade thousands of substrates
for d in ['BORTEZOMIB', 'CARFILZOMIB', 'MG-132']:
    SELECTIVITY[d] = 'PROMISCUOUS'

# HSP90 inhibitors: >200 client proteins
for d in ['17-AAG', 'TANESPIMYCIN', 'AUY922', 'GANETESPIB', 'LUMINESPIB', 'SNX-2112']:
    SELECTIVITY[d] = 'PROMISCUOUS'

# Pan-HDAC inhibitors: hit HDAC1/2/3/6/8/10/11
for d in ['VORINOSTAT', 'BELINOSTAT', 'PANOBINOSTAT', 'TRICHOSTATIN A', 'AR-42']:
    SELECTIVITY[d] = 'PROMISCUOUS'

# Pan-CDK inhibitors: hit multiple CDKs
for d in ['DINACICLIB', 'ALVOCIDIB', 'CGP-60474']:
    SELECTIVITY[d] = 'PROMISCUOUS'

# Multi-kinase inhibitors (>5 kinase targets at relevant concentrations)
for d in ['SORAFENIB', 'SUNITINIB', 'PAZOPANIB', 'LENVATINIB',
          'CABOZANTINIB', 'REGORAFENIB', 'DOVITINIB',
          'DASATINIB', 'PONATINIB', 'BOSUTINIB',
          'MIDOSTAURIN', 'LESTAURTINIB',
          'FORETINIB', 'AMUVATINIB', 'MASITINIB', 'TIVOZANIB']:
    SELECTIVITY[d] = 'PROMISCUOUS'

# Dual PI3K/MTOR inhibitors: hit multiple kinases
for d in ['NVP-BEZ235', 'DACTOLISIB', 'APITOLISIB']:
    SELECTIVITY[d] = 'PROMISCUOUS'

# Multi-target pan-ErbB inhibitors
for d in ['CANERTINIB', 'AZD8931', 'SAPITINIB', 'AST-1306']:
    SELECTIVITY[d] = 'PROMISCUOUS'

# BX-795 (TBK1/PDK1/IKKε/multiple)
PPI_DEGREE.setdefault('BX-795', 'PERIPHERAL')
SELECTIVITY['BX-795'] = 'PROMISCUOUS'

# AT13148 (pan-AGC kinase)
SELECTIVITY['AT13148'] = 'PROMISCUOUS'

# --- SELECTIVE (≤3 specific targets) ---

# PARP1/2-selective
for d in ['OLAPARIB', 'TALAZOPARIB', 'RUCAPARIB', 'NIRAPARIB', 'VELIPARIB']:
    SELECTIVITY[d] = 'SELECTIVE'

# MRE11
SELECTIVITY['MIRIN'] = 'SELECTIVE'

# ATM-specific
for d in ['KU-55933', 'KU-60019']:
    SELECTIVITY[d] = 'SELECTIVE'

# DNA-PKcs-specific
for d in ['KU-57788', 'NU-7441']:
    SELECTIVITY[d] = 'SELECTIVE'

# ATR-specific
for d in ['AZD6738', 'VE-821', 'VE-822']:
    SELECTIVITY[d] = 'SELECTIVE'

# CHK1-selective
for d in ['AZD7762', 'CHIR-124', 'MK-8776']:
    SELECTIVITY[d] = 'SELECTIVE'

# TOP1-selective
for d in ['CAMPTOTHECIN', 'SN-38', 'IRINOTECAN', 'TOPOTECAN']:
    SELECTIVITY[d] = 'SELECTIVE'

# TOP2-selective (etoposide is more specific than doxorubicin)
SELECTIVITY['ETOPOSIDE'] = 'SELECTIVE'

# Antimetabolites: target 1-2 specific enzymes
for d in ['GEMCITABINE', 'CYTARABINE', '5-FLUOROURACIL', 'METHOTREXATE',
          'FLUDARABINE', 'CLOFARABINE', 'HYDROXYUREA', 'PEMETREXED', 'CLADRIBINE']:
    SELECTIVITY[d] = 'SELECTIVE'

# CDK4/6-selective
for d in ['PALBOCICLIB', 'RIBOCICLIB', 'ABEMACICLIB']:
    SELECTIVITY[d] = 'SELECTIVE'

# CDK1-selective
PPI_DEGREE.setdefault('RO-3306', 'HUB')
SELECTIVITY['RO-3306'] = 'SELECTIVE'
SELECTIVITY['681640'] = 'SELECTIVE'

# MDM2-specific
for d in ['NUTLIN-3A (-)', 'NUTLIN-3A', 'RG7388', 'IDASANUTLIN']:
    SELECTIVITY[d] = 'SELECTIVE'

# p53-specific (reactivator)
SELECTIVITY['APR-246'] = 'SELECTIVE'

# NAE-specific
SELECTIVITY['PEVONEDISTAT'] = 'SELECTIVE'

# Aurora A/B selective
for d in ['ALISERTIB', 'ZM-447439', 'BARASERTIB', 'TOZASERTIB']:
    SELECTIVITY[d] = 'SELECTIVE'

# PLK1-selective
for d in ['BI-2536', 'VOLASERTIB', 'GSK461364']:
    SELECTIVITY[d] = 'SELECTIVE'

# KSP-selective, MPS1-selective
for d in ['S-TRITYL-L-CYSTEINE', 'ISPINESIB', 'MPS1-IN-1']:
    SELECTIVITY[d] = 'SELECTIVE'

# BCL2-selective (venetoclax), BCL2/BCL-XL dual (navitoclax)
SELECTIVITY['VENETOCLAX'] = 'SELECTIVE'
SELECTIVITY['ABT-199'] = 'SELECTIVE'
SELECTIVITY['NAVITOCLAX'] = 'SELECTIVE'  # BCL2 + BCL-XL = 2 targets
SELECTIVITY['ABT-737'] = 'SELECTIVE'

# IAP/SMAC mimetics: XIAP + cIAP1/2 = 3 targets
for d in ['AZD5582', 'BIRINAPANT', 'LCL-161']:
    SELECTIVITY[d] = 'SELECTIVE'
SELECTIVITY['EMBELIN'] = 'SELECTIVE'
SELECTIVITY['YM-155'] = 'SELECTIVE'  # survivin
SELECTIVITY['OBATOCLAX'] = 'PROMISCUOUS'  # pan-BCL2 family + other

# HDAC6-selective
for d in ['ACY-1215', 'TUBASTATIN A', 'CAY10603']:
    SELECTIVITY[d] = 'SELECTIVE'

# Class-I HDAC selective
SELECTIVITY['ENTINOSTAT'] = 'SELECTIVE'  # HDAC1/3

# BET bromodomain selective (BRD2/3/4 = 3 targets)
for d in ['JQ1', 'I-BET-762', 'OTX015']:
    SELECTIVITY[d] = 'SELECTIVE'
SELECTIVITY['APABETALONE'] = 'SELECTIVE'  # BRD2/3/4-BD2 selective

# Methyltransferase-specific
for d in ['EPZ-5676', 'PINOMETOSTAT']:
    SELECTIVITY[d] = 'SELECTIVE'  # DOT1L
for d in ['GSK343', 'EI1']:
    SELECTIVITY[d] = 'SELECTIVE'  # EZH2
SELECTIVITY['EPZ004777'] = 'SELECTIVE'  # DOT1L
SELECTIVITY['UNC0638'] = 'SELECTIVE'  # G9a
SELECTIVITY['CHAETOCIN'] = 'PROMISCUOUS'  # non-specific SUV39H1 + thioredoxin
SELECTIVITY['PFI-3'] = 'SELECTIVE'  # SMARCA2/4

# DNMT-selective
for d in ['DECITABINE', 'AZACYTIDINE']:
    SELECTIVITY[d] = 'SELECTIVE'

# MEK1/2-selective (exquisitely selective kinase inhibitors)
for d in ['PD-0325901', 'TRAMETINIB', 'SELUMETINIB', 'BINIMETINIB', 'COBIMETINIB',
          'REFAMETINIB', 'CI-1040', 'PIMASERTIB']:
    SELECTIVITY[d] = 'SELECTIVE'

# BRAF-selective (V600E-specific)
for d in ['PLX-4720', 'DABRAFENIB', 'VEMURAFENIB', 'ENCORAFENIB']:
    SELECTIVITY[d] = 'SELECTIVE'
# AZ-628, SB-590885: less selective BRAF
for d in ['AZ-628', 'SB-590885']:
    SELECTIVITY[d] = 'SELECTIVE'
SELECTIVITY['TAK-632'] = 'SELECTIVE'  # pan-RAF but still RAF-specific

# ERK1/2-selective
for d in ['SCH772984', 'BVD-523', 'ULIXERTINIB', 'VX-11E']:
    SELECTIVITY[d] = 'SELECTIVE'

# PI3K-selective (isoform-specific or pan-PI3K)
for d in ['GDC-0941', 'ALPELISIB', 'BUPARLISIB', 'PICTILISIB',
          'IDELALISIB', 'COPANLISIB', 'AMG-319', 'TASELISIB', 'AZD6482']:
    SELECTIVITY[d] = 'SELECTIVE'

# MTOR-selective (mTORC1/2)
for d in ['AZD8055', 'VISTUSERTIB', 'SAPANISERTIB', 'OSI-027']:
    SELECTIVITY[d] = 'SELECTIVE'

# Rapalogs: MTOR (via FKBP12, very specific)
for d in ['SIROLIMUS', 'EVEROLIMUS', 'TEMSIROLIMUS', 'RAPAMYCIN']:
    SELECTIVITY[d] = 'SELECTIVE'

# AKT-selective
for d in ['MK-2206', 'AZD5363', 'IPATASERTIB', 'CAPIVASERTIB', 'UPROSERTIB']:
    SELECTIVITY[d] = 'SELECTIVE'

# EGFR-selective
for d in ['ERLOTINIB', 'GEFITINIB', 'OSIMERTINIB', 'AZD3759', 'CETUXIMAB']:
    SELECTIVITY[d] = 'SELECTIVE'

# EGFR/HER2 dual (2 targets)
for d in ['LAPATINIB', 'NERATINIB', 'AFATINIB']:
    SELECTIVITY[d] = 'SELECTIVE'

# ALK-selective (ALK +/- a few)
for d in ['ALECTINIB', 'CERITINIB']:
    SELECTIVITY[d] = 'SELECTIVE'
# Crizotinib: ALK + MET + ROS1 = 3 targets → selective
SELECTIVITY['CRIZOTINIB'] = 'SELECTIVE'
SELECTIVITY['NVP-TAE684'] = 'SELECTIVE'  # ALK-specific

# MET-selective
for d in ['PHA-665752', 'SAVOLITINIB']:
    SELECTIVITY[d] = 'SELECTIVE'

# FGFR-selective (3-4 FGFR isoforms)
for d in ['PD-173074', 'AZD4547', 'BGJ398']:
    SELECTIVITY[d] = 'SELECTIVE'
SELECTIVITY['BRIVANIB'] = 'PROMISCUOUS'  # VEGFR + FGFR

# IGF1R-selective
for d in ['BMS-536924', 'BMS-754807', 'LINSITINIB', 'GSK1904529A']:
    SELECTIVITY[d] = 'SELECTIVE'

# ABL-selective
for d in ['IMATINIB', 'NILOTINIB']:
    SELECTIVITY[d] = 'SELECTIVE'
# GNF-2: allosteric ABL-specific
SELECTIVITY['GNF-2'] = 'SELECTIVE'

# VEGFR-selective
SELECTIVITY['AXITINIB'] = 'SELECTIVE'  # very VEGFR-specific

# KIT-selective
# (no pure KIT inhibitors in the list)

# p38/JNK
SELECTIVITY['DORAMAPIMOD'] = 'SELECTIVE'  # p38α-specific
SELECTIVITY['AS601245'] = 'SELECTIVE'  # JNK-specific
SELECTIVITY['(5Z)-7-OXOZEAENOL'] = 'SELECTIVE'  # TAK1
SELECTIVITY['JNK INHIBITOR VIII'] = 'SELECTIVE'

# WNT/Hedgehog specific
for d in ['XAV-939', 'IWP-2', 'LGK-974', 'WNTC59']:
    SELECTIVITY[d] = 'SELECTIVE'
for d in ['CYCLOPAMINE', 'VISMODEGIB', 'SONIDEGIB']:
    SELECTIVITY[d] = 'SELECTIVE'
for d in ['SB-216763', 'CHIR-99021']:
    SELECTIVITY[d] = 'SELECTIVE'  # GSK3β-specific

# TGFβR (SB 505124)
for d in ['SB 505124', 'SB-505124']:
    SELECTIVITY[d] = 'SELECTIVE'
SELECTIVITY['AVAGACESTAT'] = 'SELECTIVE'  # gamma-secretase

# ROCK
SELECTIVITY['GSK269962A'] = 'SELECTIVE'

# GW 441756: NTRK-selective
SELECTIVITY['GW 441756'] = 'SELECTIVE'

# Hormone receptors: very specific
for d in ['TAMOXIFEN', 'BICALUTAMIDE', 'FULVESTRANT', 'DEXAMETHASONE', 'BEXAROTENE']:
    SELECTIVITY[d] = 'SELECTIVE'

# Metabolism: mostly target-specific
for d in ['AICAR', 'METFORMIN', 'PHENFORMIN']:
    SELECTIVITY[d] = 'SELECTIVE'  # AMPK
for d in ['AGI-5198', 'AGI-6780']:
    SELECTIVITY[d] = 'SELECTIVE'  # IDH1/2
for d in ['APO866', 'APO866, FK866']:
    SELECTIVITY[d] = 'SELECTIVE'  # NAMPT
SELECTIVITY['CAY10566'] = 'SELECTIVE'  # SCD1
SELECTIVITY['C-75'] = 'SELECTIVE'  # FASN
SELECTIVITY['AR-12'] = 'PROMISCUOUS'  # PDK1 + multiple
SELECTIVITY['PF-4708671'] = 'SELECTIVE'  # S6K1

# Immune
for d in ['LENALIDOMIDE', 'THALIDOMIDE', 'POMALIDOMIDE']:
    SELECTIVITY[d] = 'SELECTIVE'  # CRBN → specific neosubstrates
SELECTIVITY['RUXOLITINIB'] = 'SELECTIVE'  # JAK1/2
SELECTIVITY['TOFACITINIB'] = 'SELECTIVE'  # JAK1/3
SELECTIVITY['IBRUTINIB'] = 'SELECTIVE'
SELECTIVITY['SARACATINIB'] = 'SELECTIVE'  # SRC-selective  # BTK (+ some off-targets, borderline)
SELECTIVITY['BMS-345541'] = 'SELECTIVE'  # IKKβ


# ============================================================================
# SECTION 3: STATISTICAL ENGINE
# ============================================================================

def compute_ratio(vals_a, vals_b):
    """
    Compute magnitude ratio. For AUC, magnitude = 1 - AUC.
    Returns ratio (class with higher magnitude / class with lower magnitude)
    and direction indicator.
    """
    a = vals_a[np.isfinite(vals_a)]
    b = vals_b[np.isfinite(vals_b)]
    if len(a) < MIN_N_PER_ARM or len(b) < MIN_N_PER_ARM:
        return None

    mag_a = 1.0 - np.mean(a)
    mag_b = 1.0 - np.mean(b)

    if mag_a < 0.001 and mag_b < 0.001:
        return None

    # Always compute as (higher magnitude / lower magnitude)
    if mag_a >= mag_b:
        ratio = mag_a / mag_b if mag_b > 0.001 else float('inf')
        direction = 'A>B'
    else:
        ratio = mag_b / mag_a if mag_a > 0.001 else float('inf')
        direction = 'B>A'

    # Mann-Whitney
    U, p = stats.mannwhitneyu(a, b, alternative='two-sided')

    # Cohen's d (A - B, signed)
    n1, n2 = len(a), len(b)
    ps = np.sqrt(((n1 - 1) * np.var(a, ddof=1) + (n2 - 1) * np.var(b, ddof=1)) / (n1 + n2 - 2))
    d = (np.mean(a) - np.mean(b)) / ps if ps > 0 else 0

    return {
        'n_a': n1, 'n_b': n2,
        'mean_a': float(np.mean(a)), 'mean_b': float(np.mean(b)),
        'mag_a': float(mag_a), 'mag_b': float(mag_b),
        'ratio': float(ratio), 'direction': direction,
        'd': float(d), 'abs_d': float(abs(d)),
        'p_MW': float(p),
    }


def compute_cross_cancer_cv(dfc, auc_col, class_col, cancer_col, label=''):
    """
    For a given binary classification (class_col with values in two categories),
    compute the magnitude ratio per cancer type and return the CV.
    """
    classes = sorted(dfc[class_col].dropna().unique())
    if len(classes) != 2:
        return None

    cls_a, cls_b = classes[0], classes[1]
    ratios = []
    per_cancer = []

    for ct, grp in dfc.groupby(cancer_col):
        if len(grp) < MIN_OBS_PER_CANCER:
            continue
        va = grp.loc[grp[class_col] == cls_a, auc_col].values
        vb = grp.loc[grp[class_col] == cls_b, auc_col].values
        r = compute_ratio(va, vb)
        if r and np.isfinite(r['ratio']) and r['ratio'] < 100:
            ratios.append(r['ratio'])
            per_cancer.append({
                'cancer_type': str(ct),
                'ratio': r['ratio'],
                'direction': r['direction'],
                'abs_d': r['abs_d'],
                'p_MW': r['p_MW'],
                'n_a': r['n_a'], 'n_b': r['n_b'],
            })

    if len(ratios) < 3:
        return None

    arr = np.array(ratios)
    return {
        'label': label,
        'classes': f'{cls_a} vs {cls_b}',
        'n_cancer_types': len(ratios),
        'ratios': ratios,
        'mean_ratio': float(np.mean(arr)),
        'median_ratio': float(np.median(arr)),
        'std_ratio': float(np.std(arr, ddof=1)),
        'cv_ratio': float(np.std(arr, ddof=1) / np.mean(arr) * 100) if np.mean(arr) > 0 else float('inf'),
        'min_ratio': float(np.min(arr)),
        'max_ratio': float(np.max(arr)),
        'per_cancer': per_cancer,
    }


# ============================================================================
# SECTION 4: MAIN
# ============================================================================

def main():
    t0 = time.time()

    print("=" * 75)
    print("  R-XVII RIVAL PARTITION TEST — GDSC")
    print("  Test de spécificité: la partition ontodynamique est-elle uniquement")
    print("  discriminante, ou n'importe quel critère converge aussi bien?")
    print("=" * 75)

    # --- Load ---
    fname = sys.argv[1] if len(sys.argv) > 1 else 'sanger-dose-response.csv'
    if not os.path.exists(fname):
        print(f"\nERREUR: {fname} introuvable.")
        print(f"Usage: python3 rXVII_rival_partitions.py [chemin/sanger-dose-response.csv]")
        sys.exit(1)

    df = pd.read_csv(fname)
    auc_col = 'AUC_PUBLISHED' if 'AUC_PUBLISHED' in df.columns else 'AUC'

    print(f"\n  {len(df):,} observations, {df['COSMIC_ID'].nunique()} lignées, "
          f"{df['DRUG_NAME'].nunique()} drogues")

    # Detect cancer type column (optional — fallback to drug bootstrap if absent)
    cancer_col = None
    for c in ['TCGA_DESC', 'CANCER_TYPE', 'TISSUE']:
        if c in df.columns and df[c].notna().sum() > 0:
            cancer_col = c
            break

    # Also try loading external annotation file
    if not cancer_col:
        import glob
        ann_candidates = ['cell_line_annotations.csv', 'Model.csv',
                          'GDSC_cell_lines.csv', 'TableS1E.csv']
        # Also pick up model_list_YYYYMMDD.csv from Cell Model Passports
        ann_candidates.extend(sorted(glob.glob('model_list*.csv')))
        for ann_file in ann_candidates:
            if not os.path.exists(ann_file):
                continue
            try:
                ann = pd.read_csv(ann_file)
                # Strip whitespace from column names (cancerrxgene.org adds spaces)
                ann.columns = [c.strip() for c in ann.columns]
                # Look for COSMIC_ID + tissue/cancer type columns
                id_col = None
                for c in ['COSMIC_ID', 'COSMIC ID', 'cosmic_id', 'model_id',
                          'COSMICID', 'Sample id']:
                    if c in ann.columns:
                        id_col = c
                        break
                tissue_col = None
                for c in ['TCGA Classfication', 'TCGA Classification',  # cancerrxgene typo
                          'TCGA_DESC', 'TCGA type', 'tcga_label',
                          'cancer_type', 'CANCER_TYPE', 'cancer_type_detail',
                          'TISSUE_FACTOR', 'TISSUE', 'Tissue', 'tissue',
                          'tissue_descriptor', 'GDSC.description_1',
                          'Tissue sub-type']:
                    if c in ann.columns:
                        tissue_col = c
                        break
                if id_col and tissue_col:
                    # Ensure COSMIC ID is integer for join
                    ann[id_col] = pd.to_numeric(ann[id_col], errors='coerce')
                    ann_dedup = ann.drop_duplicates(subset=[id_col])
                    mapping = ann_dedup.set_index(id_col)[tissue_col].to_dict()
                    df['TISSUE_ANN'] = df['COSMIC_ID'].map(mapping)
                    n_mapped = df['TISSUE_ANN'].notna().sum()
                    if n_mapped > len(df) * 0.3:
                        cancer_col = 'TISSUE_ANN'
                        n_types = df['TISSUE_ANN'].nunique()
                        print(f"  Annotations chargées: {ann_file}")
                        print(f"    Colonne utilisée: {tissue_col}")
                        print(f"    {n_mapped:,} / {len(df):,} observations mappées")
                        print(f"    {n_types} types de cancer")
                    else:
                        print(f"  ⚠ {ann_file} trouvé mais mapping faible "
                              f"({n_mapped:,}/{len(df):,})")
                        print(f"    Colonnes: {list(ann.columns)}")
                    break
            except Exception as e:
                print(f"  ⚠ Erreur lecture {ann_file}: {e}")
                continue

    if cancer_col:
        print(f"  Cancer types: {cancer_col} ({df[cancer_col].nunique()} types)")
    else:
        print(f"  ⚠ Pas de colonne type de cancer trouvée.")
        print(f"    Colonnes disponibles: {list(df.columns)}")
        print(f"    → Fallback: bootstrap par drogue (CV sur rééchantillonnage)")
        print(f"    → Pour le test complet par cancer type, fournir un fichier")
        print(f"       cell_line_annotations.csv avec colonnes COSMIC_ID + TCGA_DESC")
        print(f"       (téléchargeable: cancerrxgene.org → Cell Lines Details)")

    # --- Map drugs ---
    df['PATHWAY'] = df['DRUG_NAME'].apply(map_drug)
    df['DRUG_UPPER'] = df['DRUG_NAME'].apply(
        lambda x: str(x).strip().upper() if pd.notna(x) else None)

    # ================================================================
    # APPLY PARTITIONS
    # ================================================================

    # (1) ONTODYNAMIC: pathway → STRUCTURE / INPUT
    def onto_class(pw):
        if pw in STRUCTURE_PATHWAYS: return 'STRUCTURE'
        if pw in INPUT_PATHWAYS: return 'INPUT'
        return None
    df['ONTO'] = df['PATHWAY'].apply(onto_class)

    # (2) PPI DEGREE: drug → HUB / PERIPHERAL
    df['PPI'] = df['DRUG_UPPER'].map(PPI_DEGREE)

    # (3) SELECTIVITY: drug → SELECTIVE / PROMISCUOUS
    df['SEL'] = df['DRUG_UPPER'].map(SELECTIVITY)

    # --- Coverage report ---
    print(f"\n{'=' * 75}")
    print(f"  COUVERTURE DES PARTITIONS")
    print(f"{'=' * 75}")
    for col, name in [('ONTO', 'Ontodynamique'), ('PPI', 'Degré PPI'), ('SEL', 'Sélectivité')]:
        n_mapped = df[col].notna().sum()
        classes = df[col].value_counts()
        print(f"\n  {name} ({col}):")
        print(f"    Couverture: {n_mapped:,} / {len(df):,} ({100*n_mapped/len(df):.1f}%)")
        for cls, cnt in classes.items():
            print(f"    {cls}: {cnt:,}")

    # --- Discordance analysis ---
    print(f"\n{'=' * 75}")
    print(f"  DISCORDANCE ENTRE PARTITIONS")
    print(f"  (crucial: si les partitions sont trop corrélées, le test est faible)")
    print(f"{'=' * 75}")

    for p1, p2, n1, n2 in [('ONTO', 'PPI', 'Ontodynamique', 'PPI'),
                             ('ONTO', 'SEL', 'Ontodynamique', 'Sélectivité'),
                             ('PPI', 'SEL', 'PPI', 'Sélectivité')]:
        both = df.dropna(subset=[p1, p2])
        if len(both) == 0:
            continue
        ct = pd.crosstab(both[p1], both[p2])
        print(f"\n  {n1} × {n2}:")
        print(f"    {ct.to_string().replace(chr(10), chr(10) + '    ')}")
        # Agreement rate
        # Map each partition to binary 0/1 for correlation
        vals1 = both[p1].map({v: i for i, v in enumerate(sorted(both[p1].unique()))})
        vals2 = both[p2].map({v: i for i, v in enumerate(sorted(both[p2].unique()))})
        if vals1.std() > 0 and vals2.std() > 0:
            corr = vals1.corr(vals2)
            print(f"    Corrélation (Pearson on binary): {corr:.3f}")

    # ================================================================
    # GLOBAL RESULTS
    # ================================================================
    print(f"\n{'=' * 75}")
    print(f"  RÉSULTATS GLOBAUX (tous types de cancer)")
    print(f"{'=' * 75}")

    global_results = {}
    for col, name, cls_a, cls_b in [
        ('ONTO', 'Ontodynamique', 'STRUCTURE', 'INPUT'),
        ('PPI', 'Degré PPI', 'HUB', 'PERIPHERAL'),
        ('SEL', 'Sélectivité', 'PROMISCUOUS', 'SELECTIVE'),
    ]:
        sub = df.dropna(subset=[col])
        va = sub.loc[sub[col] == cls_a, auc_col].values
        vb = sub.loc[sub[col] == cls_b, auc_col].values
        r = compute_ratio(va, vb)
        if r:
            global_results[col] = r
            print(f"\n  {name}:")
            print(f"    {cls_a} (n={r['n_a']:,}): AUC={r['mean_a']:.4f}, mag={r['mag_a']:.4f}")
            print(f"    {cls_b} (n={r['n_b']:,}): AUC={r['mean_b']:.4f}, mag={r['mag_b']:.4f}")
            print(f"    Ratio = {r['ratio']:.3f}× ({r['direction']})")
            print(f"    |d| = {r['abs_d']:.4f}, p(MW) = {r['p_MW']:.2e}")

    # ================================================================
    # CONTROLLED TESTS: does structure/input survive within strata?
    # ================================================================
    # The critical question: if selectivity explains the asymmetry,
    # then structure/input should show NO effect within SELECTIVE drugs.
    # If it does, selectivity alone can't explain it.
    # ================================================================
    print(f"\n{'=' * 75}")
    print(f"  TESTS CONTRÔLÉS: structure/input DANS chaque strate rivale")
    print(f"  (si l'effet survit au contrôle, la rivale ne l'explique pas)")
    print(f"{'=' * 75}")

    controlled_results = {}

    # For each rival partition, test structure/input WITHIN each stratum
    for rival_col, rival_name, strata in [
        ('SEL', 'Sélectivité', ['SELECTIVE', 'PROMISCUOUS']),
        ('PPI', 'Degré PPI', ['HUB', 'PERIPHERAL']),
    ]:
        print(f"\n  ── Structure/Input contrôlé par {rival_name} ──")
        controlled_results[rival_col] = {}

        for stratum in strata:
            # Subset: observations that are BOTH classified by ONTO and in this stratum
            mask = df['ONTO'].notna() & (df[rival_col] == stratum)
            sub = df[mask]

            n_struct = (sub['ONTO'] == 'STRUCTURE').sum()
            n_input = (sub['ONTO'] == 'INPUT').sum()

            if n_struct < 30 or n_input < 30:
                print(f"\n    {stratum}: n trop faible (S={n_struct}, I={n_input})")
                continue

            va = sub.loc[sub['ONTO'] == 'STRUCTURE', auc_col].values
            vb = sub.loc[sub['ONTO'] == 'INPUT', auc_col].values
            r = compute_ratio(va, vb)

            if r:
                controlled_results[rival_col][stratum] = r
                eff = "négligeable" if r['abs_d'] < 0.2 else (
                    "faible" if r['abs_d'] < 0.5 else (
                        "moyen" if r['abs_d'] < 0.8 else "FORT"))
                print(f"\n    {stratum} seulement:")
                print(f"      STRUCTURE (n={r['n_a']:,}): AUC={r['mean_a']:.4f}")
                print(f"      INPUT     (n={r['n_b']:,}): AUC={r['mean_b']:.4f}")
                print(f"      Ratio S/I = {r['ratio']:.3f}×")
                print(f"      |d| = {r['abs_d']:.4f} ({eff}), p = {r['p_MW']:.2e}")

                # Per cancer type within stratum (if cancer_col available)
                if cancer_col:
                    ratios_ct = []
                    for ct, grp in sub.groupby(cancer_col):
                        if len(grp) < 100:
                            continue
                        va_ct = grp.loc[grp['ONTO'] == 'STRUCTURE', auc_col].values
                        vb_ct = grp.loc[grp['ONTO'] == 'INPUT', auc_col].values
                        r_ct = compute_ratio(va_ct, vb_ct)
                        if r_ct and np.isfinite(r_ct['ratio']) and r_ct['ratio'] < 100:
                            ratios_ct.append(r_ct['ratio'])

                    if len(ratios_ct) >= 3:
                        arr = np.array(ratios_ct)
                        cv = float(np.std(arr, ddof=1) / np.mean(arr) * 100)
                        controlled_results[rival_col][stratum + '_cv'] = cv
                        controlled_results[rival_col][stratum + '_ratios'] = ratios_ct
                        controlled_results[rival_col][stratum + '_n_ct'] = len(ratios_ct)
                        print(f"      CV par cancer type: {cv:.1f}% "
                              f"(sur {len(ratios_ct)} types)")
                        print(f"      Ratio range: [{np.min(arr):.3f}, {np.max(arr):.3f}]")

    # Also test: selectivity WITHIN structure and within input
    print(f"\n  ── Sélectivité contrôlée par Ontodynamique ──")
    for onto_stratum in ['STRUCTURE', 'INPUT']:
        mask = (df['ONTO'] == onto_stratum) & df['SEL'].notna()
        sub = df[mask]
        n_prom = (sub['SEL'] == 'PROMISCUOUS').sum()
        n_sel = (sub['SEL'] == 'SELECTIVE').sum()

        if n_prom < 30 or n_sel < 30:
            print(f"\n    {onto_stratum}: n trop faible (P={n_prom}, S={n_sel})")
            continue

        va = sub.loc[sub['SEL'] == 'PROMISCUOUS', auc_col].values
        vb = sub.loc[sub['SEL'] == 'SELECTIVE', auc_col].values
        r = compute_ratio(va, vb)
        if r:
            eff = "négligeable" if r['abs_d'] < 0.2 else (
                "faible" if r['abs_d'] < 0.5 else (
                    "moyen" if r['abs_d'] < 0.8 else "FORT"))
            print(f"\n    Au sein des drogues {onto_stratum}:")
            print(f"      PROMISCUOUS (n={r['n_a']:,}): AUC={r['mean_a']:.4f}")
            print(f"      SELECTIVE   (n={r['n_b']:,}): AUC={r['mean_b']:.4f}")
            print(f"      Ratio P/S = {r['ratio']:.3f}×")
            print(f"      |d| = {r['abs_d']:.4f} ({eff}), p = {r['p_MW']:.2e}")

    # Summary table for controlled tests
    print(f"\n  ── RÉSUMÉ DES TESTS CONTRÔLÉS ──")
    print(f"  {'Test':<45s} {'Ratio':>7s} {'|d|':>6s} {'CV%':>6s}")
    print(f"  {'─' * 45} {'─' * 7} {'─' * 6} {'─' * 6}")

    # Uncontrolled baseline
    if 'ONTO' in global_results:
        gr = global_results['ONTO']
        onto_cv = cv_results.get('ONTO', {}).get('cv_ratio', None) if 'cv_results' in dir() else None
        # We'll fill in CV after the cv_results section; print placeholder
        print(f"  {'S/I global (pas de contrôle)':<45s} {gr['ratio']:>7.3f} {gr['abs_d']:>6.4f}   {'—':>4s}")

    for rival_col, rival_name in [('SEL', 'Sélectivité'), ('PPI', 'Degré PPI')]:
        if rival_col not in controlled_results:
            continue
        cr = controlled_results[rival_col]
        for stratum in cr:
            if stratum.endswith('_cv') or stratum.endswith('_ratios') or stratum.endswith('_n_ct'):
                continue
            r = cr[stratum]
            cv_key = stratum + '_cv'
            cv_str = f"{cr[cv_key]:.1f}" if cv_key in cr else "—"
            label = f"S/I dans {rival_name}={stratum}"
            print(f"  {label:<45s} {r['ratio']:>7.3f} {r['abs_d']:>6.4f} {cv_str:>6s}")

    # ================================================================
    # CROSS-DOMAIN CV (the critical test)
    # ================================================================
    # Two modes:
    #   A) If cancer_col available: CV of ratio across cancer types (ideal)
    #   B) If not: drug-level bootstrap CV (fallback, still valid)
    # ================================================================

    cv_results = {}

    if cancer_col:
        print(f"\n{'=' * 75}")
        print(f"  TEST CRITIQUE (mode A): CV du ratio par type de cancer")
        print(f"  (cible: CV ontodynamique < CV rivaux)")
        print(f"{'=' * 75}")

        for col, name in [('ONTO', 'Ontodynamique'), ('PPI', 'Degré PPI'), ('SEL', 'Sélectivité')]:
            sub = df.dropna(subset=[col])
            r = compute_cross_cancer_cv(sub, auc_col, col, cancer_col, name)
            if r:
                cv_results[col] = r
                print(f"\n  {name}:")
                print(f"    N types cancer: {r['n_cancer_types']}")
                print(f"    Ratio moyen:    {r['mean_ratio']:.3f}×")
                print(f"    Ratio médian:   {r['median_ratio']:.3f}×")
                print(f"    Écart-type:     {r['std_ratio']:.3f}")
                print(f"    ★ CV = {r['cv_ratio']:.1f}%")
                print(f"    Range: [{r['min_ratio']:.3f}, {r['max_ratio']:.3f}]")

                print(f"    {'Cancer type':<22s} {'Ratio':>7s} {'|d|':>6s} {'p':>10s} {'nA':>5s} {'nB':>5s}")
                for pc in sorted(r['per_cancer'], key=lambda x: x['ratio']):
                    print(f"    {pc['cancer_type']:<22s} {pc['ratio']:>7.3f} "
                          f"{pc['abs_d']:>6.3f} {pc['p_MW']:>10.2e} "
                          f"{pc['n_a']:>5d} {pc['n_b']:>5d}")

    # ================================================================
    # DRUG-LEVEL BOOTSTRAP CV (works with or without cancer types)
    # This tests: is the ratio stable when we resample which drugs
    # are included? A robust partition should give stable ratios.
    # ================================================================
    N_BOOT = 1000
    print(f"\n{'=' * 75}")
    print(f"  TEST CRITIQUE (mode B): CV par bootstrap de drogues ({N_BOOT} itérations)")
    print(f"  Rééchantillonnage des drogues avec remplacement dans chaque classe")
    print(f"{'=' * 75}")

    boot_cv_results = {}
    rng_boot = np.random.RandomState(42)

    for col, name, cls_a, cls_b in [
        ('ONTO', 'Ontodynamique', 'STRUCTURE', 'INPUT'),
        ('PPI', 'Degré PPI', 'HUB', 'PERIPHERAL'),
        ('SEL', 'Sélectivité', 'PROMISCUOUS', 'SELECTIVE'),
    ]:
        sub = df.dropna(subset=[col])
        # Get drug-level means
        drug_means = sub.groupby(['DRUG_UPPER', col])[auc_col].mean().reset_index()
        drugs_a = drug_means.loc[drug_means[col] == cls_a, 'DRUG_UPPER'].unique()
        drugs_b = drug_means.loc[drug_means[col] == cls_b, 'DRUG_UPPER'].unique()

        if len(drugs_a) < 5 or len(drugs_b) < 5:
            print(f"\n  {name}: pas assez de drogues ({len(drugs_a)} / {len(drugs_b)})")
            continue

        boot_ratios = []
        for _ in range(N_BOOT):
            # Resample drugs with replacement within each class
            sampled_a = rng_boot.choice(drugs_a, len(drugs_a), replace=True)
            sampled_b = rng_boot.choice(drugs_b, len(drugs_b), replace=True)

            # Get observations for sampled drugs
            vals_a = sub.loc[sub['DRUG_UPPER'].isin(sampled_a) & (sub[col] == cls_a), auc_col].values
            vals_b = sub.loc[sub['DRUG_UPPER'].isin(sampled_b) & (sub[col] == cls_b), auc_col].values

            mag_a = 1.0 - np.mean(vals_a)
            mag_b = 1.0 - np.mean(vals_b)

            if mag_a > 0.001 and mag_b > 0.001:
                ratio = max(mag_a, mag_b) / min(mag_a, mag_b)
                if np.isfinite(ratio) and ratio < 100:
                    boot_ratios.append(ratio)

        if len(boot_ratios) > 100:
            arr = np.array(boot_ratios)
            cv = float(np.std(arr, ddof=1) / np.mean(arr) * 100)
            boot_cv_results[col] = {
                'label': name,
                'n_drugs_a': len(drugs_a),
                'n_drugs_b': len(drugs_b),
                'mean_ratio': float(np.mean(arr)),
                'median_ratio': float(np.median(arr)),
                'std_ratio': float(np.std(arr, ddof=1)),
                'cv_ratio': cv,
                'ci_95': [float(np.percentile(arr, 2.5)), float(np.percentile(arr, 97.5))],
                'boot_ratios': arr,
            }
            print(f"\n  {name}:")
            print(f"    Drogues: {cls_a}={len(drugs_a)}, {cls_b}={len(drugs_b)}")
            print(f"    Ratio moyen bootstrap: {np.mean(arr):.3f}×")
            print(f"    Ratio médian bootstrap: {np.median(arr):.3f}×")
            print(f"    IC 95%: [{np.percentile(arr, 2.5):.3f}, {np.percentile(arr, 97.5):.3f}]")
            print(f"    ★ CV bootstrap = {cv:.1f}%")

    # ================================================================
    # RANDOM PARTITION CONTROL
    # ================================================================
    print(f"\n{'=' * 75}")
    print(f"  CONTRÔLE: {N_RANDOM} partitions aléatoires")
    print(f"{'=' * 75}")

    mapped_drugs = df.dropna(subset=['PATHWAY'])['DRUG_UPPER'].unique()
    rng = np.random.RandomState(42)

    # Pre-compute drug-level mean AUC for speed
    df_mapped = df[df['DRUG_UPPER'].isin(set(mapped_drugs))].copy()
    drug_mean_auc = df_mapped.groupby('DRUG_UPPER')[auc_col].mean()
    drug_obs_count = df_mapped.groupby('DRUG_UPPER')[auc_col].count()

    # For cancer-type CV, pre-compute per drug×cancer AUC
    if cancer_col:
        drug_cancer_auc = df_mapped.groupby(['DRUG_UPPER', cancer_col])[auc_col].agg(['mean', 'count']).reset_index()

    random_cvs = []
    random_boot_cvs = []
    random_global_ratios = []

    N_BOOT_RAND = 200  # bootstrap iterations per random partition

    for i in range(N_RANDOM):
        perm = rng.permutation(len(mapped_drugs))
        half = len(perm) // 2
        class_a_drugs = set(mapped_drugs[perm[:half]])
        class_b_drugs = set(mapped_drugs[perm[half:]])

        # Global ratio using pre-computed drug means (weighted by obs count)
        drugs_a_mask = drug_mean_auc.index.isin(class_a_drugs)
        drugs_b_mask = drug_mean_auc.index.isin(class_b_drugs)

        if drugs_a_mask.sum() < 2 or drugs_b_mask.sum() < 2:
            continue

        # Weighted mean across drugs (weight = n observations)
        wa = drug_obs_count[drugs_a_mask]
        wb = drug_obs_count[drugs_b_mask]
        mean_a = np.average(drug_mean_auc[drugs_a_mask], weights=wa)
        mean_b = np.average(drug_mean_auc[drugs_b_mask], weights=wb)
        mag_a = 1.0 - mean_a
        mag_b = 1.0 - mean_b

        if mag_a > 0.001 and mag_b > 0.001:
            ratio = max(mag_a, mag_b) / min(mag_a, mag_b)
            if np.isfinite(ratio) and ratio < 100:
                random_global_ratios.append(ratio)

        # Drug-level bootstrap CV (fast: operates on drug_mean_auc vectors)
        drugs_a_means = drug_mean_auc[drugs_a_mask].values
        drugs_b_means = drug_mean_auc[drugs_b_mask].values
        na, nb = len(drugs_a_means), len(drugs_b_means)

        if na >= 5 and nb >= 5:
            boot_r = []
            for _ in range(N_BOOT_RAND):
                sa = drugs_a_means[rng.randint(0, na, na)]
                sb = drugs_b_means[rng.randint(0, nb, nb)]
                ma = 1.0 - np.mean(sa)
                mb = 1.0 - np.mean(sb)
                if ma > 0.001 and mb > 0.001:
                    r_b = max(ma, mb) / min(ma, mb)
                    if np.isfinite(r_b) and r_b < 100:
                        boot_r.append(r_b)
            if len(boot_r) > 50:
                arr_r = np.array(boot_r)
                cv_r = float(np.std(arr_r, ddof=1) / np.mean(arr_r) * 100) if np.mean(arr_r) > 0 else float('inf')
                if np.isfinite(cv_r):
                    random_boot_cvs.append(cv_r)

        # Per-cancer CV (if available)
        if cancer_col:
            ratios_ct = []
            for ct, grp in drug_cancer_auc.groupby(cancer_col):
                grp_a = grp[grp['DRUG_UPPER'].isin(class_a_drugs)]
                grp_b = grp[grp['DRUG_UPPER'].isin(class_b_drugs)]
                if grp_a['count'].sum() < MIN_N_PER_ARM or grp_b['count'].sum() < MIN_N_PER_ARM:
                    continue
                if len(grp_a) + len(grp_b) < MIN_OBS_PER_CANCER:
                    continue
                wa_ct = grp_a['count'].values
                wb_ct = grp_b['count'].values
                if wa_ct.sum() == 0 or wb_ct.sum() == 0:
                    continue
                mean_a_ct = np.average(grp_a['mean'].values, weights=wa_ct)
                mean_b_ct = np.average(grp_b['mean'].values, weights=wb_ct)
                mag_a_ct = 1.0 - mean_a_ct
                mag_b_ct = 1.0 - mean_b_ct
                if mag_a_ct > 0.001 and mag_b_ct > 0.001:
                    r_ct = max(mag_a_ct, mag_b_ct) / min(mag_a_ct, mag_b_ct)
                    if np.isfinite(r_ct) and r_ct < 100:
                        ratios_ct.append(r_ct)
            if len(ratios_ct) >= 3:
                arr_ct = np.array(ratios_ct)
                cv_ct = float(np.std(arr_ct, ddof=1) / np.mean(arr_ct) * 100) if np.mean(arr_ct) > 0 else float('inf')
                if np.isfinite(cv_ct):
                    random_cvs.append(cv_ct)

    random_cvs = np.array(random_cvs) if random_cvs else np.array([])
    random_boot_cvs = np.array(random_boot_cvs)
    random_ratios = np.array(random_global_ratios)

    print(f"  Partitions aléatoires valides: {len(random_ratios)}")
    print(f"  Ratio global: médiane = {np.median(random_ratios):.3f}×, "
          f"IQR = [{np.percentile(random_ratios, 25):.3f}, {np.percentile(random_ratios, 75):.3f}]")

    if len(random_boot_cvs) > 0:
        print(f"  CV bootstrap (drogue): médiane = {np.median(random_boot_cvs):.1f}%, "
              f"IQR = [{np.percentile(random_boot_cvs, 25):.1f}%, {np.percentile(random_boot_cvs, 75):.1f}%]")
    if len(random_cvs) > 0:
        print(f"  CV cancer-type: médiane = {np.median(random_cvs):.1f}%, "
              f"IQR = [{np.percentile(random_cvs, 25):.1f}%, {np.percentile(random_cvs, 75):.1f}%]")

    # Percentile comparison
    for test_name, test_cvs, rand_cvs, label in [
        ('cancer-type', cv_results, random_cvs, 'CV par cancer type'),
        ('drug-bootstrap', boot_cv_results, random_boot_cvs, 'CV bootstrap drogues'),
    ]:
        if 'ONTO' in test_cvs and len(rand_cvs) > 0:
            onto_cv = test_cvs['ONTO']['cv_ratio']
            pct = float(np.mean(rand_cvs <= onto_cv) * 100)
            print(f"\n  {label}:")
            print(f"    CV ontodynamique ({onto_cv:.1f}%) est au percentile {pct:.1f}% des aléatoires")
            if pct < 5:
                print(f"    → p < 0.05: convergence SIGNIFICATIVEMENT meilleure que le hasard")
            elif pct < 10:
                print(f"    → marginalement significatif")
            else:
                print(f"    → non significatif")

    # ================================================================
    # SUMMARY TABLE
    # ================================================================
    print(f"\n{'=' * 75}")
    print(f"  TABLE RÉCAPITULATIVE")
    print(f"{'=' * 75}")

    # Decide which CV results to use for the main comparison
    main_cv = cv_results if cv_results else boot_cv_results
    cv_label = "CV cancer" if cv_results else "CV boot"

    header = (f"  {'Partition':<20s} {'Ratio global':>13s} {'|d| global':>11s} "
              f"{cv_label:>10s} {'CV boot':>10s}")
    print(header)
    print(f"  {'─' * 20} {'─' * 13} {'─' * 11} {'─' * 10} {'─' * 10}")

    for col, name in [('ONTO', 'Ontodynamique'), ('PPI', 'Degré PPI'), ('SEL', 'Sélectivité')]:
        gr = global_results.get(col)
        cv_cancer = cv_results.get(col, {}).get('cv_ratio', None)
        cv_boot = boot_cv_results.get(col, {}).get('cv_ratio', None)
        if gr:
            cv_c_str = f"{cv_cancer:.1f}%" if cv_cancer is not None else "—"
            cv_b_str = f"{cv_boot:.1f}%" if cv_boot is not None else "—"
            print(f"  {name:<20s} {gr['ratio']:>12.3f}× {gr['abs_d']:>11.4f} "
                  f"{cv_c_str:>10s} {cv_b_str:>10s}")

    if len(random_boot_cvs) > 0:
        med_r = np.median(random_ratios) if len(random_ratios) > 0 else 0
        med_cv_b = np.median(random_boot_cvs)
        med_cv_c = np.median(random_cvs) if len(random_cvs) > 0 else None
        cv_c_str = f"{med_cv_c:.1f}%" if med_cv_c is not None else "—"
        print(f"  {'Aléatoire (méd.)':<20s} {med_r:>12.3f}× {'—':>11s} "
              f"{cv_c_str:>10s} {med_cv_b:>9.1f}%")

    # ================================================================
    # VISUALIZATION
    # ================================================================
    print(f"\n{'=' * 75}")
    print(f"  FIGURES")
    print(f"{'=' * 75}")

    # Use whichever CV results are available
    plot_cv = cv_results if cv_results else boot_cv_results
    plot_rand_cvs = random_cvs if len(random_cvs) > 0 else random_boot_cvs
    cv_mode = "cancer type" if cv_results else "drug bootstrap"

    fig, axes = plt.subplots(2, 2, figsize=(14, 11))
    fig.suptitle('R-XVII Rival Partition Test — GDSC\n'
                 'La partition ontodynamique est-elle spécifiquement discriminante?',
                 fontsize=13, fontweight='bold')

    # Panel 1: CV comparison bar chart
    ax = axes[0, 0]
    names_cv = []
    vals_cv = []
    colors_cv = []
    for col, name, color in [('ONTO', 'Ontodynamique', '#1565C0'),
                               ('PPI', 'Degré PPI', '#6A1B9A'),
                               ('SEL', 'Sélectivité', '#E65100')]:
        if col in plot_cv:
            names_cv.append(name)
            vals_cv.append(plot_cv[col]['cv_ratio'])
            colors_cv.append(color)

    if len(plot_rand_cvs) > 0:
        names_cv.append('Aléatoire\n(médiane)')
        vals_cv.append(float(np.median(plot_rand_cvs)))
        colors_cv.append('#9E9E9E')

    if vals_cv:
        bars = ax.bar(names_cv, vals_cv, color=colors_cv, alpha=0.8, edgecolor='black', lw=0.5)
        ax.set_ylabel('CV du ratio (%)')
        ax.set_title(f'CV du ratio par {cv_mode}\n(plus bas = plus convergent)')
        for bar, val in zip(bars, vals_cv):
            ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.5,
                    f'{val:.1f}%', ha='center', fontsize=10, fontweight='bold')

    # Panel 2: Bootstrap CI or cancer-type ratios
    ax = axes[0, 1]
    if cv_results:
        # Ratio by cancer type for each partition
        offsets = {'ONTO': -0.25, 'PPI': 0, 'SEL': 0.25}
        colors_part = {'ONTO': '#1565C0', 'PPI': '#6A1B9A', 'SEL': '#E65100'}
        labels_part = {'ONTO': 'Ontodynamique', 'PPI': 'Degré PPI', 'SEL': 'Sélectivité'}
        all_cancer_types = set()
        for col in ['ONTO', 'PPI', 'SEL']:
            if col in cv_results:
                for pc in cv_results[col]['per_cancer']:
                    all_cancer_types.add(pc['cancer_type'])
        cancer_type_list = sorted(all_cancer_types)
        if cancer_type_list:
            y_pos = np.arange(len(cancer_type_list))
            for col in ['ONTO', 'PPI', 'SEL']:
                if col not in cv_results:
                    continue
                ratios_by_ct = {pc['cancer_type']: pc['ratio']
                                for pc in cv_results[col]['per_cancer']}
                vals = [ratios_by_ct.get(ct, np.nan) for ct in cancer_type_list]
                ax.barh(y_pos + offsets[col], vals, 0.22,
                        color=colors_part[col], alpha=0.7, label=labels_part[col])
            ax.set_yticks(y_pos)
            ax.set_yticklabels([ct[:18] for ct in cancer_type_list], fontsize=7)
            ax.axvline(1.0, color='gray', ls='-', lw=0.5)
            ax.set_xlabel('Ratio magnitude (A/B)')
            ax.set_title('Ratio par type de cancer et partition')
            ax.legend(fontsize=7, loc='lower right')
    elif boot_cv_results:
        # Show bootstrap distributions
        colors_boot = {'ONTO': '#1565C0', 'PPI': '#6A1B9A', 'SEL': '#E65100'}
        labels_boot = {'ONTO': 'Ontodynamique', 'PPI': 'Degré PPI', 'SEL': 'Sélectivité'}
        for col in ['ONTO', 'PPI', 'SEL']:
            if col in boot_cv_results and 'boot_ratios' in boot_cv_results[col]:
                ax.hist(boot_cv_results[col]['boot_ratios'], bins=50, alpha=0.4,
                        color=colors_boot[col], density=True, label=labels_boot[col])
        ax.axvline(1.0, color='gray', ls='-', lw=0.5)
        ax.set_xlabel('Ratio S/I (bootstrap)')
        ax.set_ylabel('Densité')
        ax.set_title('Distribution bootstrap du ratio par partition')
        ax.legend(fontsize=8)

    # Panel 3: Distribution of random CVs with observed CVs marked
    ax = axes[1, 0]
    if len(plot_rand_cvs) > 0:
        ax.hist(plot_rand_cvs, bins=50, alpha=0.6, color='#9E9E9E', density=True,
                label='Partitions aléatoires')
        for col, name, color in [('ONTO', 'Onto.', '#1565C0'),
                                   ('PPI', 'PPI', '#6A1B9A'),
                                   ('SEL', 'Sél.', '#E65100')]:
            if col in plot_cv:
                ax.axvline(plot_cv[col]['cv_ratio'], color=color, lw=2.5,
                           label=f'{name}: {plot_cv[col]["cv_ratio"]:.1f}%')
        ax.set_xlabel('CV du ratio (%)')
        ax.set_ylabel('Densité')
        ax.set_title(f'CV observés vs {N_RANDOM} partitions aléatoires\n({cv_mode})')
        ax.legend(fontsize=8)

    # Panel 4: Global ratio comparison
    ax = axes[1, 1]
    if len(random_ratios) > 0:
        ax.hist(random_ratios, bins=50, alpha=0.6, color='#9E9E9E', density=True,
                label='Partitions aléatoires')
        for col, name, color in [('ONTO', 'Onto.', '#1565C0'),
                                   ('PPI', 'PPI', '#6A1B9A'),
                                   ('SEL', 'Sél.', '#E65100')]:
            if col in global_results:
                ax.axvline(global_results[col]['ratio'], color=color, lw=2.5,
                           label=f'{name}: {global_results[col]["ratio"]:.3f}×')
        ax.set_xlabel('Ratio magnitude (A/B)')
        ax.set_ylabel('Densité')
        ax.set_title('Ratio global: observé vs aléatoire')
        ax.legend(fontsize=8)

    plt.tight_layout()
    fig_path = OUT_DIR / 'rival_partitions_comparison.png'
    plt.savefig(fig_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"  → {fig_path}")

    # ================================================================
    # EXPORT JSON
    # ================================================================
    export = {
        'protocol': 'R-XVII rival partition test',
        'n_random': N_RANDOM,
        'min_obs_per_cancer': MIN_OBS_PER_CANCER,
        'cancer_col': cancer_col,
        'cv_mode': cv_mode,
        'global': {},
        'cv_cancer': {},
        'cv_bootstrap': {},
        'random_summary': {},
    }
    for col in ['ONTO', 'PPI', 'SEL']:
        if col in global_results:
            export['global'][col] = global_results[col]
        if col in cv_results:
            export['cv_cancer'][col] = {k: v for k, v in cv_results[col].items()
                                         if k != 'ratios'}
        if col in boot_cv_results:
            export['cv_bootstrap'][col] = {k: v for k, v in boot_cv_results[col].items()
                                            if k != 'boot_ratios'}

    if len(random_boot_cvs) > 0:
        export['random_summary']['boot'] = {
            'n_valid': int(len(random_boot_cvs)),
            'cv_median': float(np.median(random_boot_cvs)),
            'cv_q25': float(np.percentile(random_boot_cvs, 25)),
            'cv_q75': float(np.percentile(random_boot_cvs, 75)),
        }
    if len(random_ratios) > 0:
        export['random_summary']['ratio_median'] = float(np.median(random_ratios))
    if len(random_cvs) > 0:
        export['random_summary']['cancer_type'] = {
            'n_valid': int(len(random_cvs)),
            'cv_median': float(np.median(random_cvs)),
        }

    # Percentile info
    for test_key, test_cvs, rand_cvs in [
        ('cancer_type_percentile', cv_results, random_cvs),
        ('boot_percentile', boot_cv_results, random_boot_cvs),
    ]:
        if 'ONTO' in test_cvs and len(rand_cvs) > 0:
            export['random_summary'][test_key] = float(
                np.mean(rand_cvs <= test_cvs['ONTO']['cv_ratio']) * 100)

    def nc(o):
        if isinstance(o, (np.integer,)): return int(o)
        if isinstance(o, (np.floating,)): return float(o)
        if isinstance(o, np.ndarray): return o.tolist()
        if isinstance(o, np.bool_): return bool(o)
        raise TypeError(f"{type(o)}")

    json_path = OUT_DIR / 'rival_partitions_results.json'
    with open(json_path, 'w') as f:
        json.dump(export, f, indent=2, default=nc)
    print(f"  → {json_path}")

    # ================================================================
    # VERDICT
    # ================================================================
    print(f"\n{'=' * 75}")
    print(f"  VERDICT")
    print(f"{'=' * 75}")

    # Use whichever CV results are available
    verdict_cv = cv_results if cv_results else boot_cv_results
    verdict_rand = random_cvs if len(random_cvs) > 0 else random_boot_cvs

    if 'ONTO' in verdict_cv and len(verdict_rand) > 0:
        onto_cv = verdict_cv['ONTO']['cv_ratio']
        ppi_cv = verdict_cv.get('PPI', {}).get('cv_ratio', float('inf'))
        sel_cv = verdict_cv.get('SEL', {}).get('cv_ratio', float('inf'))
        rand_med_cv = float(np.median(verdict_rand))

        print(f"\n  Mode: {cv_mode}")
        print(f"  CV ontodynamique:  {onto_cv:.1f}%")
        print(f"  CV degré PPI:      {ppi_cv:.1f}%")
        print(f"  CV sélectivité:    {sel_cv:.1f}%")
        print(f"  CV aléatoire (méd):{rand_med_cv:.1f}%")

        pct = float(np.mean(verdict_rand <= onto_cv) * 100)
        print(f"  Percentile ontodynamique parmi aléatoires: {pct:.1f}%")

        if onto_cv < ppi_cv and onto_cv < sel_cv and onto_cv < rand_med_cv:
            if onto_cv < 0.5 * min(ppi_cv, sel_cv):
                print(f"\n  ★ RÉSULTAT FORT: la partition ontodynamique converge")
                print(f"    significativement mieux que TOUTES les rivales.")
                print(f"    L'objection d'accommodance est sérieusement entamée.")
            else:
                print(f"\n  ★ RÉSULTAT MODÉRÉ: la partition ontodynamique converge")
                print(f"    mieux, mais l'écart avec les rivales est modeste.")
        elif onto_cv < rand_med_cv:
            print(f"\n  ★ RÉSULTAT MIXTE: la partition ontodynamique converge mieux")
            print(f"    que le hasard, mais une partition rivale fait aussi bien.")
            print(f"    L'objection d'accommodance reste partiellement ouverte.")
        else:
            print(f"\n  ★ RÉSULTAT NÉGATIF: la partition ontodynamique ne converge")
            print(f"    pas mieux que le hasard. L'objection d'accommodance")
            print(f"    n'est pas réfutée par ce test.")

        # Additional context for bootstrap-only mode
        if not cv_results:
            print(f"\n  ⚠ NOTE: Ce verdict est basé sur le bootstrap par drogues.")
            print(f"    Pour le test complet par type de cancer, fournir un fichier")
            print(f"    d'annotations (cell_line_annotations.csv) avec COSMIC_ID")
            print(f"    et TCGA_DESC. Téléchargeable sur cancerrxgene.org.")
    else:
        # Fallback: just compare global results
        print(f"\n  Résultats globaux seulement (pas de sous-domaines):")
        for col, name in [('ONTO', 'Ontodynamique'), ('PPI', 'Degré PPI'), ('SEL', 'Sélectivité')]:
            if col in global_results:
                r = global_results[col]
                print(f"    {name}: ratio={r['ratio']:.3f}×, |d|={r['abs_d']:.4f}, p={r['p_MW']:.2e}")

    elapsed = time.time() - t0
    print(f"\n  Temps: {elapsed:.1f}s")


if __name__ == '__main__':
    main()