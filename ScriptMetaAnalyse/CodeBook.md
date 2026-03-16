# Codebook: Input / Structure Classification

> **Purpose**: Make the I/S partition auditable and reproducible by a third party.
> Each row documents one perturbation arm with the formal criterion it satisfies
> and a pointer to the implementing code.
>
> **Applicability conditions** (from the manuscript):
> - **C1** — Classification is non-circular: it depends only on the nature of the perturbation, never on the observed response.
> - **C2** — Temporal symmetry: both arms operate in the same temporal regime (same duration, same measurement window).
> - **C3** — Degree of closure is estimable independently of the test.

---

## 1. Microbiome (MDSINE2) — Gibson et al. mouse gut

| Perturbation | Class | Criterion | Justification | Code ref |
|---|---|---|---|---|
| High-fat diet (HFD), days 21.5–28.5 | **INPUT** | C1: perturbation modifies metabolic flux (nutrient composition) without destroying taxa | Dietary shift alters substrate availability; no antibiotic killing; taxonomic composition changes are secondary to flux change | `ScriptMDSINE2/04_robustness_metrics.py` L240: `'HFD': ('input', 28.5, 35.5)` |
| Vancomycin, days 35.5–42.5 | **STRUCTURE** | C1: antibiotic selectively destroys Gram-positive taxa (structural components of the community) | Vancomycin targets cell wall synthesis → bactericidal against Gram-positives → removes structural elements | `ScriptMDSINE2/04_robustness_metrics.py` L241: `'vancomycin': ('hardware', 42.5, 50.5)` |
| Gentamicin, days 50.5–57.5 | **STRUCTURE** | C1: aminoglycoside antibiotic destroys Gram-negative taxa | Gentamicin inhibits 30S ribosomal subunit → bactericidal → removes structural elements | `ScriptMDSINE2/04_robustness_metrics.py` L242: `'gentamicin': ('hardware', 57.5, 65.0)` |

**Response variable**: Bray-Curtis distance from global baseline (late equilibration, t = 15–21.5 days).
Measured in late recovery only (t_since_perturbation ≥ 4 days).

**Baseline**: Mean relative abundance profile over the last 3+ samples of the equilibration phase (t ∈ [15, 21.5)), shared across all perturbation comparisons (global baseline design fixes the sequential drift confound identified in Phase 1).

**C2 check**: All three perturbations last 7 days; recovery is measured in the same 7-day window post-perturbation. ✓

**Code ref** (data loading): `ScriptMDSINE2/04_robustness_metrics.py` L95–96 (Study.load), L125–133 (extract_data), L218–256 (compute_rxvii_all_metrics). Requires `_patch_llvmlite()` (L50–86) before `import mdsine2`.

**Sample sizes**: n_input = 10 (5 subjects × 2 late-recovery timepoints), n_structure = 30 (5 subjects × 2 antibiotics × 3 late-recovery timepoints).

---

## 2. Coral Reefs (GCBD) — Global Coral Bleaching Database

| Perturbation | Class | Criterion | Justification | Code ref |
|---|---|---|---|---|
| Thermal stress: 4 ≤ DHW < 8, cyclone ≤ median | **INPUT** | C1: sub-lethal heat stress modifies metabolic flux (photosynthesis disruption) without destroying reef builders; NOAA Bleaching Alert Level 1 | DHW 4–8 causes symbiont expulsion (metabolic stress) but coral skeleton and tissue remain intact | `ScriptCorail/corail.py` L78: `pt[(dhw >= 4) & (dhw < 8) & (cyc <= cyc_med)] = 'input'` |
| Thermal stress: DHW ≥ 8 | **STRUCTURE** | C1: mortality-level heat (NOAA Alert Level 2+) destroys coral tissue, the structural builder of the reef | DHW ≥ 8 causes widespread mortality; the organism maintaining reef structure is physically destroyed | `ScriptCorail/corail.py` L79: `pt[(dhw >= 8) | (cyc > cyc_med * 1.5)] = 'structure'` |
| Cyclone frequency > 1.5 × median | **STRUCTURE** | C1: physical destruction of reef framework (mechanical breakage of skeleton) | Cyclones fracture coral colonies — direct structural damage independent of thermal stress | `ScriptCorail/corail.py` L79 (same line, OR condition) |
| DHW < 4 | **BASELINE** | No significant thermal stress | Below NOAA bleaching watch threshold | `ScriptCorail/corail.py` L77: `pt = pd.Series('baseline', index=df.index)` |

**Response variable**: `Percent_Bleaching` (site-level survey, 0–100%).

**Classification is strictly exogenous**: DHW is satellite-derived (NOAA Coral Reef Watch); cyclone frequency is meteorological. Bleaching % is **never** used in the classification — it is exclusively the response variable. This is stated explicitly in the code docstring (L56–71).

**C2 check**: Both arms are measured at the same temporal resolution (site-year observations). No pulse/press asymmetry. ✓

**Code ref** (data loading): `ScriptCorail/corail.py` L32–51 (load), L54–87 (classify_clean), L91–120 (test_asymmetry).

**Sample sizes**: n_input = 2,949; n_structure = 3,685; n_baseline = 27,759.

---

## 3. Cancer Pharmacology (GDSC) — Sanger Genomics of Drug Sensitivity in Cancer

| Perturbation | Class | Criterion | Justification | Code ref |
|---|---|---|---|---|
| **Signaling modulators** (pathway-only): ERK MAPK, PI3K/MTOR, EGFR, RTK, Hormone-related, WNT, JNK/p38, Metabolism, Immune response | **INPUT** | C1: these drugs modulate information-processing cascades (kinase signaling, receptor activation, metabolic flux) without targeting maintenance machinery | Mechanism of action = flux modulation; the cellular structural integrity machinery is not the direct target | `ScriptGDSC/GDSC2.py` L92–146 (`_input_drugs` dict), L194–200 (`pathway_type`) |
| **Maintenance-targeting drugs** (pathway-only): Genome integrity, DNA replication, Cell cycle, Mitosis, Protein stability/degradation, Apoptosis regulation, Chromatin | **STRUCTURE** | C1: these drugs target the machinery that maintains cellular structural integrity (DNA repair, proteasome, mitotic spindle, cell cycle checkpoints) | Mechanism of action = destruction or disabling of maintenance components; analogous to removing structural elements | `ScriptGDSC/GDSC2.py` L50–90 (`_struct_drugs` dict), L194–200 (`pathway_type`) |
| Unmapped drugs (no known pathway) | **EXCLUDED** | Cannot classify without mechanism of action | 44.1% of observations excluded (170,862/387,626) | `ScriptGDSC/GDSC2.py` L199: `return None` |

**Response variable**: `AUC_PUBLISHED` (Area Under dose-response Curve; 1 = no effect, 0 = complete killing). Perturbation magnitude = 1 − AUC.

**Classification mode**: **Pathway-only** (used in the preprint). The alternative dose-classified mode (GDSC1.py L246–259) reclassifies INPUT drugs at supra-lethal doses as STRUCTURE; this produces a different ratio (~4.95×) and is documented as a robustness variant, not the primary analysis.

**C1 check**: Classification depends exclusively on the drug's mechanism of action (a property of the treatment), never on the cellular response (AUC). ✓

**C2 check**: All drug-cell line pairs measured in the same experimental protocol (72h exposure, same readout). ✓

**Drug → pathway mapping**: `ScriptGDSC/GDSC2.py` L50–146 (explicit drug lists per pathway) + L159–192 (`map_drug()` with direct match, then pattern fallback).

**Sample sizes**: n_input = 119,090; n_structure = 97,674.

---

## 4. Yeast — Haploid/Homozygous Deletions (Exploratory)

| Perturbation | Class | Criterion | Justification | Code ref |
|---|---|---|---|---|
| Genes annotated to INPUT GO terms only (24 terms: signal transduction, MAPK, GTPase, GPCR, TOR, phosphorylation, transmembrane transport, stress response) | **INPUT** | C1: knockout of a gene whose function is signal processing / flux regulation, not structural maintenance | These genes mediate information flow (signaling cascades, ion transport, stress sensing); their deletion modifies the cell's input-processing capacity | `ScriptYeast/RXVII.py` L37–44 (`INPUT_TERMS`), L73: `elif is_i and not is_s` |
| Genes annotated to STRUCTURE GO terms only (23 terms: DNA repair, proteasome, chaperones, ERAD, cell cycle/division, DNA replication, cell wall, mitochondria, ribosome biogenesis, chromatin, chromosome segregation) | **STRUCTURE** | C1: knockout of a gene whose function is structural maintenance of the cell | These genes maintain cellular infrastructure (genome integrity, protein quality control, cell division machinery); their deletion removes structural maintenance capacity | `ScriptYeast/RXVII.py` L29–36 (`STRUCTURE_TERMS`), L71: `if is_s and not is_i` |
| Genes annotated to BOTH S and I terms | **EXCLUDED** | Ambiguous classification | 69 genes excluded (from `gene_classification.tsv`: 1,204 S, 589 I, 69 BOTH, 5,267 NONE) | `ScriptYeast/RXVII.py` L69–74 (mutual exclusion logic) |
| Genes annotated to neither | **EXCLUDED** | No relevant GO annotation | 5,267 genes unclassified | implicit: only genes matching S or I terms are assigned |

**Response variable**: Mean |z-score| across 273 Hillenmeyer chemical stress screens (per gene).

**Screen selection**: Hillenmeyer et al. screens within the hom/haploid collection. Selected by matching `paper` column containing "Hillenmeyer" and `collection` containing "hom" in the screen metadata file.

**GO annotation source**: `gene_association.sgd.20251124.gaf` (SGD Gene Ontology annotations, Nov 2024). Annotations with `NOT` qualifier are excluded. Only direct annotations (no OBO hierarchy propagation).

**C1 check**: Classification depends on the gene's GO functional annotation (a property of the gene), never on the fitness phenotype under perturbation. ✓

**C2 check**: All genes measured under the same screens, same protocol, same temporal regime. ✓

**Code ref** (data loading): `ScriptYeast/RXVII.py` L47–77 (`load_gaf`), L80–95 (`select_chemical_screens`), L155–176 (matrix loading + severity computation).

**Sample sizes**: n_structure = 713 genes; n_input = 509 genes; 273 screens.

---

## 5. Yeast — Heterozygous Deletions (Confirmatory, Pre-registered)

| Perturbation | Class | Criterion | Justification | Code ref |
|---|---|---|---|---|
| Same GO partition as Test 4 | **INPUT** / **STRUCTURE** | Same as above | Same GO terms, same exclusion rule | Same as Test 4 |

**Differences from exploratory test** (documented in `ScriptYeast/README.md` §7):
- Collection: heterozygous diploid (haploinsufficiency, not complete knockout)
- Essential genes present (absent in hom collection)
- No Hillenmeyer screens in het collection → falls back to all chemical screens (6,946 screens)
- Pre-registered on OSF: DOI [10.17605/OSF.IO/S7CN9](https://osf.io/s7cn9/)
- Decision criteria (from pre-registration §6.2): ratio > 1.0, p < 0.01, CI_low > 1.0, permutation p < 0.001

**Response variable**: Mean |z-score| across 6,946 all-chemical screens (per gene).

**Screen selection**: All screens with concentration annotation (regex `[uUnNmMg%]` in conditionset), excluding standard/control/untreated/DMSO.

**Code ref**: `ScriptYeast/RXVII.py` L80–95 (`select_chemical_screens`, `all_chemical` branch), L178–187 (fallback to `chem_cols` when `hillen_cols` is empty).

**Sample sizes**: n_structure = 1,125; n_input = 538.

---

## 6. EXCLUDED — Cedar Creek (Biodiversity Experiment)

| Domain | Reason for exclusion | Condition violated |
|---|---|---|
| Cedar Creek LTER biodiversity experiment | Pulse/press design creates temporal asymmetry between arms | **C2 violated**: the "press" treatment (sustained species removal) operates over years, while "pulse" treatments are transient. The two arms are not in the same temporal regime. |

**Note**: No code exists in the repository for Cedar Creek. The exclusion was decided at the design stage, before implementation, based on the C2 applicability condition.

---

## Summary Table

| # | Domain | Dataset | n_I | n_S | Classification basis | Response variable | C1 | C2 | C3 | Status |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | Microbiome | MDSINE2 (Gibson) | 10 | 30 | Perturbation type (diet vs antibiotic) | Bray-Curtis from baseline | ✓ | ✓ | ✓ | Exploratory |
| 2 | Coral reefs | GCBD | 2,949 | 3,685 | Exogenous physical variables (DHW, cyclone) | % bleaching | ✓ | ✓ | ✓ | Exploratory |
| 3 | Cancer | GDSC (Sanger) | 119,090 | 97,674 | Drug mechanism of action (pathway-only) | 1 − AUC | ✓ | ✓ | ✓ | Exploratory |
| 4 | Yeast (hom) | Yeast Phenome | 509 | 713 | GO functional annotation | Mean \|z-score\| | ✓ | ✓ | ✓ | Exploratory |
| 5 | Yeast (het) | Yeast Phenome | 538 | 1,125 | GO functional annotation | Mean \|z-score\| | ✓ | ✓ | ✓ | Confirmatory (OSF) |
| 6 | Biodiversity | Cedar Creek | — | — | — | — | ✓ | ✗ | — | **Excluded** |