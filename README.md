# Ontodynamique — Formal System and Empirical Validation

[![Lean 4](https://img.shields.io/badge/Lean_4-504_theorems-blue)]()
[![sorry](https://img.shields.io/badge/sorry-0-brightgreen)]()
[![Domains](https://img.shields.io/badge/domains-4_validated-orange)]()
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC_BY_4.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)

**Ontodynamique** is a formal ontological framework built from two independent axioms — *Axiom I* (being = doing: every entity is an act of self-maintenance whose cost is drawn from the very structure it maintains) and *Axiom V* (exteriority admits degrees) — from which it derives finitude, irreversibility, operational closure, constitutive normativity, and a compositional gradient that classifies any finite system as *closure* (endogenous cost-bearing), *normative carriage* (externalized cost), or *aggregate* (no cycle).

The central empirical prediction is **R-XVII**: perturbations targeting the *structure* of a system (its self-maintenance machinery) produce systematically larger displacement than perturbations targeting its *input* (its metabolic flow), at matched intensity. This asymmetry is indexed on the topological target of the perturbation, not on its amplitude.

📖 **Manuscript**: [ontodynamique.com](https://www.ontodynamique.com/)  
🧪 **Interactive notebook**: [Google Colab](https://colab.research.google.com/drive/1LWbOqywO5o6AtePQRu3plooqwuOtzJrN?usp=sharing)

---

## Cross-Domain Results

The R-XVII signature converges across three causally disjoint biological domains:

| Domain | Dataset | n | Cohen's *d* | Ratio S/I | *p* |
|--------|---------|---|------------|-----------|-----|
| Gut microbiome | MDSINE2 (Gibson et al. 2025) | 9 subjects | 1.16 | 1.61× | 0.0006 |
| Coral reefs | GCBD (van Woesik & Kratochwill 2022) | 34,393 obs | 0.39 | 1.80× | 1.96 × 10⁻⁴⁸ |
| Cancer pharmacology | GDSC (Iorio et al. 2016) | 216,764 obs | 0.52 | 1.85× | < 10⁻³⁰⁰ |

**Cross-domain convergence**: ratio S/I ≈ 1.8×, CV = 7.2%.  
**Specificity**: under intensity-based classification, ratios diverge (CV = 33%). Over 100,000 random binary partitions, none achieves a mean ratio ≥ 1.3 (*p* < 10⁻⁵).

Validation splits:
- **Coral reefs (CR-02A)**: temporal split at 2010 — *d*_TEST = 0.400, ratio S/I = 2.18×, *d*_TEST within bootstrap CI of TRAIN.
- **Cancer (CR-02B)**: 70/30 cell-line split, 10 seeds — median ratio = 1.846×, CV = 1.3%, 10/10 significant.

---

## Lean 4 Formalization

The deductive core is mechanized in Lean 4 across 14 files:

- **504 theorems, 0 `sorry`**, no domain axiom beyond Lean's standard logical axioms (`propext`, `Quot.sound`)
- **2 axioms** (I = α + β, V) + **1 corollary** (IV)
- I-γ ("no act without mode"), II, III, VII **derived** as theorems
- **10 separating models** proving inter-axiom independence (I ⊥ V)
- **6 separating models** proving mutual independence of I-β components
- R-XVIII asymmetry derived via `template_saving`

Key files:
| File | Content |
|------|---------|
| `Lean/Autodynamique.lean` | Structural trunk (101 theorems) |
| `Lean/gradient.lean` | R-XVII/R-XVIII compositional gradient |
| `Lean/Conscience.lean` | Subjectivity chain, valence, paliers |
| `Lean/DPDRDerived.lean` | DPDR predictions (20 theorems) |
| `Lean/InterAxiomIndependence.lean` | Separating models |
| `Lean/SeparatingModels.lean` | I-β component independence |
| `Lean/DomainRestriction.lean` | I-β weakening map (94 theorems classified) |
| `Lean/Bridjes.lean` | Bridge hypotheses (microbiome, software debt) |

---

## Repository Structure

```
ontodynamiqueTheory/
├── Lean/                      # Lean 4 formalization (14 files)
├── ScriptMDSINE2/             # Microbiome analysis (MDSINE2)
│   ├── 01_phase1_raw_metrics.py
│   ├── 02_phase2_corrected.py
│   ├── 03_phase3_interaction_matrix.py
│   └── 04_robustness_metrics.py
├── ScriptCorail/              # Coral reef analysis (GCBD)
│   ├── corail.py              # Core R-XVII asymmetry test
│   ├── robustness_reef.py     # 4 response transformations
│   └── reef_temporal_split.py # CR-02A temporal validation
├── ScriptGDSC/                # Cancer pharmacology (GDSC)
│   ├── GDSC1.py               # Full analysis with sensitivity sweep
│   ├── GDSC2.py               # Pathway-only classification (v2)
│   └── gdsc_cellline_split.py # CR-02B cell-line validation
├── ScriptCrossDomain/         # Specificity & cross-domain tests
│   ├── SpecifityCheck.py      # 100k permutations, reversibility, target count
│   └── Sentsivity.py          # Sensitivity analysis
├── output/                    # Generated figures and JSON results
├── Ontoaudit4.lean            # Standalone audit file
├── requirements.txt
├── run_all.sh
└── README.md
```

---

## Quick Start

### Option A: Google Colab (recommended)

Open the [Colab notebook](https://colab.research.google.com/drive/1LWbOqywO5o6AtePQRu3plooqwuOtzJrN?usp=sharing) — it handles all dependencies, data download, Lean installation, and runs every script with full output.

### Option B: Local installation

```bash
# 1. Clone
git clone https://github.com/anthonyGosme/ontodynamiqueTheory
cd ontodynamiqueTheory

# 2. Python environment
python3 -m venv venv && source venv/bin/activate
pip install -r requirements.txt

# 3. MDSINE2 (microbiome scripts only)
git clone https://github.com/gerberlab/MDSINE2.git
pip install MDSINE2/.
git clone https://github.com/gerberlab/MDSINE2_Paper.git

# 4. Lean 4 (formalization verification)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain stable
export PATH="$HOME/.elan/bin:$PATH"

# 5. Run everything
bash run_all.sh
```

### Data Sources

| Domain | Dataset | Source |
|--------|---------|--------|
| Microbiome | MDSINE2 | [gerberlab/MDSINE2_Paper](https://github.com/gerberlab/MDSINE2_Paper) |
| Coral reefs | GCBD | [BCO-DMO 773466](https://www.bco-dmo.org/dataset/773466) (DOI: 10.26008/1912/bco-dmo.773466.2) |
| Cancer | GDSC | [Sanger dose-response](https://github.com/rahiuhn/GDSC_datasets) |

---

## Robustness

The R-XVII asymmetry has been tested for robustness along multiple axes:

- **Microbiome**: 5/5 distance metrics significant (Bray-Curtis, Jensen-Shannon, Aitchison, Hellinger, Canberra; all *p* < 0.001)
- **Coral reefs**: 23/23 DHW thresholds, 9/10 ocean regions, 4/4 response transformations significant; sigmoid threshold stable at DHW ≈ 7.9
- **Cancer**: stable from IC30 to IC70; 9/9 pathways significant; dose-matched control preserves ratio (1.81×)
- **Cross-domain specificity**: no random partition (n = 100,000) achieves mean ratio ≥ 1.3; reversibility partition dominated 2.8× by R-XVII; target-count partition not operable cross-domain

---

## References

- Gibson, T.E. et al. (2025). Ecosystem-scale dynamics from microbiome data with MDSINE2. *Nature Microbiology*.
- van Woesik, R. & Kratochwill, C. (2022). Global coral bleaching and environmental data. *BCO-DMO*. DOI: 10.26008/1912/bco-dmo.773466.2
- Iorio, F. et al. (2016). A landscape of pharmacogenomic interactions in cancer. *Cell*, 166(3), 740–754.
- Gosme, A. (2025). Causal symmetrization as empirical signature of operational autonomy. *arXiv:2512.09352*.
- Gosme, A. (2026). DPDR protocol — pre-registered. *OSF*. DOI: 10.17605/OSF.IO/ZMH54

---

## Author

**Anthony Gosme** — Independent researcher  
[ontodynamique.com](https://www.ontodynamique.com/)

## License

This work is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).