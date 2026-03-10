# Ontodynamique — MDSINE2 Empirical Validation

Validation empirique des prédictions ontodynamiques (R-XVII, Γ, diversité effective)
sur le dataset MDSINE2 (Gibson et al. 2025, Nature Microbiology).

## Résultats clés

| Test | Résultat | Statut |
|------|----------|--------|
| R-XVII input/hardware asymétrie | p = 0.0006, d = 1.16 (dysbiotique) | ✓ Confirmé |
| Diversité effective H vs D | 14.7 ± 2.6 vs 9.6 ± 2.0 | ✓ Confirmé |
| Γ_corrected (recovery_3) | H > D, p = 0.006 | ✓ Confirmé |
| Ratio de variance | H = 0.50× vs D = 2.03× | ✓ Exploitable |

## Installation

```bash
# 1. Cloner ce repo
git clone https://github.com/anthonyGosme/ontodynamiqueTheory
cd ontodynamiqueTheory

# 2. Créer un environnement virtuel
python3 -m venv venv
source venv/bin/activate

# 3. Installer les dépendances
pip install -r requirements.txt

# 4. Cloner MDSINE2 et installer
git clone https://github.com/gerberlab/MDSINE2.git

pip install MDSINE2/.


MAC:
pip install ete3 --no-deps
pip install llvmlite --only-binary=:all:
pip install numba --only-binary=:all:
pip install PyQt5 --only-binary=:all:
pip install ./MDSINE2 --no-build-isolation











# 5. Cloner le repo MDSINE2_Paper (contient les données)
git clone https://github.com/gerberlab/MDSINE2_Paper.git
```

## Structure des données attendue

```
ontodynamiqueTheory/
├── MDSINE2_Paper/
│   └── datasets/gibson/
│       ├── healthy/preprocessed/gibson_healthy_agg_filtered.pkl
│       └── uc/preprocessed/gibson_uc_agg_filtered.pkl
├── scripts/
│   ├── 01_phase1_raw_metrics.py      # Exploration initiale (problèmes méthodologiques documentés)
│   ├── 02_phase2_corrected.py        # *** Résultats publiables ***
│   └── 03_phase3_interaction_matrix.py # Tentative gLV ridge (non concluant — nécessite MCMC)
├── output/                            # Figures et résultats générés ici
├── requirements.txt
├── run_all.sh
└── README.md
```

## Exécution

```bash
# Tout lancer d'un coup
bash run_all.sh

# Ou script par script
python scripts/01_phase1_raw_metrics.py
python scripts/02_phase2_corrected.py
python scripts/03_phase3_interaction_matrix.py
```

Les figures sont générées dans `output/`.

## Notes méthodologiques

### Phase 1 — Problèmes identifiés et corrigés en Phase 2
- Γ inversé : artefact de faible diversité (systèmes pauvres = rangs trivialement stables)
- R-XVII non significatif : baselines séquentielles → dérive entre comparaisons
- Granger sous-puissé : n=4-5 sujets, 8-15 points par phase

### Phase 2 — Corrections appliquées
- Γ normalisé par diversité effective : `Γ = (rank_persistence × log(eff_diversity)) / (1 + activity_flux)`
- R-XVII avec baseline globale unique (pré-perturbation, t=15-21.5)
- VAR Granger sur composantes PCA (toujours sous-puissé mais pattern qualitatif)

### Phase 3 — Pourquoi la ridge regression ne remplace pas MCMC
- 50 régresseurs pour 70-75 points → R² ≈ 0.75 dans les deux cohorts (overfitting)
- Phases individuelles : R² > 0.95 = bruit capturé autant que signal
- Topologie (réciprocité ≈ 0.09) identique entre cohorts
- **Conclusion** : le Γ topologique nécessite les posteriors bayésiens de MDSINE2 (~300 Go sur Zenodo)
  ou un dataset avec n >> 9 sujets

## Références

- Gibson et al. (2025). Learning ecosystem-scale dynamics from microbiome data with MDSINE2. *Nature Microbiology*.
- Gosme (2025). Causal symmetrization as empirical signature of operational autonomy. *arXiv:2512.09352*.


=========

analyse Corail bimodality

Dataset: Bleaching and environmental data for global coral reef sites from 1980-2020
DataSet : https://www.bco-dmo.org/dataset/773466#data-files
10.26008/1912/bco-dmo.773466.2

=======
analyse GDSC
https://github.com/rahiuhn/GDSC_datasets/tree/maindatasets/blob/main/sanger-dose-response.zip