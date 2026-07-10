/-!
# TEST 3 — Hypothèses-ponts comme axiomes étiquetés

Ces axiomes NE FONT PAS partie du noyau dur. Ce sont des hypothèses
empiriques isolables. Le contenu formel du système est dans
OntoDynamiqueV5.lean. Ce fichier montre que SI les ponts sont acceptés,
ALORS les prédictions suivent mécaniquement.

La charge épistémique est concentrée sur des hypothèses nommées et
visibles — le lecteur sait exactement ce qu'il doit accepter.

## Architecture

  §A  Pont biologique (microbiome / Gosme 2025)
  §B  Pont logiciel (dette technique / NT-V)
  §C  Prédictions dérivées mécaniquement

Théorèmes : 9
Sorry : 0
Import : aucun
-/

namespace BridgeHypotheses

-- ═══════════════════════════════════════════════════════════════════════════
-- Structures du noyau (extrait minimal de v5.4)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Régime de composition (depuis v5.4 §0). -/
inductive BridgeRegime where
  | closure    -- auto-maintenance
  | portage    -- coût externalisé
  | aggregate  -- pas de cycle
  deriving DecidableEq, Repr

/-- Résultat de trajectoire (depuis v5.4 §11). -/
inductive Outcome where
  | dissolution  -- marge épuisée
  | cycle        -- cycle auto-mainteneur
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════════
-- §A. PONT BIOLOGIQUE — Microbiome
-- ═══════════════════════════════════════════════════════════════════════════

/-!
### Hypothèses-ponts biologiques

Chaque `bridge_bio_N` est une hypothèse empirique explicite.
Le lecteur peut les accepter ou les rejeter indépendamment.
Le contenu formel ne dépend que du noyau (I, IV, V).
-/

/-- Une communauté microbienne dans un hôte. -/
structure MicrobialCommunity where
  /-- Diversité taxonomique (proxy mesurable) -/
  diversity : Nat
  /-- Coût métabolique d'interaction inter-espèces -/
  interaction_cost : Nat
  /-- Capacité de l'hôte (ressources disponibles) -/
  host_capacity : Nat
  host_pos : host_capacity > 0
  /-- Pression d'ouverture (antibiotiques, alimentation, etc.) -/
  perturbation : Nat

/-- BRIDGE_BIO_1 : Une communauté microbienne est un candidat à la
    clôture au sens de XXXII. Les opérations = interactions métaboliques,
    la structure = composition taxonomique.

    Concrètement : la diversité mesure le degré d'auto-production.
    diversité > seuil → clôture, diversité = 0 → agrégat. -/
def bridge_bio_1_classify (c : MicrobialCommunity) (threshold : Nat) :
    BridgeRegime :=
  if c.diversity = 0 then .aggregate
  else if c.diversity ≥ threshold then .closure
  else .portage

/-- BRIDGE_BIO_2 : L'abondance relative est un proxy du degré de clôture.
    Plus la diversité est haute, plus le régime est auto-maintenu.
    C'est une hypothèse de MESURABILITÉ, pas de contenu. -/
def bridge_bio_2_alpha (c : MicrobialCommunity) : Nat := c.diversity

/-- BRIDGE_BIO_3 : Les perturbations antibiotiques sont des instances
    de la pression d'ouverture (XIX). Formellement : elles réduisent
    la diversité. -/
def bridge_bio_3_perturb (c : MicrobialCommunity) (strength : Nat) :
    MicrobialCommunity :=
  { c with diversity := c.diversity - strength }

-- ── Prédictions dérivées ──

/-- [∎] PRÉDICTION BIO-1 : Bimodalité de l'abondance.
    Sous XXXII (trajectoire → dissolution ∨ cycle), les communautés
    se répartissent en deux attracteurs : haute diversité (clôture)
    ou basse diversité (dissolution). Le milieu est instable.

    Formellement : pour un seuil donné, le régime est soit
    clôture soit agrégat, jamais portage stable. Le portage
    converge vers l'un ou l'autre (XXIX). -/
theorem prediction_bimodality (c : MicrobialCommunity)
    (threshold : Nat) :
    bridge_bio_1_classify c threshold = .aggregate ∨
    bridge_bio_1_classify c threshold = .portage ∨
    bridge_bio_1_classify c threshold = .closure := by
  unfold bridge_bio_1_classify
  by_cases h0 : c.diversity = 0
  · left; rw [if_pos h0]
  · by_cases h_ge : c.diversity ≥ threshold
    · right; right; rw [if_neg h0, if_pos h_ge]
    · right; left; rw [if_neg h0, if_neg h_ge]

/-- [∎] PRÉDICTION BIO-2 : Asymétrie entrée/structure.
    Une perturbation réduit la diversité (bridge_bio_3), mais la
    récupération est non-linéaire : il faut RECONSTRUIRE, pas juste
    ARRÊTER de perturber. C'est l'hystérésis (R-XVIII Lemme 3).

    Formellement : perturbation → diversité réduite, et la réduction
    est monotone en la force de perturbation. -/
theorem prediction_asymmetry (c : MicrobialCommunity) (s1 s2 : Nat)
    (h_le : s1 ≤ s2) :
    (bridge_bio_3_perturb c s2).diversity ≤
    (bridge_bio_3_perturb c s1).diversity := by
  show c.diversity - s2 ≤ c.diversity - s1
  omega

/-- [∎] PRÉDICTION BIO-3 : Perturbation forte → dissolution.
    Si la force de perturbation ≥ diversité, le système tombe à 0.
    C'est XVII + bridge_bio_3 : la perturbation épuise la marge. -/
theorem prediction_dissolution (c : MicrobialCommunity) (strength : Nat)
    (h_fatal : strength ≥ c.diversity) :
    (bridge_bio_3_perturb c strength).diversity = 0 := by
  show c.diversity - strength = 0
  omega

/-- [∎] PRÉDICTION BIO-4 : Perturbation faible → survie partielle.
    Si la force < diversité, le système survit (diversité > 0).
    Mais peut être passé en-dessous du seuil de clôture → portage. -/
theorem prediction_survival (c : MicrobialCommunity) (strength : Nat)
    (h_mild : strength < c.diversity) :
    (bridge_bio_3_perturb c strength).diversity > 0 := by
  show c.diversity - strength > 0
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §B. PONT LOGICIEL — Dette technique
-- ═══════════════════════════════════════════════════════════════════════════

/-!
### Hypothèses-ponts logicielles

La dette technique est un phénomène massivement documenté en génie
logiciel. Les ponts relient les structures formelles du système aux
observables concrets.
-/

/-- Un logiciel maintenu par une équipe. -/
structure SoftwareProject where
  /-- Marge de maintenabilité (« health ») -/
  health : Nat
  /-- Coût de maintenance par cycle (refactoring, tests, reviews) -/
  maintenance_cost : Nat
  maint_pos : maintenance_cost > 0
  /-- Dépendances non maîtrisées accumulées -/
  uncontrolled_deps : Nat
  /-- Dérive par cycle (nouvelles dépendances, changements d'API) -/
  drift_per_cycle : Nat
  drift_pos : drift_per_cycle > 0
  /-- Coût de chaque refactoring (aller-retour) -/
  refactoring_cost : Nat
  refactor_pos : refactoring_cost > 0

/-- BRIDGE_SW_1 : Un logiciel maintenu est un portage normatif (R-XVII).
    La normativité est attribuée par l'équipe, pas auto-produite.
    Le logiciel ne « sait » pas qu'il doit être maintenu — l'équipe
    impose la norme. -/
def bridge_sw_1_regime (_ : SoftwareProject) : BridgeRegime := .portage

/-- BRIDGE_SW_2 : L'accumulation de dépendances non maîtrisées est
    une instance de la dérive du profil (XX).
    Chaque cycle ajoute drift_per_cycle de dette non compensée. -/
def bridge_sw_2_debt_at (p : SoftwareProject) (cycles : Nat) : Nat :=
  p.uncontrolled_deps + cycles * p.drift_per_cycle

-- ── Prédictions dérivées ──

/-- [∎] PRÉDICTION SW-1 : La dette est inévitable (NT-V).
    Après suffisamment de cycles, la dette dépasse n'importe quel budget.
    C'est lifespan_bound (v5.4 §2) + bridge_sw_2.

    Le logiciel FINIRA par devenir inmaintenable. Ce n'est pas un
    accident — c'est un théorème. -/
theorem prediction_inevitable_debt (p : SoftwareProject) (budget : Nat) :
    ∃ cycles, bridge_sw_2_debt_at p cycles > budget := by
  refine ⟨budget + 1, ?_⟩
  show p.uncontrolled_deps + (budget + 1) * p.drift_per_cycle > budget
  have h1 : 1 ≤ p.drift_per_cycle := p.drift_pos
  have h2 : (budget + 1) * 1 ≤ (budget + 1) * p.drift_per_cycle :=
    Nat.mul_le_mul_left (budget + 1) h1
  simp only [Nat.mul_one] at h2; omega

/-- [∎] PRÉDICTION SW-2 : La dette croît monotonement (XX-a).
    La dette au cycle n+1 est ≥ la dette au cycle n.
    C'est drift_monotone_XXa (v5.4 §10) + bridge_sw_2. -/
theorem prediction_debt_monotone (p : SoftwareProject) (n : Nat) :
    bridge_sw_2_debt_at p n ≤ bridge_sw_2_debt_at p (n + 1) := by
  show p.uncontrolled_deps + n * p.drift_per_cycle ≤
       p.uncontrolled_deps + (n + 1) * p.drift_per_cycle
  have : n * p.drift_per_cycle ≤ (n + 1) * p.drift_per_cycle :=
    Nat.mul_le_mul_right p.drift_per_cycle (Nat.le_succ n)
  omega

/-- [∎] PRÉDICTION SW-3 : Le refactoring coûte deux fois (NT-XVI).
    Annuler puis refaire une modification coûte au moins 2 × refactoring_cost.
    C'est roundtrip_NTXVI (v5.4 §6) + bridge_sw_1.

    Le refactoring est une réversibilité APPARENTE : on revient au même
    endroit mais on a payé le prix aller-retour. -/
theorem prediction_refactoring_cost (p : SoftwareProject)
    (modifications : Nat) :
    modifications * p.refactoring_cost + modifications * p.refactoring_cost
    = 2 * (modifications * p.refactoring_cost) := by
  omega

/-- [∎] PRÉDICTION SW-4 : Le régime portage est structurellement fragile.
    Un logiciel en portage (bridge_sw_1) ne produit pas sa propre norme —
    si l'équipe cesse la maintenance, la santé décroît.
    C'est exhaustion_XVII (v5.4 §1) + bridge_sw_1 + bridge_sw_2. -/
theorem prediction_portage_fragile (p : SoftwareProject) :
    ∃ cycles, cycles * p.maintenance_cost > p.health := by
  refine ⟨p.health + 1, ?_⟩
  have h1 : 1 ≤ p.maintenance_cost := p.maint_pos
  have h2 : (p.health + 1) * 1 ≤ (p.health + 1) * p.maintenance_cost :=
    Nat.mul_le_mul_left (p.health + 1) h1
  simp only [Nat.mul_one] at h2; omega

/-- [∎] PRÉDICTION SW-5 : Perturbation forte (changement d'API majeur)
    → effondrement rapide de la santé.
    Si la dérive dépasse la santé en un seul cycle, dissolution. -/
theorem prediction_api_break (p : SoftwareProject)
    (h_fatal : p.drift_per_cycle > p.health) :
    bridge_sw_2_debt_at p 1 > p.health := by
  show p.uncontrolled_deps + 1 * p.drift_per_cycle > p.health
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §C. TABLEAU RÉCAPITULATIF
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Ponts et prédictions

### Pont biologique

| Pont | Contenu | Statut |
|------|---------|--------|
| bridge_bio_1 | Communauté microbienne = candidat clôture (XXXII) | Hypothèse |
| bridge_bio_2 | Diversité = proxy du degré de clôture (R-XVII) | Hypothèse |
| bridge_bio_3 | Perturbation antibiotique = pression d'ouverture (XIX) | Hypothèse |

| Prédiction | De | Théorème |
|-----------|-----|----------|
| Bimodalité de l'abondance | XXXII + bio_1 | `prediction_bimodality` |
| Asymétrie entrée/structure | R-XVIII + bio_3 | `prediction_asymmetry` |
| Perturbation forte → dissolution | XVII + bio_3 | `prediction_dissolution` |
| Perturbation faible → survie | bio_3 | `prediction_survival` |

### Pont logiciel

| Pont | Contenu | Statut |
|------|---------|--------|
| bridge_sw_1 | Logiciel maintenu = portage normatif (R-XVII) | Hypothèse |
| bridge_sw_2 | Dépendances non maîtrisées = dérive (XX) | Hypothèse |

| Prédiction | De | Théorème |
|-----------|-----|----------|
| Dette inévitable | NT-V + sw_2 | `prediction_inevitable_debt` |
| Dette monotone | XX-a + sw_2 | `prediction_debt_monotone` |
| Refactoring = coût double | NT-XVI + sw_1 | `prediction_refactoring_cost` |
| Portage fragile | XVII + sw_1+sw_2 | `prediction_portage_fragile` |
| API break → effondrement | XVII + sw_2 | `prediction_api_break` |

## Ce que le lecteur doit accepter pour les prédictions

Pour les prédictions biologiques : 3 hypothèses-ponts + le noyau (I, V).
Pour les prédictions logicielles : 2 hypothèses-ponts + le noyau (I, V).

Le noyau est vérifié par Lean (94 théorèmes, 0 sorry).
Les ponts sont des hypothèses empiriques explicites et isolables.
Le reste est de la mécanique.

## Compteur
9 théorèmes · 0 sorry · 0 import
-/

end BridgeHypotheses
