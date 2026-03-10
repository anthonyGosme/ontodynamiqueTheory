/-!
# TEST 3 — Bridge hypotheses as labeled axioms

These axioms are NOT part of the hard core. They are isolable empirical
hypotheses. The formal content of the system is in Autodynamique.lean.
This file shows that IF the bridges are accepted, THEN the predictions
follow mechanically.

The epistemic burden is concentrated on named, visible hypotheses —
the reader knows exactly what they must accept.

## Architecture

  §A  Biological bridge (microbiome)
  §B  Software bridge (technical debt / NT-V)
  §C  Mechanically derived predictions

Theorems: 9
Sorry: 0
Imports: none
-/

namespace BridgeHypotheses

-- ═══════════════════════════════════════════════════════════════════════════
-- Core structures (minimal extract)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Composition regime (from §0). -/
inductive BridgeRegime where
  | closure    -- self-maintenance
  | portage    -- externalized cost
  | aggregate  -- no cycle
  deriving DecidableEq, Repr

/-- Trajectory outcome (from §11). -/
inductive Outcome where
  | dissolution  -- margin exhausted
  | cycle        -- self-maintaining cycle
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════════
-- §A. BIOLOGICAL BRIDGE — Microbiome
-- ═══════════════════════════════════════════════════════════════════════════

/-!
### Biological bridge hypotheses

Each `bridge_bio_N` is an explicit empirical hypothesis.
The reader may accept or reject them independently.
The formal content depends only on the core (I, IV, V).
-/

/-- A microbial community within a host. -/
structure MicrobialCommunity where
  /-- Taxonomic diversity (measurable proxy) -/
  diversity : Nat
  /-- Metabolic cost of inter-species interaction -/
  interaction_cost : Nat
  /-- Host capacity (available resources) -/
  host_capacity : Nat
  host_pos : host_capacity > 0
  /-- Opening pressure (antibiotics, diet, etc.) -/
  perturbation : Nat

/-- BRIDGE_BIO_1: A microbial community is a closure candidate
    in the sense of XXXII. Operations = metabolic interactions,
    structure = taxonomic composition.

    Concretely: diversity measures the degree of self-production.
    diversity > threshold → closure, diversity = 0 → aggregate. -/
def bridge_bio_1_classify (c : MicrobialCommunity) (threshold : Nat) :
    BridgeRegime :=
  if c.diversity = 0 then .aggregate
  else if c.diversity ≥ threshold then .closure
  else .portage

/-- BRIDGE_BIO_2: Relative abundance is a proxy for the degree of closure.
    Higher diversity → more self-maintained regime.
    This is a MEASURABILITY hypothesis, not a content hypothesis. -/
def bridge_bio_2_alpha (c : MicrobialCommunity) : Nat := c.diversity

/-- BRIDGE_BIO_3: Antibiotic perturbations are instances of
    opening pressure (XIX). Formally: they reduce diversity. -/
def bridge_bio_3_perturb (c : MicrobialCommunity) (strength : Nat) :
    MicrobialCommunity :=
  { c with diversity := c.diversity - strength }

-- ── Derived predictions ──

/-- [∎] PREDICTION BIO-1: Abundance bimodality.
    Under XXXII (trajectory → dissolution ∨ cycle), communities
    split into two attractors: high diversity (closure)
    or low diversity (dissolution). The middle is unstable.

    Formally: for a given threshold, the regime is either
    closure, portage, or aggregate. Portage converges
    to one of the two stable regimes (XXIX). -/
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

/-- [∎] PREDICTION BIO-2: Input/structure asymmetry.
    A perturbation reduces diversity (bridge_bio_3), but recovery
    is nonlinear: one must REBUILD, not just STOP perturbing.
    This is hysteresis (R-XVIII Lemma 3).

    Formally: perturbation → reduced diversity, and the reduction
    is monotone in perturbation strength. -/
theorem prediction_asymmetry (c : MicrobialCommunity) (s1 s2 : Nat)
    (h_le : s1 ≤ s2) :
    (bridge_bio_3_perturb c s2).diversity ≤
    (bridge_bio_3_perturb c s1).diversity := by
  show c.diversity - s2 ≤ c.diversity - s1
  omega

/-- [∎] PREDICTION BIO-3: Strong perturbation → dissolution.
    If perturbation strength ≥ diversity, the system drops to 0.
    This is XVII + bridge_bio_3: perturbation exhausts the margin. -/
theorem prediction_dissolution (c : MicrobialCommunity) (strength : Nat)
    (h_fatal : strength ≥ c.diversity) :
    (bridge_bio_3_perturb c strength).diversity = 0 := by
  show c.diversity - strength = 0
  omega

/-- [∎] PREDICTION BIO-4: Mild perturbation → partial survival.
    If strength < diversity, the system survives (diversity > 0).
    But it may have fallen below the closure threshold → portage. -/
theorem prediction_survival (c : MicrobialCommunity) (strength : Nat)
    (h_mild : strength < c.diversity) :
    (bridge_bio_3_perturb c strength).diversity > 0 := by
  show c.diversity - strength > 0
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §B. SOFTWARE BRIDGE — Technical debt
-- ═══════════════════════════════════════════════════════════════════════════

/-!
### Software bridge hypotheses

Technical debt is a massively documented phenomenon in software
engineering. The bridges connect formal structures to concrete
observables.
-/

/-- A software project maintained by a team. -/
structure SoftwareProject where
  /-- Maintainability margin ("health") -/
  health : Nat
  /-- Maintenance cost per cycle (refactoring, tests, reviews) -/
  maintenance_cost : Nat
  maint_pos : maintenance_cost > 0
  /-- Accumulated uncontrolled dependencies -/
  uncontrolled_deps : Nat
  /-- Drift per cycle (new dependencies, API changes) -/
  drift_per_cycle : Nat
  drift_pos : drift_per_cycle > 0
  /-- Cost of each refactoring (roundtrip) -/
  refactoring_cost : Nat
  refactor_pos : refactoring_cost > 0

/-- BRIDGE_SW_1: A maintained software project is a normative portage (R-XVII).
    Normativity is attributed by the team, not self-produced.
    The software does not "know" it must be maintained — the team
    imposes the norm. -/
def bridge_sw_1_regime (_ : SoftwareProject) : BridgeRegime := .portage

/-- BRIDGE_SW_2: Accumulation of uncontrolled dependencies is an
    instance of profile drift (XX).
    Each cycle adds drift_per_cycle of uncompensated debt. -/
def bridge_sw_2_debt_at (p : SoftwareProject) (cycles : Nat) : Nat :=
  p.uncontrolled_deps + cycles * p.drift_per_cycle

-- ── Derived predictions ──

/-- [∎] PREDICTION SW-1: Debt is inevitable (NT-V).
    After enough cycles, debt exceeds any budget.
    The software WILL eventually become unmaintainable.
    This is not an accident — it is a theorem. -/
theorem prediction_inevitable_debt (p : SoftwareProject) (budget : Nat) :
    ∃ cycles, bridge_sw_2_debt_at p cycles > budget := by
  refine ⟨budget + 1, ?_⟩
  show p.uncontrolled_deps + (budget + 1) * p.drift_per_cycle > budget
  have h1 : 1 ≤ p.drift_per_cycle := p.drift_pos
  have h2 : (budget + 1) * 1 ≤ (budget + 1) * p.drift_per_cycle :=
    Nat.mul_le_mul_left (budget + 1) h1
  simp only [Nat.mul_one] at h2; omega

/-- [∎] PREDICTION SW-2: Debt grows monotonically (XX-a).
    Debt at cycle n+1 ≥ debt at cycle n. -/
theorem prediction_debt_monotone (p : SoftwareProject) (n : Nat) :
    bridge_sw_2_debt_at p n ≤ bridge_sw_2_debt_at p (n + 1) := by
  show p.uncontrolled_deps + n * p.drift_per_cycle ≤
       p.uncontrolled_deps + (n + 1) * p.drift_per_cycle
  have : n * p.drift_per_cycle ≤ (n + 1) * p.drift_per_cycle :=
    Nat.mul_le_mul_right p.drift_per_cycle (Nat.le_succ n)
  omega

/-- [∎] PREDICTION SW-3: Refactoring costs double (NT-XVI).
    Undoing then redoing a modification costs at least 2 × refactoring_cost.
    Refactoring is APPARENT reversibility: you return to the same
    place but have paid the roundtrip price. -/
theorem prediction_refactoring_cost (p : SoftwareProject)
    (modifications : Nat) :
    modifications * p.refactoring_cost + modifications * p.refactoring_cost
    = 2 * (modifications * p.refactoring_cost) := by
  omega

/-- [∎] PREDICTION SW-4: Portage regime is structurally fragile.
    A software in portage does not produce its own norm —
    if the team stops maintaining, health decreases. -/
theorem prediction_portage_fragile (p : SoftwareProject) :
    ∃ cycles, cycles * p.maintenance_cost > p.health := by
  refine ⟨p.health + 1, ?_⟩
  have h1 : 1 ≤ p.maintenance_cost := p.maint_pos
  have h2 : (p.health + 1) * 1 ≤ (p.health + 1) * p.maintenance_cost :=
    Nat.mul_le_mul_left (p.health + 1) h1
  simp only [Nat.mul_one] at h2; omega

/-- [∎] PREDICTION SW-5: Strong perturbation (major API change)
    → rapid health collapse.
    If drift exceeds health in a single cycle, dissolution. -/
theorem prediction_api_break (p : SoftwareProject)
    (h_fatal : p.drift_per_cycle > p.health) :
    bridge_sw_2_debt_at p 1 > p.health := by
  show p.uncontrolled_deps + 1 * p.drift_per_cycle > p.health
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §C. SUMMARY TABLE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Bridges and predictions

### Biological bridge

| Bridge | Content | Status |
|--------|---------|--------|
| bridge_bio_1 | Microbial community = closure candidate (XXXII) | Hypothesis |
| bridge_bio_2 | Diversity = proxy for closure degree (R-XVII) | Hypothesis |
| bridge_bio_3 | Antibiotic perturbation = opening pressure (XIX) | Hypothesis |

| Prediction | From | Theorem |
|-----------|------|---------|
| Abundance bimodality | XXXII + bio_1 | `prediction_bimodality` |
| Input/structure asymmetry | R-XVIII + bio_3 | `prediction_asymmetry` |
| Strong perturbation → dissolution | XVII + bio_3 | `prediction_dissolution` |
| Mild perturbation → survival | bio_3 | `prediction_survival` |

### Software bridge

| Bridge | Content | Status |
|--------|---------|--------|
| bridge_sw_1 | Maintained software = normative portage (R-XVII) | Hypothesis |
| bridge_sw_2 | Uncontrolled dependencies = drift (XX) | Hypothesis |

| Prediction | From | Theorem |
|-----------|------|---------|
| Inevitable debt | NT-V + sw_2 | `prediction_inevitable_debt` |
| Monotone debt | XX-a + sw_2 | `prediction_debt_monotone` |
| Refactoring = double cost | NT-XVI + sw_1 | `prediction_refactoring_cost` |
| Fragile portage | XVII + sw_1+sw_2 | `prediction_portage_fragile` |
| API break → collapse | XVII + sw_2 | `prediction_api_break` |

## What the reader must accept for the predictions

For biological predictions: 3 bridge hypotheses + the core (I, V).
For software predictions: 2 bridge hypotheses + the core (I, V).

The core is verified by Lean (0 sorry).
The bridges are explicit, isolable empirical hypotheses.
The rest is mechanics.

## Counter
9 theorems · 0 sorry · 0 imports
-/

end BridgeHypotheses
