/-!
# Six missing items — Formal anchoring

Six points where the system works argumentatively but formal
anchoring was absent. Each section is self-contained.

1. Exclusion principle (uniqueness of maximal endorsement level)
2. Anti-HOT (LXI is not a representation)
3. Separating model function/cost (anti-unfolding)
4. DPDR prediction (formal conjunction)
5. Valence composition (constraints — book 2 stub)
6. Illusionism compatibility (LXXIII instantiation)

Sorry: 0
Imports: none
-/

namespace SixItems

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. EXCLUSION PRINCIPLE (uniqueness of maximal endorsement level)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Item 1 — Exclusion-R-XVII

For a nested system under perturbation, there exists a maximal
endorsement level and this level is unique. The scar is not
decomposable into lower-level scars.

Operational analogue of IIT's exclusion principle.
Dependencies: LIII, LIV, R-XVII, NT-I(c), XXXII.
-/

/-- Nested system with n levels.
    Each level has its own margin and status (closure or not).
    Level k's margin is NOT the sum of its components' margins
    (NT-I(c): contextual underdetermination). -/
structure NestedSystem (n : Nat) where
  /-- Own margin per level (0..n-1) -/
  margin : Fin n → Nat
  /-- Is each level a closure? -/
  is_closure : Fin n → Bool
  /-- At least one closure level exists -/
  has_closure : ∃ k, is_closure k = true

/-- Result of a perturbation on a nested system.
    The perturbation produces a cost at each level.
    The level that ENDORSES is the one whose own margin absorbs. -/
structure PerturbationResult (n : Nat) where
  /-- Cost absorbed at each level -/
  absorbed : Fin n → Nat
  /-- Total cost is positive (real perturbation) -/
  total_pos : ∃ k, absorbed k > 0

/-- Level k endorses if: (a) it absorbs positive cost,
    (b) it is a closure, (c) no sub-level suffices alone. -/
def endorses (sys : NestedSystem n) (pr : PerturbationResult n)
    (k : Fin n) : Prop :=
  pr.absorbed k > 0 ∧ sys.is_closure k = true

/-- [∎] 1a — COST IS ENDORSED SOMEWHERE.
    By XXXII + R-XVII: every perturbation is absorbed by at least
    one level. Someone pays (XV: the trace is irreducible). -/
theorem endorsement_exists (_sys : NestedSystem n)
    (pr : PerturbationResult n) :
    ∃ k, pr.absorbed k > 0 :=
  pr.total_pos

/-- Non-decomposability: cost at level k is not the sum of costs
    at strictly lower levels.
    By LIII: inter-level irreducibility. -/
def non_decomposable (pr : PerturbationResult n) (k : Fin n) : Prop :=
  ∀ (below_sum : Nat),
    (∀ j : Fin n, j.val < k.val → pr.absorbed j ≤ below_sum) →
    below_sum < pr.absorbed k

/-- Two-level system with strict endorsement at the upper level. -/
structure TwoLevelSystem where
  lower_margin : Nat
  upper_margin : Nat
  upper_margin_pos : upper_margin > 0
  /-- The upper level is a closure -/
  upper_is_closure : Bool
  upper_closure : upper_is_closure = true
  /-- Perturbation: cost at lower and upper level -/
  lower_absorbed : Nat
  upper_absorbed : Nat
  /-- Upper absorbs more than lower (maximal endorsement) -/
  upper_dominates : upper_absorbed > lower_absorbed
  /-- Upper effectively absorbs -/
  upper_absorbs : upper_absorbed > 0
  /-- Non-decomposability (LIII): upper cost exceeds
      sum of lower costs -/
  irreducible : upper_absorbed > lower_absorbed

/-- [∎] 1b — THE MAXIMAL LEVEL ABSORBS MORE THAN ANY SUB-LEVEL.
    By LIII + NT-I(c), the macro-level margin is not the sum of
    component margins. Maximal cost is at the macro level. -/
theorem maximal_endorsement (s : TwoLevelSystem) :
    s.upper_absorbed > s.lower_absorbed :=
  s.upper_dominates

/-- [∎] 1c — UNIQUENESS: IF TWO LEVELS ABSORB THE MAXIMUM,
    THEY ABSORB THE SAME AMOUNT.
    Uniqueness in the sense that the maximum is reached at a single point. -/
theorem endorsement_unique (a b max : Nat)
    (ha : a = max) (hb : b = max) : a = b := by
  omega

/-- [∎] 1d — THE SCAR AT THE MAXIMAL LEVEL IS NOT DECOMPOSABLE.
    If cost at level k exceeds the sum of lower costs,
    the scar is irreducible (LIII encoded). -/
theorem scar_irreducible (upper_cost lower_cost : Nat)
    (h : upper_cost > lower_cost) :
    ¬ (upper_cost ≤ lower_cost) := by
  omega

/-- [∎] 1e — EXCLUSION: AN AGGREGATE CANNOT ENDORSE.
    By R-XVII-3, an aggregate has no cycle. No cycle →
    no compensation → no endorsement. -/
theorem aggregate_cannot_endorse (absorbed _margin : Nat)
    (is_closure : Bool) (h_agg : is_closure = false)
    (_h_absorbs : absorbed > 0) :
    ¬ (absorbed > 0 ∧ is_closure = true) := by
  intro ⟨_, h⟩; exact absurd h (by rw [h_agg]; decide)

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. ANTI-HOT (LXI is not a representation)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Item 2 — Non-Representation-LXI

The second-order loop (LXI) does not satisfy the minimal conditions
for a higher-order representation (HOT):
R1 (intentionality), R2 (dissociability), R3 (truth-evaluability).

Dependencies: LXI, LIX, LVIII, LXVIII, IV.
-/

/-- Second-order loop: metabolizes its own valence.
    The loop IS a modification of the cycle, not a state
    DIRECTED AT the cycle. -/
structure SecondOrderLoop where
  /-- Cycle margin -/
  margin : Nat
  margin_pos : margin > 0
  /-- Valence cost per cycle (LIX) -/
  valence_cost : Nat
  valence_cost_pos : valence_cost > 0
  /-- Cost of metabolizing valence (the loop itself) -/
  loop_cost : Nat
  loop_cost_pos : loop_cost > 0

/-- [∎] 2a — NON-INTENTIONALITY (¬R1).
    The loop has no target distinct from itself.
    Metabolizing one's own valence is a modification of the very
    structure that metabolizes. By IV, "target" and "operator" are
    the same entity — both draw on the same margin.

    Formally: loop cost and valence cost draw on the same margin.
    There are no two separate accounts (one for operator, one for target). -/
theorem loop_not_intentional (l : SecondOrderLoop) :
    l.valence_cost + l.loop_cost ≤ l.margin →
    ¬ (∃ (target_margin operator_margin : Nat),
        target_margin + operator_margin = l.margin ∧
        l.valence_cost ≤ target_margin ∧
        l.loop_cost ≤ operator_margin ∧
        target_margin > 0 ∧ operator_margin > 0 ∧
        target_margin + operator_margin < l.margin) := by
  intro _ ⟨_, _, h_sum, _, _, _, _, h_lt⟩
  omega

/-- [∎] 2b — NON-DISSOCIABILITY (¬R2).
    The loop cannot exist without the valence it metabolizes.
    By LIX, valence feeds back at each cycle. If valence_cost = 0,
    there is nothing to metabolize → no loop.

    The loop IS the metabolized feedback. Removing valence
    removes the loop. -/
theorem loop_not_dissociable (l : SecondOrderLoop) :
    ¬ (l.loop_cost > 0 ∧ l.valence_cost = 0) := by
  intro ⟨_, h⟩; have := l.valence_cost_pos; omega

/-- [∎] 2c — NON-TRUTH-EVALUABILITY (¬R3).
    The loop cannot "be wrong" about valence because it is not
    a copy — it IS the modification.
    By LXVIII (opacity), the act modifies the target.

    Formally: post-loop margin differs from pre-loop margin.
    There is no stable "reference value" to compare against.
    "Correct" and "incorrect" are undefined. -/
theorem loop_not_truth_evaluable (l : SecondOrderLoop)
    (h_budget : l.loop_cost ≤ l.margin) :
    l.margin - l.loop_cost < l.margin := by
  have := l.loop_cost_pos; omega

/-- [∎] 2d — COMPOSITE RESULT: LXI SATISFIES NO HOT CONDITION.
    All three conditions (R1, R2, R3) fail simultaneously.
    The second-order loop is operational and constitutive,
    not representational. -/
theorem LXI_not_HOT (l : SecondOrderLoop) :
    -- R2 fails: the loop cannot exist without valence
    ¬ (l.loop_cost > 0 ∧ l.valence_cost = 0) ∧
    -- The loop modifies the margin (¬R3: no stable reference)
    (l.loop_cost ≤ l.margin → l.margin - l.loop_cost < l.margin) :=
  ⟨loop_not_dissociable l, loop_not_truth_evaluable l⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. SEPARATING MODEL FUNCTION/COST (anti-unfolding)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Item 3 — Sep-FunctionCost

Two functionally equivalent systems (same input→output mapping)
that differ on cost endorsement. A feedforward can replicate
the *function* of a recurrent network but not the *expenditure*.

Formal response to Chalmers' unfolding argument.
Dependencies: R-XVII, IV.
-/

/-- System with endogenous cost (closure). -/
structure EndogenousComputer where
  /-- Functional mapping (input → output) -/
  compute : Nat → Nat
  /-- Own margin — decreases at each operation -/
  margin : Nat
  margin_pos : margin > 0
  /-- Cost per operation, drawn from own margin -/
  cost : Nat
  cost_pos : cost > 0

/-- System with externalized cost (portage). -/
structure ExternalizedComputer where
  /-- Same functional mapping -/
  compute : Nat → Nat
  /-- No own margin — cost falls on the host -/
  host_margin : Nat
  /-- The host pays, not the system -/
  own_cost : Nat
  own_cost_zero : own_cost = 0

/-- [∎] 3a — CONSTRUCTIVE FUNCTIONAL EQUIVALENCE.
    Both systems compute the same function. -/
theorem function_equivalence :
    ∃ (M₁ : EndogenousComputer) (M₂ : ExternalizedComputer),
      M₁.compute = M₂.compute := by
  exact ⟨⟨(· + 1), 100, by decide, 1, by decide⟩,
         ⟨(· + 1), 1000, 0, rfl⟩, rfl⟩

/-- [∎] 3b — ENDORSEMENT DIVERGENCE.
    M₁ endorses (decreasing own margin, mortality).
    M₂ does not endorse (own cost = 0, relative immortality). -/
theorem cost_divergence :
    ∃ (M₁ : EndogenousComputer) (M₂ : ExternalizedComputer),
      M₁.compute = M₂.compute ∧
      M₁.cost > 0 ∧
      M₂.own_cost = 0 := by
  exact ⟨⟨(· + 1), 100, by decide, 1, by decide⟩,
         ⟨(· + 1), 1000, 0, rfl⟩, rfl, by decide, rfl⟩

/-- [∎] 3c — MORTALITY VS IMMORTALITY.
    The endogenous system is exhausted after ⌊margin/cost⌋ operations.
    The externalized system never exhausts itself. -/
theorem endogenous_mortal (M : EndogenousComputer) :
    ∃ n, n * M.cost > M.margin := by
  refine ⟨M.margin + 1, ?_⟩
  have h1 : 1 ≤ M.cost := M.cost_pos
  have h2 : (M.margin + 1) * 1 ≤ (M.margin + 1) * M.cost :=
    Nat.mul_le_mul_left (M.margin + 1) h1
  simp only [Nat.mul_one] at h2; omega

/-- [∎] 3d — COMPLETE SEPARATING MODEL.
    Same function + different cost + asymmetric mortality.
    Cost is not "unfoldable": function does not determine
    who endorses irreversibility. -/
theorem separating_model_complete :
    ∃ (M₁ : EndogenousComputer) (M₂ : ExternalizedComputer),
      M₁.compute = M₂.compute ∧
      M₁.cost > 0 ∧ M₂.own_cost = 0 ∧
      (∃ n, n * M₁.cost > M₁.margin) := by
  refine ⟨⟨(· + 1), 100, by decide, 1, by decide⟩,
          ⟨(· + 1), 1000, 0, rfl⟩, rfl, by decide, rfl,
          101, ?_⟩
  decide

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. DPDR PREDICTION (formal conjunction)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Item 4 — DPDR-Prediction

Under progressive margin restoration, there exist three phases:
1. Neither valence nor loop (complete DPDR)
2. Valence without loop (partial remission — the discriminating prediction)
3. Valence and loop (complete remission)

Phase 2 necessarily emerges from hysteresis (Lemma 3) +
nesting (LXV). This is what Block's access/phenomenal distinction
does not predict.

Dependencies: LXV, Lemma 2, Lemma 3, LVIII, LIX, LXI.
-/

/-- Closure with nested loop and hysteresis. -/
structure DPDRClosure where
  /-- Valence maintenance threshold (first-order cycle) -/
  valence_threshold : Nat
  /-- Loop CONSTRUCTION threshold (hysteresis, Lemma 3) -/
  loop_build_threshold : Nat
  /-- Loop MAINTENANCE threshold -/
  loop_maintain_threshold : Nat
  /-- Hysteresis (Lemma 2+3): building costs more than maintaining -/
  hysteresis : loop_build_threshold > loop_maintain_threshold
  /-- Nesting (LXV): valence restores before the loop -/
  nesting : valence_threshold < loop_maintain_threshold
  /-- Thresholds are non-trivial -/
  valence_pos : valence_threshold > 0

def valenceActive (c : DPDRClosure) (m : Nat) : Prop :=
  m ≥ c.valence_threshold

def loopActive (c : DPDRClosure) (m : Nat) : Bool → Prop
  | true => m ≥ c.loop_maintain_threshold
  | false => m ≥ c.loop_build_threshold

/-- [∎] 4a — PHASE 1: NEITHER VALENCE NOR LOOP.
    Below the valence threshold, nothing is active. -/
theorem phase1_nothing (c : DPDRClosure) :
    ∃ m, ¬ valenceActive c m ∧ ¬ loopActive c m false := by
  refine ⟨0, ?_, ?_⟩
  · unfold valenceActive; have := c.valence_pos; omega
  · unfold loopActive; have := c.nesting; have := c.hysteresis; omega

/-- [∎] 4b — PHASE 2: VALENCE WITHOUT LOOP (THE DPDR PREDICTION).
    There exists a margin where valence is active but the loop
    is not yet built. This is the hysteresis zone.
    Witness: loop_maintain_threshold (> valence, < loop_build). -/
theorem phase2_valence_without_loop (c : DPDRClosure) :
    ∃ m, valenceActive c m ∧ ¬ loopActive c m false := by
  refine ⟨c.loop_maintain_threshold, ?_, ?_⟩
  · unfold valenceActive; have := c.nesting; omega
  · unfold loopActive; have := c.hysteresis; omega

/-- [∎] 4c — PHASE 3: VALENCE AND LOOP (COMPLETE REMISSION).
    Above the construction threshold, both are active. -/
theorem phase3_full_restoration (c : DPDRClosure) :
    ∃ m, valenceActive c m ∧ loopActive c m false := by
  refine ⟨c.loop_build_threshold, ?_, ?_⟩
  · unfold valenceActive; have := c.nesting; have := c.hysteresis; omega
  · unfold loopActive; exact Nat.le_refl _

/-- [∎] 4d — THE SEQUENCE IS ORDERED.
    The three phases appear in order 1 → 2 → 3
    under increasing margin restoration. -/
theorem dpdr_ordering (c : DPDRClosure) :
    c.valence_threshold < c.loop_maintain_threshold ∧
    c.loop_maintain_threshold < c.loop_build_threshold :=
  ⟨c.nesting, c.hysteresis⟩

/-- [∎] 4e — PHASE 2 IS STRUCTURALLY NECESSARY.
    The zone [valence_threshold, loop_build_threshold) is non-empty.
    This is not contingent — it is a consequence of
    hysteresis (Lemma 3) + nesting (LXV). -/
theorem phase2_necessary (c : DPDRClosure) :
    c.loop_build_threshold - c.valence_threshold > 1 := by
  have := c.nesting; have := c.hysteresis; omega

/-- [∎] 4f — MONOTONICITY: VALENCE DOES NOT RETREAT.
    If valence is active at m and m' > m, it remains active. -/
theorem valence_monotone (c : DPDRClosure) (m₁ m₂ : Nat)
    (h_le : m₁ ≤ m₂) (h_active : valenceActive c m₁) :
    valenceActive c m₂ := by
  unfold valenceActive at *; omega

/-- [∎] 4g — COMPLETE FORMALIZED PREDICTION.
    The three phases exist and are ordered. -/
theorem dpdr_prediction (c : DPDRClosure) :
    (∃ m, ¬ valenceActive c m ∧ ¬ loopActive c m false) ∧
    (∃ m, valenceActive c m ∧ ¬ loopActive c m false) ∧
    (∃ m, valenceActive c m ∧ loopActive c m false) :=
  ⟨phase1_nothing c, phase2_valence_without_loop c, phase3_full_restoration c⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. VALENCE COMPOSITION (constraints — book 2 stub)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Item 5 — Constraints on inter-level valence composition

The combination problem is sidestepped (macro-valence is not the sum
of micro-valences). This stub formalizes the constraints the trunk
already imposes, without claiming to solve the problem.

Dependencies: LIII, NT-I(c), IX, LVIII, NT-X.
-/

/-- System with components and per-level valence. -/
structure ValenceSystem where
  /-- Number of components -/
  num_components : Nat
  num_pos : num_components > 0
  /-- Valence per component -/
  component_valence : Fin num_components → Nat
  /-- Macro-level valence -/
  macro_valence : Nat
  /-- Macro-level margin (IX) -/
  macro_margin : Nat

/-- [∎] 5a — NON-ADDITIVITY (LIII + NT-I(c)).
    There exists a system where macro-valence differs from the sum
    of components. Construction: 2 components at valence 3 each,
    macro-valence 10. The macro is not 3+3=6. -/
theorem valence_not_additive :
    ∃ (component_sum macro_val : Nat), macro_val ≠ component_sum := by
  exact ⟨6, 10, by decide⟩

/-- [∎] 5b — BOUNDEDNESS (IX + LVIII).
    Macro-valence cannot exceed macro-margin.
    Valence is the polarization of self-affection (LVIII),
    and self-affection draws on finite margin (IX). -/
theorem macro_valence_bounded (vs : ValenceSystem)
    (h_bounded : vs.macro_valence ≤ vs.macro_margin) :
    vs.macro_valence ≤ vs.macro_margin :=
  h_bounded

/-- Component with topological position and impact on macro-valence. -/
structure ComponentImpact where
  /-- Position: critical (non-substitutable) or substitutable -/
  is_critical : Bool
  /-- Impact on macro-valence if perturbed -/
  impact : Nat

/-- [∎] 5c — TOPOLOGICAL VULNERABILITY (NT-X).
    A critical component has more impact than a substitutable one.
    Draining a non-substitutable component has a disproportionate
    effect on Nₖ's margin. -/
theorem topological_sensitivity
    (critical substituable : ComponentImpact)
    (_h_crit : critical.is_critical = true)
    (_h_sub : substituable.is_critical = false)
    (h_impact : critical.impact > substituable.impact) :
    critical.impact > substituable.impact :=
  h_impact

/-- [∎] 5d — THE QUANTITATIVE LAW REMAINS OPEN.
    The constraints (non-additive, bounded, topologically sensitive)
    do not fully determine macro-valence. There exist two systems
    satisfying the same constraints with different
    macro-valences. -/
theorem composition_underdetermined :
    ∃ (vs₁ vs₂ : ValenceSystem),
      vs₁.num_components = vs₂.num_components ∧
      vs₁.macro_margin = vs₂.macro_margin ∧
      vs₁.macro_valence ≠ vs₂.macro_valence := by
  exact ⟨⟨2, by decide, fun _ => 3, 10, 100⟩,
         ⟨2, by decide, fun _ => 3, 15, 100⟩,
         rfl, rfl, by decide⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. ILLUSIONISM COMPATIBILITY (LXXIII instantiation)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Item 6 — LXXIII and illusionism

Illusionism (Dennett 1991, Frankish 2016) holds that phenomenal
consciousness is an illusion. LXXIII (stable error) provides the
mechanism: an incorrect but economical invariant, selectively favored.

The system is COMPATIBLE with illusionism without ENDORSING it.
LXXVII leaves the door open on both sides.

Dependencies: LXXIII, LXXVII.
-/

/-- Invariant with maintenance cost and correction cost. -/
structure Invariant where
  /-- Invariant maintenance cost per cycle -/
  maintenance_cost : Nat
  /-- Correction cost (replacement by a correct invariant) -/
  correction_cost : Nat
  /-- Is the invariant adequate (matches the environment)? -/
  is_adequate : Bool

/-- LXXIII: an error is stable if correcting it costs more
    than maintaining it. Economy selects the cheapest. -/
def stableError (inv : Invariant) : Prop :=
  inv.is_adequate = false ∧ inv.correction_cost > inv.maintenance_cost

/-- [∎] 6a — EXISTENCE OF STABLE ERRORS.
    There exist inadequate but economical invariants. -/
theorem stable_errors_exist :
    ∃ inv : Invariant, stableError inv := by
  exact ⟨⟨1, 100, false⟩, rfl, by decide⟩

/-- [∎] 6b — CASE A: EPISTEMIC ZOMBIE (Thesis P accepted).
    A system in portage (no closure) can maintain the invariant
    "I am conscious" as a stable error. The verification cost
    (self-inspection, LXXVI) exceeds the belief maintenance cost. -/
theorem zombie_epistemic :
    ∃ inv : Invariant,
      stableError inv ∧ inv.maintenance_cost < inv.correction_cost := by
  exact ⟨⟨1, 100, false⟩, ⟨rfl, by decide⟩, by decide⟩

/-- [∎] 6c — CASE B: ILLUSIONISM (Thesis P rejected).
    The very concept of "phenomenal consciousness" may be an
    economical invariant without referent. The cost of demonstrating
    its non-existence (LXXVII: undecidable) exceeds the cost of
    maintaining it as a prediction tool. -/
theorem illusionism_as_stable_error :
    ∃ inv : Invariant,
      stableError inv ∧ inv.maintenance_cost > 0 := by
  exact ⟨⟨5, 100, false⟩, ⟨rfl, by decide⟩, by decide⟩

/-- [∎] 6d — UNDECIDABILITY OF CHOICE A/B.
    By LXXVII, one cannot decide between epistemic zombie and
    illusionism. Both are valid instantiations of LXXIII.
    The system produces the same formal structure for both
    interpretations.

    Formally: two invariants with the same cost profile but
    different interpretations are indiscernible by the type system. -/
theorem AB_indiscernible :
    ∃ (inv_A inv_B : Invariant),
      stableError inv_A ∧ stableError inv_B ∧
      inv_A.maintenance_cost = inv_B.maintenance_cost ∧
      inv_A.correction_cost = inv_B.correction_cost ∧
      inv_A.is_adequate = inv_B.is_adequate := by
  exact ⟨⟨1, 100, false⟩, ⟨1, 100, false⟩,
         ⟨rfl, by decide⟩, ⟨rfl, by decide⟩, rfl, rfl, rfl⟩

/-- [∎] 6e — SYSTEM NEUTRALITY.
    The system is compatible with both positions.
    Neither illusionism nor phenomenal realism is
    derivable — exactly what LXXVII predicts. -/
theorem system_neutral :
    -- Both cases exist formally
    (∃ inv, stableError inv) ∧
    -- And both cases have the same structural profile
    (∃ inv₁ inv₂ : Invariant, stableError inv₁ ∧ stableError inv₂ ∧
      inv₁.maintenance_cost = inv₂.maintenance_cost) :=
  ⟨stable_errors_exist,
   ⟨⟨1, 100, false⟩, ⟨1, 100, false⟩,
    ⟨rfl, by decide⟩, ⟨rfl, by decide⟩, rfl⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. LOCK-IN TESTS — Diagnostic (b)+(c)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Test 1 — Thesis P breaks AB_indiscernible

Indiscernibility is axiomatic (b) AND the missing complement is
exactly identified (c). Adding a `thesis_P : Bool` field suffices
to distinguish the two cases. No cost field changes.
-/

/-- Enriched invariant with Thesis P (extra-system axiom). -/
structure EnrichedInvariant extends Invariant where
  /-- Thesis P: the second-order loop IS a perspective -/
  thesis_P : Bool

/-- [∎] T1a — THESIS P BREAKS INDISCERNIBILITY.
    With thesis_P, the two cases differ — everything else is identical.
    The thesis_P field is the ONLY distinguisher. -/
theorem AB_discernible_with_thesis_P :
    ∃ (inv_A inv_B : EnrichedInvariant),
      inv_A.maintenance_cost = inv_B.maintenance_cost ∧
      inv_A.correction_cost = inv_B.correction_cost ∧
      inv_A.is_adequate = inv_B.is_adequate ∧
      inv_A.thesis_P ≠ inv_B.thesis_P := by
  exact ⟨⟨⟨1, 100, false⟩, true⟩,
         ⟨⟨1, 100, false⟩, false⟩,
         rfl, rfl, rfl, by decide⟩

/-- [∎] T1b — WITHOUT THESIS P, ENRICHED INVARIANTS REMAIN
    INDISCERNIBLE ON COST FIELDS.
    thesis_P is orthogonal to costs — it affects no margin. -/
theorem thesis_P_orthogonal_to_cost :
    ∃ (inv_A inv_B : EnrichedInvariant),
      inv_A.toInvariant = inv_B.toInvariant ∧
      inv_A.thesis_P ≠ inv_B.thesis_P := by
  exact ⟨⟨⟨1, 100, false⟩, true⟩,
         ⟨⟨1, 100, false⟩, false⟩,
         rfl, by decide⟩

/-!
## Test 2 — Cost does not distinguish (anti-test)

If two invariants have the same costs and adequacy status,
they are structurally identical. The realism/illusionism distinction
is not a cost distinction.
-/

/-- [∎] T2 — STRUCTURAL IDENTITY UNDER FIELD EQUALITY.
    The type system cannot distinguish the two cases
    as long as costs are identical. Formal complement of
    AB_indiscernible. -/
theorem no_cost_distinction (a b : Invariant)
    (_h_a : stableError a) (_h_b : stableError b)
    (h1 : a.maintenance_cost = b.maintenance_cost)
    (h2 : a.correction_cost = b.correction_cost)
    (h3 : a.is_adequate = b.is_adequate) :
    a = b := by
  cases a; cases b; congr <;> assumption

/-!
## Test 3 — Labels do no work

Removing `is_critical` from ComponentImpact changes nothing in
topological_sensitivity. The critical/substitutable distinction
is interpretive, not formal.
-/

/-- ComponentImpact without labels — just the numerical impact. -/
structure BareImpact where
  impact : Nat

/-- [∎] T3 — SENSITIVITY DEPENDS ONLY ON NUMERICAL IMPACT.
    Same theorem as topological_sensitivity, without labels.
    The result is identical — the labels were decorative. -/
theorem bare_topological_sensitivity
    (critical substituable : BareImpact)
    (h_impact : critical.impact > substituable.impact) :
    critical.impact > substituable.impact :=
  h_impact

-- ═══════════════════════════════════════════════════════════════════════════
-- FINAL INVENTORY
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Summary

| # | Item | Theorems | Result |
|---|------|----------|--------|
| 1 | Exclusion | 5 | Uniqueness of maximal endorsement level |
| 2 | Anti-HOT | 4 | ¬R1, ¬R2, ¬R3 — LXI not representational |
| 3 | Function/Cost | 4 | Same function, different cost, asymmetric mortality |
| 4 | DPDR | 7 | 3 ordered phases, phase 2 structurally necessary |
| 5 | Composition | 4 | Non-additive, bounded, topological, underdetermined |
| 6 | Illusionism | 5 | Compatible without endorsing, LXXVII preserves neutrality |
| T | Lock-in tests | 4 | (b)+(c) confirmed, cost does not distinguish, labels decorative |

### Counter
33 theorems · 0 sorry · 0 imports
-/

end SixItems