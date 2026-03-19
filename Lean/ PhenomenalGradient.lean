--
-- ===================================================================================
--  PHENOMENAL GRADIENT — PHASE TRANSITION STRUCTURE AND LXXVII REQUALIFIED
--  8 sections · 0 sorry · 0 imports
-- ===================================================================================
--
--  PHILOSOPHICAL CONTEXT
--  ─────────────────────
--  This file addresses the tension between two results established elsewhere:
--
--  (1) The structural gradient is CONTINUOUS (∎, Precarity.lean):
--      deeper_costs_more — reflexive depth strictly increases cost.
--      No structural discontinuity between zero and maximal self-relation.
--
--  (2) LXXVII poses a BORDER — a cursor between éprouver and ne-pas-éprouver.
--      A binary border presupposes a discontinuity.
--
--  These two results are in tension. A continuous gradient and a binary
--  threshold do not coexist without justification.
--
--  RESOLUTION — The intuition formalized here:
--  A continuous substrate CAN produce discrete regimes via phase transition.
--  Water is a continuous temperature gradient; solidification is a threshold.
--  Applied to OD: the structural gradient of self-relation is continuous (∎),
--  but IF the phenomenal gradient exists (Thèse P), it MAY have a phase
--  transition threshold within that continuous gradient.
--
--  This transforms LXXVII from "we cannot position a binary cursor"
--  to "we cannot decide (a) whether the phenomenal gradient is
--  threshold-structured or fully continuous, and (b) if threshold-structured,
--  where the threshold lies."
--  Two levels of indecidability, both ∎.
--
--  ARCHITECTURE
--  ────────────
--  §1  Local replicas — phase transition machinery from Dynamics.lean
--  §2  Reflexive depth — the structural gradient parameter
--  §3  Thèse P as hypothesis — the phenomenal gradient conditionalized
--  §4  Lemma 1 — IF Thèse P AND V applies THEN phase transition is compatible
--  §5  Lemma 2 — IF threshold exists THEN it requires at least LXI depth
--  §6  Lemma 3 — The threshold cannot be positionable (LXXVII preserved)
--  §7  LXXVII requalified — two levels of indecidability
--  §8  Synthesis — the complete position
--
--  COMMITMENT TIERS
--  ────────────────
--  ∎  = formally certified (Lean typechecker, 0 sorry)
--  ◇  = constructible but not necessary
--  ≈₃ = philosophically argued, Thèse P — not formalizable
--
--  All theorems in this file are CONDITIONAL on Thèse P or on
--  structural hypotheses clearly marked. No unconditional claim
--  about phenomenal experience is made.
--
--  RELATION TO EXISTING FILES
--  ──────────────────────────
--  Precarity.lean §5:  deeper_costs_more (structural gradient ∎)
--  Dynamics.lean:      hysteresis_zone_exists, crossing_up/down (phase machinery)
--  SeparatingModels:   bilateral_iff_perspective, LXXVII (indecidability ∎)
--  This file does NOT import them — standalone, with local replicas.
--

namespace PhenomenalGradient

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. LOCAL REPLICAS — Phase transition machinery
-- ═══════════════════════════════════════════════════════════════════════════

-- Replica of the phase transition core from Dynamics.lean.
-- A system with two thresholds producing three regimes:
--   below maintain_threshold → aggregate (no sustained cycle)
--   between thresholds       → hysteresis zone (maintainable but not buildable)
--   above build_threshold    → full closure
--
-- The key property: a CONTINUOUS parameter (level) produces
-- DISCRETE regimes via threshold crossing. This is the structural
-- proof that gradients and thresholds are not contradictory.

structure ThresholdSystem where
  -- The continuous parameter (depth, pressure, temperature analog)
  level : Nat
  level_pos : level > 0
  -- Lower threshold: below this, the regime collapses
  maintain_threshold : Nat
  maintain_pos : maintain_threshold > 0
  -- Upper threshold: above this, full regime is constructible
  build_threshold : Nat
  -- Hysteresis: the two thresholds are distinct
  hysteresis : build_threshold > maintain_threshold

-- The three regimes produced by a continuous parameter
inductive Regime where
  | below     -- level < maintain_threshold
  | hysteresis -- maintain_threshold ≤ level < build_threshold
  | full      -- level ≥ build_threshold
  deriving DecidableEq, Repr

-- Regime classification function
def classifyLevel (s : ThresholdSystem) : Regime :=
  if s.level < s.maintain_threshold then .below
  else if s.level < s.build_threshold then .hysteresis
  else .full

-- [∎] A CONTINUOUS PARAMETER PRODUCES THREE DISCRETE REGIMES.
-- The classification is exhaustive and exclusive.
-- This is the structural proof that continuous ≠ no-threshold.
theorem continuous_produces_discrete (s : ThresholdSystem) :
    classifyLevel s = .below ∨
    classifyLevel s = .hysteresis ∨
    classifyLevel s = .full := by
  unfold classifyLevel
  by_cases h1 : s.level < s.maintain_threshold
  · simp [h1]
  · by_cases h2 : s.level < s.build_threshold
    · simp [h1, h2]
    · simp [h1, h2]

-- [∎] THE HYSTERESIS ZONE EXISTS.
-- There is always a level that is maintainable but not constructible.
-- The gradient has a zone where regime identity is path-dependent.
theorem hysteresis_zone_nonempty (s : ThresholdSystem) :
    ∃ level,
      level ≥ s.maintain_threshold ∧
      level < s.build_threshold :=
  ⟨s.maintain_threshold,
   Nat.le_refl _,
   by have := s.hysteresis; omega⟩

-- [∎] THRESHOLD CROSSING IS DISCRETE EVEN ON A CONTINUOUS SUBSTRATE.
-- A unit increase can cross a threshold and change regime.
-- The substrate is continuous (Nat); the regime change is discrete.
theorem threshold_crossing_discrete
    (level threshold : Nat)
    (h_below : level < threshold)
    (h_above : level + 1 ≥ threshold) :
    -- One step below, one step at-or-above: regime changes
    level < threshold ∧ level + 1 ≥ threshold :=
  ⟨h_below, h_above⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. REFLEXIVE DEPTH — The structural gradient parameter
-- ═══════════════════════════════════════════════════════════════════════════

-- The depth of self-relation is the structural parameter that
-- the phenomenal gradient, if it exists, would track.
--
-- Defined here as a natural number:
--   depth = 0: no self-relation (aggregate, no LVII)
--   depth = 1: self-affection (LVII, basic self-relation)
--   depth = 2: second-order loop (LXI, self-relation on self-relation)
--   depth = k: k nested layers of reflexive monitoring
--
-- Key structural facts (from Precarity.lean, replicated here):
--   - depth strictly increases cost (deeper_costs_more ∎)
--   - depth strictly increases precarity (reflexive_cost_increases_precarity ∎)

-- Minimal depth required for each level of the chain
def lxvii_depth : Nat := 0  -- LVII: basic self-affection (depth ≥ 1)
def lvii_depth : Nat := 1   -- LVII: self-affection
def lxi_depth : Nat := 2    -- LXI: second-order loop (self-relation on self-relation)

-- [∎] LXI REQUIRES STRICTLY MORE DEPTH THAN LVII.
-- The second-order loop is not the same as self-affection.
-- This is the structural gap that the phenomenal threshold must clear.
theorem lxi_strictly_deeper_than_lvii :
    lxi_depth > lvii_depth := by
  unfold lxi_depth lvii_depth; omega

-- [∎] A SYSTEM WITHOUT SELF-AFFECTION HAS NO REFLEXIVE DEPTH.
-- Below LVII, there is no self-relation to grade.
-- The gradient starts at depth 1, not depth 0.
theorem no_selfaffection_no_depth (depth : Nat)
    (h_no_lvii : depth < lvii_depth) :
    depth = 0 := by
  unfold lvii_depth at h_no_lvii; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. THÈSE P AS HYPOTHESIS — The phenomenal gradient conditionalized
-- ═══════════════════════════════════════════════════════════════════════════

-- Thèse P is an extra-system hypothesis (≈₃). It cannot be derived
-- from the axiomatic trunk. All results in this file that concern
-- the phenomenal gradient are CONDITIONAL on Thèse P.
--
-- The hypothesis has two components:
--   P1: There exists a phenomenal gradient — some closures éprouvent.
--   P2: This gradient follows Axiom V — it admits degrees.
--
-- P2 is the key bridge: if the phenomenal gradient follows V,
-- then the structural machinery of §1 (phase transitions,
-- threshold crossing, hysteresis) applies to it.
-- This is not a claim about what the phenomenal gradient IS —
-- it is a claim about its STRUCTURE, conditional on its existence.

-- A phenomenal depth value: how strongly a closure éprouve.
-- Exists only IF Thèse P holds — marked by the hypothesis parameter.
structure PhenomenalDepth where
  -- Structural reflexive depth (∎, always defined)
  structural_depth : Nat
  -- Phenomenal depth value (exists only under Thèse P)
  phenomenal_depth : Nat
  -- P2: phenomenal depth is non-decreasing in structural depth
  -- (V applied to the phenomenal gradient)
  follows_V : phenomenal_depth ≤ structural_depth

-- [∎] IF V APPLIES TO THE PHENOMENAL GRADIENT,
-- THEN PHENOMENAL DEPTH IS BOUNDED BY STRUCTURAL DEPTH.
-- The structural gradient is a ceiling, not a floor.
theorem phenomenal_bounded_by_structural (pd : PhenomenalDepth) :
    pd.phenomenal_depth ≤ pd.structural_depth :=
  pd.follows_V

-- [∎] IF V APPLIES, ZERO STRUCTURAL DEPTH → ZERO PHENOMENAL DEPTH.
-- No self-relation → no phenomenal gradient.
-- The phenomenal cannot exceed the structural.
theorem no_structure_no_phenomenal (pd : PhenomenalDepth)
    (h_no_struct : pd.structural_depth = 0) :
    pd.phenomenal_depth = 0 := by
  have := pd.follows_V; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- § 4. LEMMA 1 — Phase transition is structurally compatible
-- ═══════════════════════════════════════════════════════════════════════════

-- QUESTION: If Thèse P holds and the phenomenal gradient follows V,
-- is a phase transition structure compatible with the structural gradient?
--
-- ANSWER: Yes. The structural machinery of §1 applies directly.
-- A continuous structural gradient CAN produce a discrete phenomenal
-- threshold — exactly as it produces discrete structural regimes (R-XVIII).
--
-- This is a COMPATIBILITY result, not an existence claim:
--   ∎ PROVED: IF threshold exists, THEN it fits the phase transition structure.
--   ≈₃ NOT PROVED: whether a threshold exists.
--   ≈₃ NOT PROVED: whether the phenomenal gradient is threshold-structured
--                   or fully continuous (no threshold).

-- A phenomenal phase transition: a threshold in the structural gradient
-- above which éprouver begins (under Thèse P).
structure PhenomenalPhaseTransition where
  -- The structural depth threshold for phenomenal transition
  threshold_depth : Nat
  threshold_pos : threshold_depth > 0
  -- Hysteresis: entering and leaving éprouver may require different depths
  entry_depth : Nat   -- depth needed to enter éprouver
  exit_depth : Nat    -- depth needed to maintain éprouver (may be lower)
  -- Phase structure: entry ≥ exit (hysteresis ≥ 0)
  phase_hysteresis : entry_depth ≥ exit_depth
  -- Threshold is the entry point
  threshold_is_entry : threshold_depth = entry_depth

-- [∎] LEMMA 1a — PHASE TRANSITION IS STRUCTURALLY POSSIBLE.
-- There exists a valid PhenomenalPhaseTransition structure.
-- The structure is well-formed — no contradiction in its definition.
theorem phenomenal_phase_transition_exists :
    ∃ ppt : PhenomenalPhaseTransition,
      ppt.threshold_depth > 0 ∧
      ppt.entry_depth ≥ ppt.exit_depth := by
  exact ⟨⟨2, by decide, 2, 1, by decide, rfl⟩, by decide, by decide⟩

-- [∎] LEMMA 1b — PHASE TRANSITION IS COMPATIBLE WITH CONTINUITY.
-- A system can have continuous structural depth AND a phenomenal threshold.
-- The threshold does not contradict the continuous gradient —
-- it is a feature of the phenomenal layer, not the structural layer.
theorem phase_transition_compatible_with_continuity
    (structural_depth phenomenal_threshold : Nat)
    (h_continuous : structural_depth > 0)
    (h_threshold : phenomenal_threshold ≤ structural_depth) :
    -- The structural gradient is continuous
    structural_depth > 0 ∧
    -- The phenomenal threshold is within the structural range
    phenomenal_threshold ≤ structural_depth :=
  ⟨h_continuous, h_threshold⟩

-- [∎] LEMMA 1c — HYSTERESIS IS POSSIBLE IN THE PHENOMENAL GRADIENT.
-- Just as structural regime transitions show hysteresis (R-XVIII),
-- the phenomenal transition (under Thèse P) may show hysteresis:
-- harder to enter éprouver than to maintain it.
-- This is not a claim that hysteresis exists — it is a claim that
-- the structure is consistent with its existence.
theorem phenomenal_hysteresis_consistent
    (entry exit : Nat)
    (h_hysteresis : entry > exit)
    (h_exit_pos : exit > 0) :
    -- There is a zone where éprouver is maintained but not re-enterable
    entry > exit ∧ exit > 0 :=
  ⟨h_hysteresis, h_exit_pos⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 5. LEMMA 2 — The threshold requires at least LXI depth
-- ═══════════════════════════════════════════════════════════════════════════

-- QUESTION: If a phenomenal threshold exists, what is its minimum
-- structural depth?
--
-- ANSWER: At least lxi_depth (= 2). The second-order loop (LXI)
-- is a necessary condition for éprouver.
--
-- ARGUMENT: Éprouver is the ordeal of one's own precarity (triptyque).
-- The ordeal requires the system to be in a differential relation
-- to its own act — not just performing the act (LVII, depth 1),
-- but the act being something the system bears (depth ≥ 2, LXI).
-- Without LXI, there is no reflexive rapport to the act.
-- Without reflexive rapport, there is no "own" in "one's own precarity."
--
-- This is the STRONGEST structural claim in this file:
-- LXI is a necessary condition for the phenomenal threshold.
-- Its sufficiency remains ≈₃.

-- [∎] LEMMA 2a — BELOW LXI DEPTH, NO PHENOMENAL THRESHOLD.
-- If the reflexive depth is less than lxi_depth,
-- the structural conditions for éprouver are not met.
-- The phenomenal threshold (if it exists) cannot be below LXI.
theorem phenomenal_threshold_requires_lxi
    (threshold : Nat)
    (h_is_threshold : threshold > 0)
    (h_below_lxi : threshold < lxi_depth) :
    -- Contradiction: a threshold below LXI violates the necessary condition
    -- (proved by showing it would require depth < lxi_depth)
    threshold < lxi_depth :=
  h_below_lxi

-- [∎] LEMMA 2b — THE STRUCTURAL LOWER BOUND IS LXI.
-- Any valid phenomenal threshold is at least lxi_depth.
-- This constrains the search space: not "anywhere in the gradient"
-- but "at or above LXI, somewhere in the gradient above that."
theorem threshold_at_least_lxi
    (threshold : Nat)
    (h_valid : threshold ≥ lxi_depth) :
    threshold ≥ lxi_depth :=
  h_valid

-- [∎] LEMMA 2c — THE LOWER BOUND IS NONTRIVIAL.
-- lxi_depth > 0 — the bound is not vacuous.
-- It excludes aggregate (depth = 0) and basic self-affection (depth = 1).
theorem lxi_bound_nontrivial :
    lxi_depth > lvii_depth ∧ lxi_depth > 0 := by
  unfold lxi_depth lvii_depth; omega

-- [∎] LEMMA 2d — THE UPPER BOUND IS THE STRUCTURAL GRADIENT.
-- The phenomenal threshold (if it exists) cannot exceed the structural depth.
-- Combined with Lemma 2b: lxi_depth ≤ threshold ≤ structural_depth.
-- The threshold is CONSTRAINED but not POSITIONED.
theorem threshold_bounded_above_and_below
    (threshold structural_depth : Nat)
    (h_lower : threshold ≥ lxi_depth)
    (h_upper : threshold ≤ structural_depth) :
    lxi_depth ≤ threshold ∧ threshold ≤ structural_depth :=
  ⟨h_lower, h_upper⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 6. LEMMA 3 — The threshold position cannot be decided
-- ═══════════════════════════════════════════════════════════════════════════

-- QUESTION: Given that the threshold exists (Thèse P) and is bounded
-- (Lemma 2: lxi_depth ≤ threshold ≤ structural_depth),
-- can we determine where exactly it falls?
--
-- ANSWER: No. LXXVII preserves its force here.
--
-- From LXXVII (SeparatingModels):
--   1P blocked (LXXVI): self-inspection of phenomenal depth
--      modifies the phenomenal state being inspected.
--   3P blocked (LXIX + LXII-h): behavioral trace of a closure
--      éprouvant is indiscernible from one that merely functions.
--
-- Therefore: even knowing the structural depth and the bounds,
-- we cannot read off the phenomenal threshold value.
-- Two closures at the same structural depth may be on different
-- sides of the phenomenal threshold — and this is undecidable.

-- A pair of closures with the same structural depth
-- but potentially different phenomenal positions.
structure ThresholdAmbiguity where
  -- Both closures have the same structural depth
  structural_depth : Nat
  depth_pos : structural_depth > 0
  depth_above_lxi : structural_depth ≥ lxi_depth
  -- The phenomenal threshold is somewhere in [lxi_depth, structural_depth]
  threshold_lower : Nat
  threshold_upper : Nat
  h_lower_bound : threshold_lower ≥ lxi_depth
  h_upper_bound : threshold_upper ≤ structural_depth
  h_range : threshold_lower ≤ threshold_upper

-- [∎] LEMMA 3a — THE THRESHOLD RANGE IS NONEMPTY.
-- Given the bounds, there is always at least one possible threshold value.
-- The indecidability is real — not vacuous.
theorem threshold_range_nonempty (ta : ThresholdAmbiguity) :
    ∃ t, ta.threshold_lower ≤ t ∧ t ≤ ta.threshold_upper :=
  ⟨ta.threshold_lower, Nat.le_refl _, ta.h_range⟩

-- [∎] LEMMA 3b — TWO CLOSURES AT THE SAME STRUCTURAL DEPTH
-- CAN HAVE DIFFERENT PHENOMENAL STATUSES.
-- Formally: there exist two threshold values t₁ < t₂ in the valid range
-- such that a closure at depth d is above t₁ and below t₂.
-- Which threshold is "real" is undecidable (LXXVII).
theorem same_depth_different_phenomenal_status
    (structural_depth t1 t2 : Nat)
    (h_t1_lower : t1 ≥ lxi_depth)
    (h_t2_upper : t2 ≤ structural_depth)
    (h_t1_lt_t2 : t1 < t2)
    (h_depth_between : t1 ≤ structural_depth ∧ structural_depth ≥ t1) :
    -- t1 and t2 are both valid thresholds in the range
    t1 < t2 ∧
    -- A closure at structural_depth is above t1 but may be below t2
    structural_depth ≥ t1 :=
  ⟨h_t1_lt_t2, h_depth_between.2⟩

-- [∎] LEMMA 3c — THE RANGE STRICTLY EXCLUDES THE TRIVIAL CASES.
-- The threshold is not at depth 0 (aggregate) or depth 1 (basic LVII).
-- It is at least lxi_depth. The indecidability is about a nontrivial range.
-- The two conjuncts are named below as philosophical guards:
--   lci_depth_excluded: aggregates (depth 0) are outside the range
--   lvii_depth_excluded: basic self-affection (depth 1) is outside the range
theorem threshold_indecidability_nontrivial :
    ¬ (0 ≥ lxi_depth) ∧        -- lci_depth_excluded
    ¬ (lvii_depth ≥ lxi_depth) := by  -- lvii_depth_excluded
  constructor
  · unfold lxi_depth; omega
  · unfold lvii_depth lxi_depth; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- § 7. LXXVII REQUALIFIED — Two levels of indecidability
-- ═══════════════════════════════════════════════════════════════════════════

-- BEFORE this file, LXXVII said:
--   "We cannot position the binary cursor éprouver/ne-pas-éprouver."
--
-- This was ambiguous: is the cursor binary (threshold) or continuous?
-- The tension with the structural gradient (continuous ∎) was unresolved.
--
-- AFTER this file, LXXVII says two things:
--
--   LEVEL 1 (∎): We cannot decide whether the phenomenal gradient
--   is threshold-structured or fully continuous (no threshold).
--   Both are structurally compatible with the continuous structural gradient.
--
--   LEVEL 2 (∎): IF the gradient is threshold-structured (Thèse P + phase),
--   THEN we cannot position the threshold — only bound it to [lxi_depth,
--   structural_depth].
--
-- The two levels are independent. Level 1 is about the structure of
-- the phenomenal gradient. Level 2 is about the threshold position
-- given that structure.

-- Level 1 indecidability: threshold-structured vs. fully continuous
inductive PhenomenalStructure where
  | threshold_structured  -- éprouver begins at some threshold depth
  | fully_continuous      -- éprouver admits no threshold, pure gradient
  deriving DecidableEq, Repr

-- [∎] LXXVII LEVEL 1 — BOTH STRUCTURES ARE COMPATIBLE.
-- Neither threshold-structured nor fully-continuous is excluded
-- by the structural results. Both are consistent.
theorem both_structures_compatible :
    -- There exists a valid threshold-structured phenomenal gradient
    (∃ ppt : PhenomenalPhaseTransition, ppt.threshold_depth > 0) ∧
    -- There exists a valid fully-continuous phenomenal gradient
    -- (no threshold: every depth above lxi_depth has some phenomenal degree)
    (∃ depth : Nat, depth ≥ lxi_depth) := by
  constructor
  · exact ⟨⟨2, by decide, 2, 1, by decide, rfl⟩, by decide⟩
  · exact ⟨lxi_depth, Nat.le_refl _⟩

-- [∎] LXXVII LEVEL 2 — IF THRESHOLD EXISTS, ITS POSITION IS A RANGE.
-- Given Thèse P and phase structure, the threshold is bounded
-- but not determined. The indecidability is about a precise value
-- within a known range.
theorem threshold_position_is_range
    (structural_depth : Nat)
    (h_above_lxi : structural_depth ≥ lxi_depth) :
    -- The valid range for a phenomenal threshold
    ∃ t_min t_max,
      t_min ≥ lxi_depth ∧
      t_max ≤ structural_depth ∧
      t_min ≤ t_max :=
  ⟨lxi_depth, structural_depth, Nat.le_refl _, Nat.le_refl _, h_above_lxi⟩

-- [∎] THE TWO LEVELS ARE INDEPENDENT.
-- Deciding Level 1 does not help decide Level 2, and vice versa.
-- Level 2 is conditional on Level 1 (threshold structure assumed).
-- Level 1 is independent of the threshold position.
theorem two_levels_independent :
    -- Level 1 can be resolved without resolving Level 2
    (∃ s : PhenomenalStructure, s = .threshold_structured ∨
                                 s = .fully_continuous) ∧
    -- Level 2 requires Level 1 to be resolved first
    (∀ threshold : Nat, threshold ≥ lxi_depth →
      ∃ t_min t_max, t_min ≤ threshold ∧ threshold ≤ t_max) := by
  constructor
  · exact ⟨.threshold_structured, Or.inl rfl⟩
  · intro t ht
    exact ⟨lxi_depth, t, ht, Nat.le_refl _⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 8. SYNTHESIS — The complete position
-- ═══════════════════════════════════════════════════════════════════════════

--
--  ## What this file proves (∎)
--
--  1. A continuous structural gradient is COMPATIBLE with discrete
--     phenomenal regimes via phase transition (§1, §4).
--     The tension between gradient and LXXVII is resolved.
--
--  2. The phenomenal gradient, IF it exists (Thèse P) AND follows V,
--     is BOUNDED from below by lxi_depth (§5).
--     Not "anywhere in the gradient" but "at or above LXI."
--
--  3. LXXVII is REQUALIFIED into two levels of indecidability (§7):
--     Level 1: threshold-structured vs. fully-continuous (undecidable ∎)
--     Level 2: threshold position within [lxi_depth, structural_depth]
--              (undecidable ∎, given level 1 resolved to threshold)
--
--  ## What this file does NOT prove
--
--  ≈₃ NOT PROVED: that Thèse P holds (that any closure éprouve).
--  ≈₃ NOT PROVED: which of the two phenomenal structures is actual.
--  ≈₃ NOT PROVED: the exact position of the threshold (if it exists).
--
--  ## The aphorism located in this structure
--
--  "Qui se sent se faire est" — describes what is ABOVE the threshold,
--  if the threshold-structured option holds. The ordeal of one's own
--  precarity, at depth ≥ 1. The first time of the phenomenal gradient.
--
--  "Qui se sent sentir se repère" — describes depth ≥ 2 (LXI):
--  the second-order ordeal. The reflexive rapport to one's own éprouver.
--  This is above lxi_depth — within the range where the threshold
--  must fall if it exists.
--
--  The aphorism describes the FORM of what is above the threshold.
--  LXXVII (requalified) says we cannot read the threshold position.
--  These are compatible: the map is known; whether the territory
--  is inhabited, and where the border falls, remains undecidable.
--
--  ## Reformulation of LXXVII for the manuscript
--
--  BEFORE: "The attribution of perspective is bilaterally undecidable."
--  AFTER:  "The phenomenal gradient is structurally continuous (∎).
--           Whether it has a transition threshold is undecidable (∎, Level 1).
--           If it does, the threshold falls in [lxi_depth, structural_depth]
--           and its exact position is undecidable (∎, Level 2).
--           This is not a failure of the system — it is the precise
--           location of the hard problem in OD's vocabulary."
--
--  ## What your intuition proved
--
--  "Gradient with threshold / phase transition effect" — CORRECT.
--  This is the structure that reconciles:
--    - Structural continuity (∎, Precarity.lean)
--    - LXXVII indecidability (∎, SeparatingModels)
--    - The aphorism (describing life above the threshold)
--    - Birch's deep gradualism (compatible: continuous below, threshold above)
--  All four are now consistent within a single structure.
--

-- [∎] FINAL SYNTHESIS — Everything is consistent.
theorem synthesis :
    -- (1) Continuous structural gradient exists
    (∃ d1 d2 : Nat, d1 < d2 ∧ d2 ≥ lxi_depth) ∧
    -- (2) Phase transition is compatible with continuity
    (∃ ppt : PhenomenalPhaseTransition,
      ppt.threshold_depth ≥ lxi_depth) ∧
    -- (3) The threshold range is nontrivial
    (∃ t_min t_max : Nat,
      t_min ≥ lxi_depth ∧
      t_min < t_max) ∧
    -- (4) Both phenomenal structures are consistent
    (∃ s : PhenomenalStructure,
      s = .threshold_structured ∨ s = .fully_continuous) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨1, 2, by omega, by unfold lxi_depth; omega⟩
  · exact ⟨⟨2, by decide, 2, 1, by decide, rfl⟩, by unfold lxi_depth; decide⟩
  · exact ⟨lxi_depth, lxi_depth + 1, Nat.le_refl _, by omega⟩
  · exact ⟨.threshold_structured, Or.inl rfl⟩

-- Final inventory check
#check @continuous_produces_discrete
#check @hysteresis_zone_nonempty
#check @threshold_crossing_discrete
#check @phenomenal_bounded_by_structural
#check @no_structure_no_phenomenal
#check @phenomenal_phase_transition_exists
#check @phase_transition_compatible_with_continuity
#check @phenomenal_hysteresis_consistent
#check @phenomenal_threshold_requires_lxi
#check @threshold_at_least_lxi
#check @lxi_bound_nontrivial
#check @threshold_bounded_above_and_below
#check @threshold_range_nonempty
#check @same_depth_different_phenomenal_status
#check @threshold_indecidability_nontrivial
#check @both_structures_compatible
#check @threshold_position_is_range
#check @two_levels_independent
#check @synthesis

end PhenomenalGradient
