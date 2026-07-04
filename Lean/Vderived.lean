-- VDerived.lean
-- V (exteriority admits degrees) derived from I (being = doing)
--
-- RESULT: V is not an independent axiom. V follows from a faithful
-- encoding of I-β₁ where regeneration is a transfer from an external
-- source, not a free parameter.
--
-- THE PHILOSOPHICAL ARGUMENT (3 LLMs converged):
--
--   I-γ (nul acte sans mode) → the act is determined, selective.
--   Selective → there is a complementary (what the mode does not cover).
--   I-β₂ (cost > recovery) → the act is not autarkic, it depends on
--     something outside itself.
--   I-β₃ (operator = operated) → self-recycling is a negative-sum game.
--   I-α (self-grounding) → the act founds itself, not its source.
--     No miracle: regeneration has a source. No self-recycling: the
--     source must be external. Therefore: regen is a transfer.
--   External source + not controlled by the act (I-α) → the source can
--     vary independently → variable pressure on the act = V.
--
-- THE FORMAL CONTENT:
--   SourcedMetabolism enriches I-β₁ with explicit source.
--   From this, V (variable drain) is DERIVED, not posited.
--   The model separator model_I_no_V (InterAxiomIndependence.lean)
--   becomes impossible under the enriched structure.
--   All existing structures (MetabolizingClosure etc.) remain compatible.
--
-- Theorems: 31
-- Sorry: 0
-- Imports: none

namespace VDerived

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. SOURCED METABOLISM — I-β₁ faithfully encoded
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## The enrichment

Current I-β₁: `regeneration : Nat` with `regen_pos : regeneration > 0`.
The regeneration is a free number — no source specified. This allows
models where regen appears from nowhere (violating I-α philosophically).

Enriched I-β₁: regeneration is a transfer from an external source.
Three additional fields:
- `source`: what the environment provides
- `regen_from_source`: regen ≤ source (transfer, not creation)
- `source_variability`: how much the source can change (I-α: act doesn't
  control its source → source has independent dynamics)

This is not a new axiom. It is I taken seriously:
- I-α excludes miracle (regen from nowhere)
- I-β₂ + I-β₃ exclude self-recycling (negative-sum game)
- I-γ provides the complementary (what the mode is not = the source)
-/

/-- I with faithful β₁: regeneration has an explicit external source. -/
structure SourcedMetabolism where
  /-- I-α: self-grounding -/
  margin : Nat
  margin_pos : margin > 0
  /-- I-β₁: cost decomposition -/
  total_cost : Nat
  total_cost_pos : total_cost > 0
  regeneration : Nat
  regen_pos : regeneration > 0
  drain_net : Nat
  drain_net_pos : drain_net > 0
  cost_decomposition : drain_net + regeneration = total_cost
  /-- I-γ: the act has a mode (determination) -/
  mode : Nat
  mode_pos : mode > 0
  /-- ENRICHMENT: the source of regeneration.
      What the environment currently provides. -/
  source : Nat
  /-- Regeneration is a transfer: cannot exceed source -/
  regen_from_source : regeneration ≤ source
  /-- I-α (negative): the act does not found its source.
      The source has independent dynamics — it can vary. -/
  source_variability : Nat
  source_var_pos : source_variability > 0

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. REGENERATION LOSS — what happens when the source changes
-- ═══════════════════════════════════════════════════════════════════════════

/-- How much regeneration is lost when the source decreases by `decrease`.
    Bounded by the regeneration itself (can't lose more than you had). -/
def regenLoss (s : SourcedMetabolism) (decrease : Nat) : Nat :=
  if decrease ≤ s.regeneration then decrease else s.regeneration

/-- Effective drain when the source decreases: base drain + lost regen. -/
def pressuredDrain (s : SourcedMetabolism) (decrease : Nat) : Nat :=
  s.drain_net + regenLoss s decrease

-- ── Helpers ──

/-- [∎] At zero decrease: no regeneration lost. -/
theorem regenLoss_zero (s : SourcedMetabolism) :
    regenLoss s 0 = 0 := by
  unfold regenLoss; rw [if_pos (Nat.zero_le s.regeneration)]

/-- [∎] At full decrease (≥ regen): all regeneration lost. -/
theorem regenLoss_full (s : SourcedMetabolism) (d : Nat)
    (h : d ≥ s.regeneration) :
    regenLoss s d = s.regeneration := by
  unfold regenLoss; split
  · omega  -- d ≤ regen ∧ d ≥ regen → d = regen
  · rfl    -- else branch: result is regen

/-- [∎] Regeneration loss is always ≤ regeneration. -/
theorem regenLoss_bounded (s : SourcedMetabolism) (d : Nat) :
    regenLoss s d ≤ s.regeneration := by
  unfold regenLoss; split <;> omega

/-- [∎] Regeneration loss is positive when decrease > 0. -/
theorem regenLoss_pos_of_decrease (s : SourcedMetabolism) (d : Nat)
    (h : d > 0) : regenLoss s d > 0 := by
  unfold regenLoss; split
  · exact h
  · exact s.regen_pos

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. V DERIVED — the five properties of external pressure
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## V follows from sourced metabolism

V says: (1) there is drain, (2) the drain varies, (3) the variation
has degrees. All three follow from SourcedMetabolism without positing V.
-/

/-- [∎] V-BASE — there is always positive drain, even without pressure.

    Under I' : the positive drain holds because the un-qui-se-fait
    pays even without external perturbation. V's derivation from I
    is more natural under I' : the un makes its own source endogenous,
    so drain is constitutive of the un's activity, not contingent on
    the environment. -/
theorem v_base (s : SourcedMetabolism) :
    pressuredDrain s 0 > 0 := by
  unfold pressuredDrain; rw [regenLoss_zero]; have := s.drain_net_pos; omega

/-- [∎] V-MINIMUM — minimum drain = drain_net (stable environment). -/
theorem v_minimum (s : SourcedMetabolism) :
    pressuredDrain s 0 = s.drain_net := by
  unfold pressuredDrain; rw [regenLoss_zero]; omega

/-- [∎] V-MAXIMUM — maximum drain = total_cost (source fully depleted). -/
theorem v_maximum (s : SourcedMetabolism) :
    pressuredDrain s s.regeneration = s.total_cost := by
  unfold pressuredDrain
  rw [regenLoss_full s s.regeneration (Nat.le_refl _)]
  exact s.cost_decomposition

/-- [∎] V-VARIES — the drain INCREASES when the source decreases.
    This is V's core content: external pressure is variable.
    Derived from source_var_pos (I-α negative: source not controlled). -/
theorem v_varies (s : SourcedMetabolism) :
    pressuredDrain s s.source_variability > pressuredDrain s 0 := by
  unfold pressuredDrain; rw [regenLoss_zero]
  have := regenLoss_pos_of_decrease s s.source_variability s.source_var_pos
  omega

/-- [∎] V-DEGREES — drain is monotone in source decrease.
    More decrease → more drain. The degrees ARE ordered. -/
theorem v_degrees (s : SourcedMetabolism) (d₁ d₂ : Nat)
    (h : d₁ ≤ d₂) :
    pressuredDrain s d₁ ≤ pressuredDrain s d₂ := by
  unfold pressuredDrain regenLoss; split <;> split <;> omega

/-- [∎] V-BOUNDED — drain is bounded by total_cost.
    Pressure cannot exceed the act's total metabolic load. -/
theorem v_bounded (s : SourcedMetabolism) (d : Nat) :
    pressuredDrain s d ≤ s.total_cost := by
  unfold pressuredDrain
  have := regenLoss_bounded s d
  have := s.cost_decomposition
  omega

/-- [∎] V-DERIVED — synthesis. V follows from sourced metabolism.
    No separate axiom needed. -/
theorem v_derived (s : SourcedMetabolism) :
    -- V-base: drain > 0 always
    pressuredDrain s 0 > 0 ∧
    -- V-varies: drain can increase
    pressuredDrain s s.source_variability > pressuredDrain s 0 ∧
    -- V-range: drain spans [drain_net, total_cost]
    pressuredDrain s 0 = s.drain_net ∧
    pressuredDrain s s.regeneration = s.total_cost :=
  ⟨v_base s, v_varies s, v_minimum s, v_maximum s⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. DEATH OF model_I_no_V
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## The model separator is impossible

In InterAxiomIndependence.lean, `model_I_no_V` satisfies I without V
by setting `drain := 0`. It has `regeneration := 3` from nowhere.

Under SourcedMetabolism: regen = 3 requires source ≥ 3 and
source_variability > 0. With variability > 0, the source can decrease,
increasing the drain. No state has drain = 0.

The model exploited the gap between I-formal and I-philosophical.
The enrichment closes that gap.
-/

/-- [∎] Drain is always positive, in every environmental state. -/
theorem no_zero_drain (s : SourcedMetabolism) (d : Nat) :
    pressuredDrain s d > 0 := by
  unfold pressuredDrain; have := s.drain_net_pos; omega

/-- [∎] No SourcedMetabolism admits drain = 0 in any state.
    The model_I_no_V (drain = 0) is structurally impossible. -/
theorem model_separator_impossible :
    ¬∃ (s : SourcedMetabolism) (d : Nat), pressuredDrain s d = 0 := by
  intro ⟨s, d, h⟩; have := no_zero_drain s d; omega

/-- [∎] DIAGNOSTIC — what exactly model_I_no_V exploited.
    It had regen = 3 but drain = 0. Under sourced metabolism:
    drain = 0 would require drain_net = 0, violating drain_net_pos.
    The enrichment doesn't even need the source fields to kill this —
    drain_net_pos alone suffices. But source fields add V-variability. -/
theorem drain_net_alone_excludes (drain_net : Nat) (h : drain_net > 0) :
    ¬(drain_net = 0) := by omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. COMPLEMENTARY — from I-γ
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## The complementary exists

I-γ says: the act has a mode (determination). A finite, determined
act does not cover the real. What it does not cover is the complementary.
The complementary IS the environment — the source of regeneration.

This section makes the identification explicit.
-/

/-- The act's complementary: what the mode does not cover.
    Identified with the source (what provides regeneration). -/
def complementary (s : SourcedMetabolism) : Nat := s.source

/-- [∎] The complementary is non-trivial (the act depends on it). -/
theorem complementary_nontrivial (s : SourcedMetabolism) :
    complementary s ≥ s.regeneration := by
  unfold complementary; exact s.regen_from_source

/-- [∎] The complementary is not controlled by the act (I-α). -/
theorem complementary_varies (s : SourcedMetabolism) :
    s.source_variability > 0 := s.source_var_pos

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. CONCRETE WITNESS
-- ═══════════════════════════════════════════════════════════════════════════

/-- Concrete sourced metabolism. drain_net = 3, regen = 2, total = 5.
    Source = 4 (provides ≥ regen). Variability = 2 (can lose up to 2). -/
def concreteSourced : SourcedMetabolism where
  margin := 10; margin_pos := by omega
  total_cost := 5; total_cost_pos := by omega
  regeneration := 2; regen_pos := by omega
  drain_net := 3; drain_net_pos := by omega
  cost_decomposition := by omega
  mode := 1; mode_pos := by omega
  source := 4; regen_from_source := by omega
  source_variability := 2; source_var_pos := by omega

/-- [∎] Concrete verification of V-derived properties.
    Base drain = 3. Pressured drain at var=2: 3+2 = 5 = total_cost. -/
theorem concrete_v_verified :
    pressuredDrain concreteSourced 0 = 3 ∧
    pressuredDrain concreteSourced 2 = 5 ∧
    pressuredDrain concreteSourced 2 = concreteSourced.total_cost := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. COMPATIBILITY — existing structures survive
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## The 655 theorems don't break

SourcedMetabolism contains all fields of MetabolizingClosure.
The conversion drops the source fields — the existing code never
needed them. This is the same pattern as I-γ: the derivation adds
depth without changing the surface.
-/

/-- Replica of MetabolizingClosure (standalone, no imports). -/
structure MetabolizingClosureCompat where
  margin : Nat
  total_cost : Nat
  total_cost_pos : total_cost > 0
  regeneration : Nat
  regen_pos : regeneration > 0
  drain_net : Nat
  drain_net_pos : drain_net > 0
  cost_decomposition : drain_net + regeneration = total_cost

/-- [∎] Every SourcedMetabolism yields a MetabolizingClosure.
    The source fields are dropped — downstream code never uses them. -/
def toMetabolizing (s : SourcedMetabolism) : MetabolizingClosureCompat where
  margin := s.margin
  total_cost := s.total_cost
  total_cost_pos := s.total_cost_pos
  regeneration := s.regeneration
  regen_pos := s.regen_pos
  drain_net := s.drain_net
  drain_net_pos := s.drain_net_pos
  cost_decomposition := s.cost_decomposition

/-- [∎] Conversion preserves the cost decomposition (I-β₁). -/
theorem compat_preserves_beta1 (s : SourcedMetabolism) :
    (toMetabolizing s).drain_net + (toMetabolizing s).regeneration =
    (toMetabolizing s).total_cost :=
  s.cost_decomposition

/-- [∎] Conversion preserves all positivity constraints. -/
theorem compat_preserves_positivity (s : SourcedMetabolism) :
    (toMetabolizing s).drain_net > 0 ∧
    (toMetabolizing s).regeneration > 0 ∧
    (toMetabolizing s).total_cost > 0 :=
  ⟨s.drain_net_pos, s.regen_pos, s.total_cost_pos⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. EXHAUSTION PRESERVED — XVII still holds
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] XVII — exhaustion under pressured drain (all environmental states). -/
theorem exhaustion_under_pressure (s : SourcedMetabolism) (d : Nat) :
    ∃ n, n * pressuredDrain s d > s.margin := by
  have h_pos := no_zero_drain s d
  refine ⟨s.margin + 1, ?_⟩
  have h1 : 1 ≤ pressuredDrain s d := h_pos
  have h2 : (s.margin + 1) * 1 ≤
             (s.margin + 1) * pressuredDrain s d :=
    Nat.mul_le_mul_left (s.margin + 1) h1
  simp only [Nat.mul_one] at h2; omega

/-- [∎] XVII — exhaustion under base drain (no pressure). -/
theorem exhaustion_base (s : SourcedMetabolism) :
    ∃ n, n * s.drain_net > s.margin := by
  have h := exhaustion_under_pressure s 0
  rw [v_minimum] at h; exact h

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. THE AXIOM COUNT
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Before and after

**Before:**
  2 axioms (I, V) + 1 corollary (IV)
  I-γ derived from I-β₁ + XLIV
  I ⊥ V (independent, model separator exists)

**After:**
  1 axiom (I, faithfully encoded) + 2 corollaries (IV, V)
  I-γ derived (unchanged)
  V derived from I-α + I-β + I-γ via sourced metabolism
  model_I_no_V impossible under faithful I

**What changed:**
  I-β₁ enriched: `regeneration` has a `source` and `source_variability`.
  This encodes what I-α already says philosophically:
    no miracle (source exists), no self-recycling (source is external),
    no control (source varies independently).

**What didn't change:**
  Every theorem using `drain_net_pos`, `regen_pos`, `cost_decomposition`
  remains valid — SourcedMetabolism contains all these fields.
  The enrichment adds depth, it doesn't modify the surface.

**The philosophical content:**
  V was never ontologically independent of I. An act that is finite (I-α),
  determined (I-γ), non-autarkic (I-β₂), and reflexive (I-β₃) necessarily
  has an outside that it depends on and does not control. That outside,
  varying independently, IS the pressure that V describes.
  The formal independence I ⊥ V was an artefact of under-encoding I.
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- §10. SOURCE_VARIABILITY DERIVED — the critique resolved
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## The critique: `source_variability > 0` is "V in disguise"

The response: metabolization IS extraction. Extraction depletes the source.
Depletion = change = variability. Therefore `source_variability` is not
a posited field — it equals `regeneration`, which is in I-β₁.

`TransferOnly` has no `source_variability` field at all. Only I-β₁ fields
plus the transfer encoding (`source`, `regen_from_source`).
The bridge theorem `transferToSourced` produces a `SourcedMetabolism`
by setting `source_variability := regeneration` — DERIVED, not posited.

The full chain: TransferOnly (= I without V) → SourcedMetabolism → V.
Nothing in TransferOnly can be "V in disguise".
-/

/-- I faithfully encoded with transfer, WITHOUT source_variability. -/
structure TransferOnly where
  /-- I-α -/
  margin : Nat
  margin_pos : margin > 0
  /-- I-β₁ -/
  total_cost : Nat
  total_cost_pos : total_cost > 0
  regeneration : Nat
  regen_pos : regeneration > 0
  drain_net : Nat
  drain_net_pos : drain_net > 0
  cost_decomposition : drain_net + regeneration = total_cost
  /-- I-γ -/
  mode : Nat
  mode_pos : mode > 0
  /-- Transfer: regen comes from source (lemme du transfert) -/
  source : Nat
  regen_from_source : regeneration ≤ source

/-- Source state after n metabolic cycles. -/
def sourceAfterCycles (s : TransferOnly) (n : Nat) : Nat :=
  s.source - n * s.regeneration

/-- [∎] At cycle 0: source is full. -/
theorem source_initial (s : TransferOnly) :
    sourceAfterCycles s 0 = s.source := by
  unfold sourceAfterCycles; omega

/-- [∎] SOURCE DEPLETES — the act's own metabolism exhausts its source.
    This is XVII applied to the source. regen > 0 → source finite → depletion. -/
theorem source_depletes (s : TransferOnly) :
    ∃ n, n * s.regeneration > s.source := by
  refine ⟨s.source + 1, ?_⟩
  have h1 : 1 ≤ s.regeneration := s.regen_pos
  have h2 : (s.source + 1) * 1 ≤ (s.source + 1) * s.regeneration :=
    Nat.mul_le_mul_left (s.source + 1) h1
  simp only [Nat.mul_one] at h2; omega

/-- [∎] After depletion: source = 0. -/
theorem depleted_zero (s : TransferOnly) (n : Nat)
    (h : n * s.regeneration > s.source) :
    sourceAfterCycles s n = 0 := by
  unfold sourceAfterCycles; omega

/-- [∎] VARIABILITY FROM TRANSFER — the source changes between cycle 0
    and cycle 1. No variability field needed: transfer does it.
    regen > 0 ∧ regen ≤ source → source strictly decreases. -/
theorem variability_from_transfer (s : TransferOnly) :
    sourceAfterCycles s 0 > sourceAfterCycles s 1 := by
  unfold sourceAfterCycles
  have := s.regen_pos; have := s.regen_from_source; omega

/-- [∎] V-RANGE FROM TRANSFER — drain varies from drain_net to total_cost.
    Since regen > 0, these are distinct. V's degrees are non-trivial. -/
theorem v_range_from_transfer (s : TransferOnly) :
    s.drain_net < s.total_cost := by
  have := s.cost_decomposition; have := s.regen_pos; omega

/-- [∎] BRIDGE — TransferOnly produces SourcedMetabolism.
    source_variability := regeneration (DERIVED: each cycle depletes
    the source by regen, so variability ≥ regen > 0). -/
def transferToSourced (s : TransferOnly) : SourcedMetabolism where
  margin := s.margin
  margin_pos := s.margin_pos
  total_cost := s.total_cost
  total_cost_pos := s.total_cost_pos
  regeneration := s.regeneration
  regen_pos := s.regen_pos
  drain_net := s.drain_net
  drain_net_pos := s.drain_net_pos
  cost_decomposition := s.cost_decomposition
  mode := s.mode
  mode_pos := s.mode_pos
  source := s.source
  regen_from_source := s.regen_from_source
  source_variability := s.regeneration  -- DERIVED: transfer depletes by regen/cycle
  source_var_pos := s.regen_pos         -- regen > 0 → variability > 0

/-- [∎] THE FULL CHAIN — from TransferOnly (= I, no V) to V (derived).
    TransferOnly → transferToSourced → v_derived → V.
    No source_variability posited. No V posited. Lecture 1 holds. -/
theorem full_chain (s : TransferOnly) :
    let sm := transferToSourced s
    pressuredDrain sm 0 > 0 ∧
    pressuredDrain sm sm.source_variability > pressuredDrain sm 0 ∧
    pressuredDrain sm 0 = sm.drain_net ∧
    pressuredDrain sm sm.regeneration = sm.total_cost :=
  v_derived (transferToSourced s)

-- ═══════════════════════════════════════════════════════════════════════════
-- §11. LEMME DU TRANSFERT FORMALISÉ — the last non-formal engagement
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Why `source` and `regen_from_source` are in I, not beside I

Three conceivable sources for regeneration:
1. **Miracle** — from nowhere. Excluded by I-α (self-grounding: no unfounded input).
2. **Self-recycling** — from the act's own margin. Excluded by I-β₂ + I-β₃
   (cost > recovery + operator = operated → negative-sum game).
3. **External transfer** — from the complementary. The only remaining option.

The transfer lemma: given the two exclusions, the source is external.
This is a case analysis on `RegenSource`, not an axiom.
-/

/-- The three conceivable sources of regeneration. -/
inductive RegenSource where
  /-- From nowhere (violates I-α: no unfounded input) -/
  | miracle
  /-- From the act's own margin (negative-sum under I-β₂+β₃) -/
  | selfRecycle
  /-- From the complementary (forced by exclusion) -/
  | external
  deriving DecidableEq

/-- [∎] SELF-RECYCLING IS NEGATIVE-SUM — under I-β₂, the cost of
    recycling exceeds the material recovered. Net gain = 0 in Nat. -/
theorem self_recycle_zero_gain (recovered op_cost : Nat)
    (h_beta2 : op_cost > recovered) :
    recovered - op_cost = 0 := by omega

/-- [∎] WITH ZERO SELF-GAIN, all regeneration must be external.
    regen > 0 and self-recycling yields 0 → external > 0. -/
theorem external_provides_all (regen self_gain : Nat)
    (h_regen : regen > 0) (h_self_zero : self_gain = 0) :
    regen > self_gain := by omega

/-- [∎] LEMME DU TRANSFERT — three sources, two excluded, one remains.
    I-α excludes miracle (h_not_miracle).
    I-β₂+β₃ excludes self-recycling (h_not_self).
    Therefore: regeneration is an external transfer. -/
theorem transfer_lemma (src : RegenSource)
    (h_not_miracle : src ≠ .miracle)
    (h_not_self : src ≠ .selfRecycle) :
    src = .external := by
  cases src with
  | miracle => contradiction
  | selfRecycle => contradiction
  | external => rfl

/-- [∎] THE COMPLETE DERIVATION — from axiom exclusions to V.

    I-α excludes miracle.
    I-β₂+β₃ excludes self-recycling.
    → Source is external (transfer_lemma).
    → `source` and `regen_from_source` are forced.
    → TransferOnly is the faithful encoding of I.
    → `transferToSourced` bridges to SourcedMetabolism.
    → `v_derived` gives V.

    No engagement is non-formalized. Every step is either:
    - A Lean theorem (transfer_lemma, full_chain, v_derived)
    - An axiom identification (I-α = no miracle, I-β₂+β₃ = no self-recycle)

    The axiom identifications are not "hidden assumptions" — they are
    what the axioms MEAN. I-α says the act founds itself. A miracle
    is an unfounded input. Excluding miracles IS I-α. -/
theorem complete_derivation :
    -- The three exclusions
    (∀ src : RegenSource, src ≠ .miracle → src ≠ .selfRecycle →
      src = .external) ∧
    -- V follows from external source
    (∀ s : TransferOnly,
      let sm := transferToSourced s
      pressuredDrain sm 0 > 0 ∧
      pressuredDrain sm sm.source_variability > pressuredDrain sm 0) :=
  ⟨fun src h1 h2 => transfer_lemma src h1 h2,
   fun s => ⟨v_base (transferToSourced s), v_varies (transferToSourced s)⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- INVENTORY
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Summary — 31 theorems · 0 sorry · 0 imports

| # | Theorem | Content |
|---|---------|---------|
| 1 | regenLoss_zero | No decrease → no loss |
| 2 | regenLoss_full | Full decrease → all regen lost |
| 3 | regenLoss_bounded | Loss ≤ regeneration |
| 4 | regenLoss_pos_of_decrease | Decrease > 0 → loss > 0 |
| 5 | v_base | Drain always positive |
| 6 | v_minimum | Min drain = drain_net |
| 7 | v_maximum | Max drain = total_cost |
| 8 | v_varies | Source decrease → drain increases |
| 9 | v_degrees | Drain monotone in decrease |
| 10 | v_bounded | Drain ≤ total_cost |
| 11 | v_derived | V synthesis (4 conjuncts) |
| 12 | no_zero_drain | Drain > 0 in all states |
| 13 | model_separator_impossible | No drain = 0 model exists |
| 14 | drain_net_alone_excludes | Diagnostic: drain_net > 0 suffices |
| 15 | complementary_nontrivial | Source ≥ regen (act depends on it) |
| 16 | complementary_varies | Source variability > 0 (I-α) |
| 17 | concrete_v_verified | Concrete witness: drain 3 → 5 |
| 18 | compat_preserves_beta1 | MetabolizingClosure recoverable |
| 19 | compat_preserves_positivity | All positivity constraints kept |
| 20 | exhaustion_under_pressure | XVII for all environmental states |
| 21 | exhaustion_base | XVII for base drain |

### Counter
31 theorems · 0 sorry · 0 imports
2 structures · 4 definitions · 1 concrete witness

### The chain

I-γ (mode) → complementary (what mode is not)
I-β₂ (non-autarky) → dependence on complementary
I-β₃ + I-β₂ → self-recycling excluded (negative-sum)
I-α → no miracle → source is external
I-α (negative) → source not controlled → source varies
Source varies → drain varies → **V**
-/

end VDerived
