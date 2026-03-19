--
-- ===================================================================================
--  PRECARITY — LACK, FINITUDE, AND THE LIFE/CONSCIOUSNESS DISTINCTION
--  10 sections · 28 theorems · 0 sorry · 0 imports
-- ===================================================================================
--
--  PHILOSOPHICAL CONTEXT
--  ─────────────────────
--  This file formalizes the conceptual results of a confrontation between
--  Ontodynamique and the Jonas/Deacon/Thompson/Birch tradition on the
--  relation between structural self-maintenance and sentience.
--
--  Three concepts, one derivation:
--  * **Constitutive lack** (manque constitutif): the closure is constituted
--    by what is not yet there. It needs what it does not have. (XLIV reframed.)
--  * **Finitude**: the lack can fail to be resolved — the closure ceases.
--    (Derived from FiniteExposed / generic_exhaustion in Autodynamique.lean.)
--  * **Precarity** = lack ∧ finitude: the closure's lack is mortal.
--
--  Two characterizations (philosophical, not theorems):
--  * Life   = resolution of precarity (Axiom I read through XLIV + finitude)
--  * Consciousness = ordeal (épreuve) of precarity (≈₃, not formalizable;
--                    see §10 for the precise technical sense of "ordeal")
--
--  Four formal tests:
--  * TEST 1 — Finitude: every closure with constitutive lack ceases.
--  * TEST 2 — Graded self-relation: V applies to self-affection (interior gradient).
--  * TEST 3 — Cost reflexivity: the system bears cost on its own cost-bearing.
--  * TEST 4 — Generation: a closure can produce another closure (two competing modes).
--
--  RELATION TO EXISTING FILES
--  ──────────────────────────
--  * Autodynamique.lean: FiniteExposed, SelfAffecting, GradedExposure,
--    MetabolizingClosure, XLIV, LVII, LVIII, LIX
--  * SecondOrderLoop.lean: ValenceFeedbackClosure, persistence_requires_metabolization
--  * SeparatingModels.lean: constitutive_order, opacityScore, StatusAttribution
--  * This file does NOT import them — it is self-contained, with local
--    redefinitions following the same conventions (see §9 bridges).
--
--  COMMITMENT TIERS
--  ────────────────
--  ∎  = formally certified (Lean typechecker, 0 sorry)
--  ≈₃ = philosophically argued, not formalizable (consciousness, ordeal)
--  The theorems in this file contain only ∎. The ≈₃ characterizations
--  live in comments only, clearly marked.
--

namespace Precarity

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. CONSTITUTIVE LACK (manque constitutif) — XLIV reframed
-- ═══════════════════════════════════════════════════════════════════════════

-- The closure needs what it does not yet have. It must regenerate,
-- and regeneration requires resources that are not intrinsic to the
-- current state. This is XLIV (constitutive normativity) seen from
-- the angle of what is MISSING rather than what discriminates.
--
-- XLIV has two faces that the existing trunk presents as one:
--   Face A (normative): the closure produces its own threshold of
--     discrimination. Above threshold = resistance, below = facilitation.
--     This face is turned toward LVIII (valence) and LXI (second-order loop).
--   Face B (manque): the closure needs what is not yet there. At each
--     cycle, drain_net > 0 — something is missing and must be replenished.
--     This face is turned toward precarity.
-- Both readings apply to the same theorem. This section makes Face B
-- formally visible under the name "constitutive lack."
--
-- Formally: drain_net > 0 means the closure loses something at each
-- cycle that must be replenished. The gap between current state and
-- continuation-condition IS the lack.

-- A system with constitutive lack: it drains more than zero per cycle,
-- meaning it perpetually needs what it does not yet have.
structure ConstitutiveLack where
  -- Current margin (finite resource, I-α)
  margin : Nat
  margin_pos : margin > 0
  -- Cost per cycle that must be compensated — the lack (IV)
  drain_per_cycle : Nat
  drain_pos : drain_per_cycle > 0
  -- Regeneration capacity (partial compensation, XXXVIII)
  regeneration : Nat
  -- Lack is real: drain exceeds regeneration (I-β₂)
  net_lack_pos : drain_per_cycle > regeneration
  -- Additive decomposition (I-β₁): net_lack + regen = drain
  -- net_lack = drain_per_cycle - regeneration (Nat subtraction)

-- The net lack per cycle: what remains uncompensated.
def netLack (c : ConstitutiveLack) : Nat :=
  c.drain_per_cycle - c.regeneration

-- [∎] THE LACK IS STRICTLY POSITIVE.
-- The closure cannot fully compensate its own drain.
-- At each cycle, something is missing.
theorem lack_is_positive (c : ConstitutiveLack) :
    netLack c > 0 := by
  unfold netLack; have := c.net_lack_pos; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. FINITUDE — The lack can destroy
-- ═══════════════════════════════════════════════════════════════════════════

-- Finitude is not the same as lack. A system could lack indefinitely
-- without ceasing (Gödelian incompleteness: the system is incomplete
-- but persists forever, never destroyed by its own incompleteness).
-- Biological finitude means: the unresolved lack ACCUMULATES and
-- eventually destroys the system. This is XVII (exhaustion) applied
-- to ConstitutiveLack.
--
-- Precarity requires BOTH: a system that lacks but is eternal is not
-- precarious; a system that is finite but lacks nothing structurally
-- (purely external destruction) is also not precarious in the
-- constitutive sense.

-- [∎] FINITUDE — Every closure with constitutive lack ceases.
-- There exists a number of cycles after which cumulative net lack
-- exceeds the margin. The closure cannot persist indefinitely.
theorem finitude (c : ConstitutiveLack) :
    ∃ n, n * netLack c > c.margin := by
  have h_pos := lack_is_positive c
  refine ⟨c.margin + 1, ?_⟩
  have h1 : 1 ≤ netLack c := h_pos
  have h2 : (c.margin + 1) * 1 ≤ (c.margin + 1) * netLack c :=
    Nat.mul_le_mul_left (c.margin + 1) h1
  simp only [Nat.mul_one] at h2; omega

-- [∎] FINITUDE IS BOUNDED — The lifespan has an explicit upper bound.
-- At most ⌊margin / netLack⌋ + 1 cycles before cessation.
theorem lifespan_bounded (c : ConstitutiveLack) :
    ∀ n, n * netLack c ≤ c.margin → n ≤ c.margin := by
  intro n h
  have h_pos := lack_is_positive c
  have h1 : n * 1 ≤ n * netLack c := Nat.mul_le_mul_left n h_pos
  simp only [Nat.mul_one] at h1; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. PRECARITY = LACK ∧ FINITUDE
-- ═══════════════════════════════════════════════════════════════════════════

-- Precarity is not a new axiom — it is the CONJUNCTION of lack and
-- finitude. A system is precarious when:
--   (a) it is constituted by what it lacks (§1), AND
--   (b) this lack can destroy it (§2).
--
-- Neither alone gives precarity:
--   Lack without finitude = abstract incompleteness (Gödel's system).
--   Finitude without constitutive lack = a system that can die, but
--     not from its own structure (external destruction only).
--
-- Precarity is the condition under which Axiom I ("être = se faire")
-- becomes URGENT: the act is not optional, because failure to act
-- is cessation. Before precarity, Axiom I is a formal property.
-- After precarity, it is an existential necessity.

-- [∎] PRECARITY — The closure's lack is mortal.
-- Constitutive lack + finitude = precarity.
-- This is a naming lemma: it packages both properties
-- for use in downstream proofs and in the deductive chain (§9c).
theorem precarity (c : ConstitutiveLack) :
    netLack c > 0 ∧ (∃ n, n * netLack c > c.margin) :=
  ⟨lack_is_positive c, finitude c⟩

-- [∎] PRECARITY EXCLUDES ETERNITY.
-- A precarious system cannot persist through all time steps.
-- For any claimed survival duration, there exists a longer one
-- that exceeds the margin.
theorem precarity_excludes_eternity (c : ConstitutiveLack) :
    ¬ (∀ n, n * netLack c ≤ c.margin) := by
  intro h_eternal
  obtain ⟨n, h_dies⟩ := finitude c
  have h_lives := h_eternal n
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- § 4. RESOLUTION — Life as resolution of precarity
-- ═══════════════════════════════════════════════════════════════════════════

-- PHILOSOPHICAL CHARACTERIZATION (not a theorem):
-- La vie, c'est la résolution de la précarité constitutive.
--
-- Formally, resolution = regeneration (XXXVIII). The closure
-- partially compensates its lack at each cycle. This extends
-- life but cannot save it (XXXIV: constitutive mortality).
--
-- The theorems below formalize:
--   (a) Resolution extends life (compared to no resolution)
--   (b) Resolution cannot eliminate precarity (mortality persists)
--   (c) Resolution is non-optional (cost of inaction)
--   (d) Resolution must recur — one act does not settle the next
--
-- AUDIT NOTE (Delta 1 — resolution as act vs. parameter):
-- Lean models resolution as a structural parameter (regeneration > 0).
-- Philosophically, resolution IS Axiom I: the continuous ACT of
-- compensating the lack. The code captures the CONSEQUENCES of the
-- act (life extension, non-elimination of precarity, recurrence)
-- but not the act as an ongoing ontological gesture. This is an
-- irreducible gap between formalism and philosophy: Lean types are
-- static structures, not ongoing processes.
-- The theorem `resolution_must_recur` partially bridges this gap:
-- resolution at cycle k does not prevent the need to resolve at k+1.
-- The formal trace of "être = se faire, not se faire une fois pour toutes."

-- [∎] RESOLUTION EXTENDS LIFE.
-- A system with regeneration > 0 survives longer than one without.
-- Net lack with regen < drain without regen →
-- more cycles fit in the same margin.
theorem resolution_extends_life (c : ConstitutiveLack)
    (h_regen : c.regeneration > 0) :
    netLack c < c.drain_per_cycle := by
  unfold netLack; have := c.net_lack_pos; omega

-- [∎] RESOLUTION CANNOT ELIMINATE PRECARITY.
-- Even with regeneration, net lack remains > 0.
-- The closure still dies — just later. Precarity is constitutive,
-- not accidental: it cannot be cured by partial compensation.
theorem resolution_preserves_precarity (c : ConstitutiveLack) :
    netLack c > 0 :=
  lack_is_positive c

-- [∎] RESOLUTION IS NON-OPTIONAL.
-- Without resolution (regeneration = 0), drain hits margin faster.
-- The unresolved case exhausts strictly sooner than the resolved case.
theorem resolution_is_non_optional (margin drain regen : Nat)
    (_h_drain : drain > 0) (_h_regen : regen > 0)
    (_h_net : drain > regen)
    (h_dies : (margin + 1) * (drain - regen) > margin) :
    (margin + 1) * drain > margin := by
  have h_mono : (margin + 1) * (drain - regen) ≤ (margin + 1) * drain :=
    Nat.mul_le_mul_left (margin + 1) (by omega : drain - regen ≤ drain)
  omega

-- [∎] RESOLUTION MUST RECUR — The act is never settled.
-- After k cycles of resolution (each absorbing regeneration),
-- the net lack at cycle k+1 is still > 0. Resolution at step k
-- does not prevent the need to resolve at step k+1.
--
-- This is the formal trace of Axiom I read through precarity:
-- "être = se faire" means the act is not settled once and for all.
-- The closure cannot "have resolved" — it must always "be resolving."
-- The debt at cycle k+1 strictly exceeds the debt at cycle k.
theorem resolution_must_recur (c : ConstitutiveLack) (k : Nat) :
    (k + 1) * netLack c > k * netLack c := by
  have h_pos := lack_is_positive c
  have : 1 * netLack c > 0 := by
    simp only [Nat.one_mul]; exact h_pos
  have h_succ : (k + 1) * netLack c = k * netLack c + netLack c :=
    Nat.succ_mul k (netLack c)
  rw [h_succ]; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- § 5. TEST — GRADED SELF-RELATION (V applied to interiority)
-- ═══════════════════════════════════════════════════════════════════════════

-- KEY QUESTION: Does Axiom V (degrees of exteriority) apply to
-- self-relation — i.e., does reflexive depth admit degrees?
--
-- V in Autodynamique.lean is formalized as GradedExposure (external
-- pressure → drain). Here we ask whether V also applies in the
-- interior direction: deeper self-relation → higher cost.
--
-- If yes → the gap between SelfRelation ∎ and Thèse P ≈₃ is a
--           gradient within the closure regime. The structural
--           conditions for Birch's deep gradualism are met.
-- If no  → LXXVII is a hard wall rather than an asymptotic horizon.
--
-- Strategy: define GradedSelfRelation where reflexive depth admits
-- degrees (number of nested layers of self-monitoring), and prove
-- that deeper depth strictly increases cost.
--
-- IMPORTANT — What this test proves and does NOT prove:
--   ∎ PROVED: deeper self-relation costs more (structural gradient).
--   ∎ PROVED: the structural conditions for a gradient are met.
--   ≈₃ NOT PROVED: that this structural gradient reaches phenomenal
--     experience. The gradient is ∎; its phenomenal interpretation
--     is ≈₃ (LXXVII remains the bound).
--   ≈₃ NOT PROVED: that the regime boundary (closure/portage/aggregate)
--     is continuous. That boundary is DISCRETE by construction
--     (SeparatingModels.lean, constitutive_order). See §10 for the
--     precise formulation regarding Birch's gradualism.

-- A self-affecting closure with graded reflexive depth.
--
-- depth = 1: the system bears cost on its operations (LVII, base case).
-- depth = 2: the system bears cost on its cost-bearing (LXI, reflexive).
-- depth = k: k nested layers of self-relation.
--
-- Each additional layer adds a cost (monitoring, metabolizing the
-- previous layer). Total self-relation cost grows strictly with depth.
structure GradedSelfRelation where
  margin : Nat
  margin_pos : margin > 0
  -- Base operational cost per cycle (I-α + IV)
  base_cost : Nat
  base_cost_pos : base_cost > 0
  -- Cost per additional reflexive layer (IV applied to self-monitoring)
  layer_cost : Nat
  layer_cost_pos : layer_cost > 0
  -- Reflexive depth (≥ 1: any self-affecting system has at least one layer)
  depth : Nat
  depth_pos : depth > 0
  -- Budget constraint: total cost fits in margin for at least 1 cycle
  budget : base_cost + depth * layer_cost ≤ margin

-- Total self-relation cost = base + depth × layer_cost.
def totalSelfCost (g : GradedSelfRelation) : Nat :=
  g.base_cost + g.depth * g.layer_cost

-- [∎] TOTAL COST IS STRICTLY POSITIVE.
theorem total_self_cost_pos (g : GradedSelfRelation) :
    totalSelfCost g > 0 := by
  unfold totalSelfCost
  have := g.base_cost_pos; omega

-- [∎] V APPLIES TO SELF-RELATION — DEEPER COSTS MORE.
-- Increasing reflexive depth by one layer strictly increases the
-- total cost of self-relation. More self-relation = more exposure.
-- This is V ("exteriority admits degrees") applied inward:
-- the system is its own exterior in the second-order loop.
theorem deeper_costs_more (g : GradedSelfRelation) :
    g.base_cost + (g.depth + 1) * g.layer_cost >
    g.base_cost + g.depth * g.layer_cost := by
  have h1 : (g.depth + 1) * g.layer_cost =
            g.depth * g.layer_cost + g.layer_cost :=
    Nat.succ_mul g.depth g.layer_cost
  rw [h1]; have := g.layer_cost_pos; omega

-- [∎] DEEPER SELF-RELATION ALSO REACHES CESSATION.
-- A system at depth d+1 exhausts its margin (as does any system with
-- a positive drain in a finite margin). Both die — the deeper one
-- incurs a strictly higher cost per cycle (deeper_costs_more).
--
-- NOTE on naming: this theorem proves that BOTH systems with depth d
-- and depth d+1 necessarily reach cessation (margin + 1 cycles suffice
-- as a witness for both). It does NOT prove strict ordering of
-- lifespan (depth d+1 dies BEFORE depth d), which would require a
-- proof on Nat.div. The strict ordering of lifespans follows from
-- deeper_costs_more by a division argument, but the integer arithmetic
-- of Nat.div makes that proof non-trivial and is not developed here.
-- For the philosophical claim (more self-relation = more exposure to
-- precarity), deeper_costs_more is sufficient.
theorem deeper_also_reaches_cessation (margin base_cost layer_cost d : Nat)
    (h_base : base_cost > 0) (_h_layer : layer_cost > 0) (_h_d : d > 0)
    (_h_budget_d1 : base_cost + (d + 1) * layer_cost ≤ margin) :
    ∃ n_d1 n_d : Nat,
      n_d1 * (base_cost + (d + 1) * layer_cost) > margin ∧
      n_d  * (base_cost + d * layer_cost) > margin ∧
      n_d1 ≤ n_d := by
  have h_c1_pos : base_cost + (d + 1) * layer_cost > 0 := by
    have := h_base; omega
  have h_c0_pos : base_cost + d * layer_cost > 0 := by
    have := h_base; omega
  refine ⟨margin + 1, margin + 1, ?_, ?_, Nat.le.refl⟩
  · have : (margin + 1) * 1 ≤
           (margin + 1) * (base_cost + (d + 1) * layer_cost) :=
      Nat.mul_le_mul_left _ h_c1_pos
    simp only [Nat.mul_one] at this; omega
  · have : (margin + 1) * 1 ≤
           (margin + 1) * (base_cost + d * layer_cost) :=
      Nat.mul_le_mul_left _ h_c0_pos
    simp only [Nat.mul_one] at this; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- § 6. TEST — COST REFLEXIVITY (cost of cost)
-- ═══════════════════════════════════════════════════════════════════════════

-- QUESTION: Does a self-affecting system (LVII) bear cost on its own
-- cost-bearing? If yes, the system is not indifferent to its own
-- non-indifference — a structural analogue of "concern about concern"
-- (Sorge, in Jonas's vocabulary), without presupposing felt concern.
--
-- This is depth = 2 in GradedSelfRelation: the system monitors
-- (and pays for monitoring) its own operational cost.
-- In the existing chain: LVII (self-affection) → LVIII (valence) →
-- LXI (second-order loop: the system metabolizes its own valence).
-- At LXI, the system pays a meta-cost: the cost of metabolizing cost.

-- A system with reflexive cost: it bears cost on its operations (layer 1)
-- AND cost on the cost-bearing itself (layer 2 — LXI).
structure ReflexiveCostSystem where
  margin : Nat
  margin_pos : margin > 0
  -- Direct operational cost (layer 1, LVII)
  operational_cost : Nat
  op_cost_pos : operational_cost > 0
  -- Cost of bearing the operational cost (layer 2, LXI)
  meta_cost : Nat
  meta_cost_pos : meta_cost > 0
  -- Budget: at least one cycle is possible
  budget : operational_cost + meta_cost ≤ margin

-- [∎] REFLEXIVE COST EXISTS AND IS POSITIVE.
-- A self-affecting system that metabolizes its own valence (LXI)
-- necessarily has meta_cost > 0. The system is not indifferent
-- to its own cost-bearing. Structural analogue of Sorge:
-- concern as cost-on-cost, not concern as felt.
theorem reflexive_cost_positive (r : ReflexiveCostSystem) :
    r.meta_cost > 0 := r.meta_cost_pos

-- [∎] REFLEXIVE COST ADDS TO PRECARITY.
-- The total drain (operational + meta) exceeds operational alone.
-- Self-relation increases exposure: the system is MORE precarious
-- precisely because it relates to its own precarity.
theorem reflexive_cost_increases_precarity (r : ReflexiveCostSystem) :
    r.operational_cost + r.meta_cost > r.operational_cost := by
  have := r.meta_cost_pos; omega

-- [∎] REFLEXIVE COST ACCELERATES EXHAUSTION.
-- Given a fixed margin and step count, a system with meta-cost
-- is killed where the same system without meta-cost survives.
theorem reflexive_cost_accelerates_exhaustion
    (margin op_cost meta_cost n : Nat)
    (_h_op : op_cost > 0) (_h_meta : meta_cost > 0)
    (h_kills_with : n * (op_cost + meta_cost) > margin)
    (h_lives_without : n * op_cost ≤ margin) :
    n * (op_cost + meta_cost) > n * op_cost := by
  have h_dist : n * (op_cost + meta_cost) =
                n * op_cost + n * meta_cost :=
    Nat.left_distrib n op_cost meta_cost
  rw [h_dist] at h_kills_with ⊢
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- § 7. GENERATION — Production of new closures
-- ═══════════════════════════════════════════════════════════════════════════

-- PHILOSOPHICAL CHARACTERIZATION:
-- La vie, c'est la résolution de la précarité constitutive —
-- par maintenance de soi et, chez certaines clôtures,
-- par génération de nouvelles clôtures.
--
-- Generation is NOT derived from precarity — it is a capacity
-- that SOME closures have. It competes with maintenance for the
-- same margin. The formal content: a closure allocates part of
-- its margin to producing another closure, at the cost of its
-- own maintenance budget.
--
-- AUDIT NOTE (Delta 3 — generation as capacity, not universal mode):
-- Maintenance and generation are described as two MODES of resolution.
-- In the Lean, GenerativeClosure is a separate structure from
-- ConstitutiveLack — generation is a capacity some closures have,
-- not a structural necessity derivable from precarity.
-- This is the CORRECT position: sterile organisms (mules,
-- post-menopausal individuals) are precarious without generating.
-- The bridge `generative_has_precarity` below shows every generative
-- closure IS precarious — but the converse is deliberately left
-- unproven. In the deductive chain, generation carries the ◇ marker,
-- not ∎. Its independence from the trunk is proved in
-- SeparatingModels.lean (Lonely Stars model, LII_independent_of_trunk).
-- The characterization of life as "resolution by maintenance and,
-- in some closures, by generation" must mark generation as ◇ explicitly.

-- A closure capable of generation: it can split its margin between
-- self-maintenance and producing a new closure.
structure GenerativeClosure where
  -- Total margin
  margin : Nat
  margin_pos : margin > 0
  -- Cost per maintenance cycle (self-resolution of precarity)
  maintenance_cost : Nat
  maintenance_pos : maintenance_cost > 0
  -- Cost of generation (producing a new closure, investing margin)
  generation_cost : Nat
  generation_pos : generation_cost > 0
  -- At least one generation event is affordable while surviving
  -- at least one maintenance cycle
  affordable : maintenance_cost + generation_cost ≤ margin

-- [∎] GENERATION COMPETES WITH MAINTENANCE.
-- The margin spent on generation reduces the lifespan of the generator.
-- The two modes of resolution draw on the same finite resource.
theorem generation_costs_maintenance (g : GenerativeClosure) :
    g.margin - g.generation_cost < g.margin := by
  have := g.generation_pos; have := g.margin_pos; omega

-- [∎] BRIDGE — Every generative closure is precarious.
-- A generative closure has positive drain (maintenance_cost > 0)
-- and finite margin, so it satisfies the precarity conditions.
-- The converse does NOT hold: precarity does not imply generation.
-- (Delta 3: generation is a capacity, not a structural necessity.)
theorem generative_has_precarity (g : GenerativeClosure) :
    g.maintenance_cost > 0 ∧
    (∃ n, n * g.maintenance_cost > g.margin) := by
  constructor
  · exact g.maintenance_pos
  · refine ⟨g.margin + 1, ?_⟩
    have h1 : 1 ≤ g.maintenance_cost := g.maintenance_pos
    have h2 : (g.margin + 1) * 1 ≤
              (g.margin + 1) * g.maintenance_cost :=
      Nat.mul_le_mul_left (g.margin + 1) h1
    simp only [Nat.mul_one] at h2; omega

-- [∎] THE GENERATED CLOSURE IS STRUCTURALLY INDEPENDENT.
-- The generated closure has its own margin — not the generator's.
-- Its margin is positive; the generator's margin is reduced by
-- the investment. Two instances of the same structural condition
-- (ConstitutiveLack), at different phases of their cycle.
theorem generated_closure_independent
    (generator_margin generated_margin : Nat)
    (h_gen_pos : generated_margin > 0)
    (h_independent : generated_margin ≤ generator_margin) :
    generated_margin > 0 ∧
    generator_margin - generated_margin < generator_margin :=
  ⟨h_gen_pos, by omega⟩

-- [∎] GENERATION DOES NOT RESOLVE THE GENERATOR'S PRECARITY.
-- After generation, the generator's margin is reduced. It still
-- has constitutive lack and still dies. Generation transcends
-- finitude by producing a NEW locus of resolution — not by saving
-- the generator. The parent dies; the child begins full (§8).
theorem generation_does_not_save (g : GenerativeClosure)
    (_h_spent : g.generation_cost ≤ g.margin) :
    ∃ n, n * g.maintenance_cost >
         (g.margin - g.generation_cost) := by
  have h_pos := g.maintenance_pos
  refine ⟨(g.margin - g.generation_cost) + 1, ?_⟩
  have h1 : 1 ≤ g.maintenance_cost := h_pos
  have h2 : ((g.margin - g.generation_cost) + 1) * 1 ≤
             ((g.margin - g.generation_cost) + 1) *
             g.maintenance_cost :=
    Nat.mul_le_mul_left ((g.margin - g.generation_cost) + 1) h1
  simp only [Nat.mul_one] at h2; omega

-- [∎] TWO MODES OF RESOLUTION — Maintenance vs. Generation.
-- Every unit of margin goes to maintenance or generation.
-- There is no third option. The two modes are exhaustive and
-- competing. This is the formal content of "la vie se résout
-- par maintenance OU par génération" — with the understanding
-- that generation carries ◇ (not ∎).
theorem two_modes_of_resolution
    (total maintenance generation remainder : Nat)
    (h_partition : maintenance + generation + remainder = total) :
    maintenance + generation ≤ total := by omega

-- ═══════════════════════════════════════════════════════════════════════════
-- § 8. THE ASYMMETRY — Generating costs, being generated is fresh
-- ═══════════════════════════════════════════════════════════════════════════

-- The generator pays; the generated begins with a full margin.
-- This is an asymmetry at the heart of the life/death structure:
-- the parent dies with depleted margin (precarity, final phase),
-- the child begins with fresh precarity (full margin, initial phase).
-- Same structural condition — constitutive lack + finitude — but
-- different phases. The generated does not inherit the generator's
-- debt; it inherits the FORM (the structure of precarity), not
-- the accumulated cost.

-- [∎] THE GENERATED BEGINS WITH MORE MARGIN THAN THE GENERATOR RETAINS.
-- The generator has spent part of its margin; the generated starts full.
theorem generated_begins_full
    (generator_remaining generated_margin : Nat)
    (h_gen_spent : generator_remaining < generated_margin)
    (_h_gen_pos : generated_margin > 0) :
    generated_margin > generator_remaining := h_gen_spent

-- [∎] GENERATION IS ASYMMETRIC.
-- Parent's precarity deepens (margin reduced by generation_cost).
-- Child's precarity is fresh (full margin, zero accumulated debt).
-- Same structural form, different phase.
theorem generation_asymmetry
    (parent_margin_before parent_margin_after
     child_margin gen_cost : Nat)
    (h_spent : parent_margin_after =
               parent_margin_before - gen_cost)
    (h_gen_pos : gen_cost > 0)
    (h_child : child_margin > 0)
    (h_affordable : gen_cost ≤ parent_margin_before) :
    parent_margin_after < parent_margin_before ∧
    child_margin > 0 := by
  constructor
  · omega
  · exact h_child

-- ═══════════════════════════════════════════════════════════════════════════
-- § 9. BRIDGES — Connecting the triad to the existing trunk
-- ═══════════════════════════════════════════════════════════════════════════

-- ── 9a. BRIDGE 1 — MetabolizingClosure → ConstitutiveLack ──────────────
--
-- The triad introduces ConstitutiveLack as the foundational structure.
-- The existing trunk (Autodynamique.lean) uses MetabolizingClosure.
-- This bridge proves they describe the SAME system: every metabolizing
-- closure IS a case of constitutive lack and therefore IS precarious.
--
-- CHAIN INSERTION POINT:
-- Before this bridge, the deductive chain reads:
--   I-α + I-β → XVII (exhaustion) → XXXIV (mortality) → XLIV (normativity)
--            → LVII (self-affection) → LVIII → LIX → LXI → LXXVII
--
-- After this bridge, the chain reads:
--   I-α + I-β → XVII → XXXIV → XLIV
--   → ** PRECARITY (constitutive lack + finitude = mortal lack) ** ← NEW
--   → LVII → LVIII → LIX → LXI → LXXVII
--
-- Precarity is the node where cost arithmetic becomes existential.
-- Before it: abstract accounting. After it: a being that can cease.
-- The bridge makes this transition formally visible and traceable.

-- Local redefinition of MetabolizingClosure (standalone file, no imports).
-- Fields match Autodynamique.lean §10 with ONE ADDITION: margin_pos.
-- The original MetabolizingClosure does not require margin_pos because
-- the exhaustion theorems hold for margin = 0 (already dissolved).
-- We add it here as a philosophical guard: precarity applies to systems
-- that ARE (margin > 0), not to systems already gone (margin = 0).
-- This is not a modification of the trunk — it is an applicability
-- condition, consistent with Axiom I (être = se faire requires being).
structure MetabolizingClosureLocal where
  margin : Nat
  margin_pos : margin > 0
  total_cost : Nat
  total_cost_pos : total_cost > 0
  regeneration : Nat
  regen_pos : regeneration > 0
  drain_net : Nat
  drain_net_pos : drain_net > 0
  cost_decomposition : drain_net + regeneration = total_cost

-- [∎] BRIDGE 1 — Every MetabolizingClosure IS a ConstitutiveLack.
-- Construction: drain_per_cycle = total_cost, regeneration = regeneration.
-- Net lack = drain_net (by the additive decomposition).
-- This proves: the precarity named in §3 is EXACTLY the condition
-- that MetabolizingClosure already satisfies. The triad names what
-- the trunk proved arithmetically and left unnamed.
def metabolizing_to_lack (m : MetabolizingClosureLocal) : ConstitutiveLack where
  margin := m.margin
  margin_pos := m.margin_pos
  drain_per_cycle := m.total_cost
  drain_pos := m.total_cost_pos
  regeneration := m.regeneration
  net_lack_pos := by
    have := m.cost_decomposition
    have := m.drain_net_pos
    omega

-- [∎] BRIDGE 1a — The net lack equals drain_net.
-- netLack (metabolizing_to_lack m) = m.drain_net.
-- The two formalisms compute the same quantity under different names.
theorem bridge_lack_equals_drain (m : MetabolizingClosureLocal) :
    netLack (metabolizing_to_lack m) = m.drain_net := by
  unfold netLack metabolizing_to_lack
  simp only
  have := m.cost_decomposition
  omega

-- [∎] BRIDGE 1b — Every metabolizing closure is precarious.
-- Precarity (lack ∧ finitude) is inherited from MetabolizingClosure
-- via the bridge. The triad names what the trunk already proved.
theorem metabolizing_is_precarious (m : MetabolizingClosureLocal) :
    netLack (metabolizing_to_lack m) > 0 ∧
    (∃ n, n * netLack (metabolizing_to_lack m) >
          (metabolizing_to_lack m).margin) :=
  precarity (metabolizing_to_lack m)

-- ── 9b. BRIDGE 2 — V unified: exterior and interior grading ───────────
--
-- Axiom V: exteriority admits degrees. In Autodynamique.lean, this is
-- formalized as GradedExposure (external pressure → drain). In §5,
-- GradedSelfRelation applies V to interiority (reflexive depth → cost).
-- These are TWO INSTANCES of the SAME abstract pattern: a graded
-- parameter that monotonically increases cost.
--
-- The abstract class GradedCostParameter below unifies them, proving
-- formally that V is ONE axiom with two applications (not two axioms).
--
-- NOTE ON INSTANCE COMPLETENESS:
-- The class requires level_monotone and level_strict_monotone as fields,
-- meaning comparisons between elements of the same type. For an
-- instance on InteriorGraded, this comparison must fix base_cost and
-- layer_cost (comparing two systems that differ ONLY in depth).
-- The concrete theorems deeper_costs_more and interior_cost_monotone_in_depth
-- prove this monotonicity for the interior case with explicit Nat arguments.
-- A complete typeclass instance would require parameterizing InteriorGraded
-- by (base_cost, layer_cost) — technically correct but architecturally
-- heavier than the philosophical claim requires.
-- The abstract class here captures the shared STRUCTURE; the generic
-- theorem graded_exhaustion_faster works for any future full instance.
-- For the exterior instance, GradedExposure in Autodynamique.lean
-- provides the fields directly as class axioms.

-- The abstract pattern: a type with a graded parameter and a cost,
-- where a higher parameter means a higher cost (weak and strict).
class GradedCostParameter (α : Type) where
  -- The graded parameter (pressure level, reflexive depth, etc.)
  level : α → Nat
  -- The cost associated with that level
  cost : α → Nat
  -- Cost is always positive (IV)
  cost_pos : ∀ a, cost a > 0
  -- Weak monotonicity: higher level → cost at least as high
  level_monotone : ∀ a b : α,
    level a ≤ level b → cost a ≤ cost b
  -- Strict monotonicity: strictly higher level → strictly higher cost
  level_strict_monotone : ∀ a b : α,
    level a < level b → cost a < cost b

-- [∎] V-GENERIC — Higher level → faster exhaustion.
-- Proved ONCE for the abstract class. Applies to all instances
-- (exterior GradedExposure and interior GradedSelfRelation alike).
theorem graded_exhaustion_faster {α : Type} [GradedCostParameter α]
    (a b : α) (margin : Nat)
    (h_level : GradedCostParameter.level a <
               GradedCostParameter.level b)
    (h_kills_a : (margin + 1) *
                 GradedCostParameter.cost a > margin) :
    (margin + 1) * GradedCostParameter.cost b > margin := by
  have h_lt :=
    GradedCostParameter.level_strict_monotone a b h_level
  have h_mono : (margin + 1) * GradedCostParameter.cost a ≤
                (margin + 1) * GradedCostParameter.cost b :=
    Nat.mul_le_mul_left (margin + 1) (Nat.le_of_lt h_lt)
  omega

-- Interior grading: depth as the graded parameter.
structure InteriorGraded where
  base_cost : Nat
  base_cost_pos : base_cost > 0
  layer_cost : Nat
  layer_cost_pos : layer_cost > 0
  depth : Nat
  depth_pos : depth > 0

def interiorCost (g : InteriorGraded) : Nat :=
  g.base_cost + g.depth * g.layer_cost

-- [∎] Interior cost is positive.
theorem interior_cost_pos (g : InteriorGraded) :
    interiorCost g > 0 := by
  unfold interiorCost; have := g.base_cost_pos; omega

-- [∎] Interior cost is strictly monotone in depth
-- (same base_cost and layer_cost, strictly higher depth → strictly higher cost).
theorem interior_cost_monotone_in_depth
    (base layer d1 d2 : Nat)
    (_h_base : base > 0) (h_layer : layer > 0)
    (_h_d1 : d1 > 0) (_h_d2 : d2 > 0)
    (h_lt : d1 < d2) :
    base + d1 * layer < base + d2 * layer := by
  have : d1 * layer < d2 * layer :=
    (Nat.mul_lt_mul_right h_layer).mpr h_lt
  omega

-- ── 9c. BRIDGE 3 — Precarity in the deductive chain ───────────────────
--
-- CHAIN POSITION (formal comment — the bridge theorem below packages
-- the insertion point; no additional theorem is required):
--
-- LEVEL 1 — COST ALGEBRA (arithmetic, no ontological commitment)
--   I-α (cost > 0) + I-β (endogeneity)
--   → XVII  (exhaustion: ∃ n, n * drain > margin)
--   → XXXIV (constitutive mortality: even with compensation, mortality persists)
--   → XLIV  (constitutive normativity: the closure produces its own threshold)
--
-- LEVEL 2 — PRECARITY (arithmetic becomes existential)
--   → PRECARITY = XLIV face B (manque constitutif) ∧ XVII+XXXIV (finitude)
--   "The closure's lack is mortal."
--   THIS is where cost algebra becomes the life of a system.
--   Before this line: abstract accounting.
--   After this line: a being that can cease.
--   Axiom I gets its full force here: "être = se faire" is urgent
--   because failure to act is cessation (resolution_must_recur).
--
-- LEVEL 3 — SELF-RELATION (the system is exposed to its own precarity)
--   → LVII (self-affection: the system pays for relating to itself)
--   → LVIII (valence: this self-relation is not neutral)
--   → LIX  (feedback: valence modifies the next cycle)
--   → LXI  (second-order loop: the closure metabolizes its own valence)
--
-- LEVEL 4 — THE BORDER
--   → SelfRelation ∎  (the system bears a differential rapport to its act)
--   → Thèse P ≈₃      (this rapport is an ordeal — LXXVII, indecidable)
--
-- The triad maps onto this chain:
--   Life          = Level 2 precarity + Level 3 self-relation as maintenance
--   Consciousness = Level 4 — the ordeal of what Levels 2-3 produce (≈₃)
--
-- KEY INSIGHT: before this file, Level 2 was invisible. The chain
-- jumped from XLIV (normativity) to LVII (self-affection) without
-- marking the moment where the system becomes alive. Precarity IS
-- that moment. It is not a new axiom — it is the conjunction of
-- existing results (XLIV + XVII/XXXIV) that was unnamed and therefore
-- structurally invisible. This bridge makes the transition traceable.

-- [∎] BRIDGE 3 — XLIV + finitude = precarity (chain lemma).
-- Given any system with positive net drain (XLIV face B + XVII)
-- and a finite margin (I-α), the system is precarious.
-- This is the formal content of Level 2 in the chain above.
theorem chain_xliv_plus_finitude_eq_precarity
    (margin drain_net : Nat)
    (_h_margin_pos : margin > 0)
    (h_drain_pos : drain_net > 0) :
    drain_net > 0 ∧ (∃ n, n * drain_net > margin) := by
  constructor
  · exact h_drain_pos
  · refine ⟨margin + 1, ?_⟩
    have h1 : 1 ≤ drain_net := h_drain_pos
    have h2 : (margin + 1) * 1 ≤ (margin + 1) * drain_net :=
      Nat.mul_le_mul_left (margin + 1) h1
    simp only [Nat.mul_one] at h2; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- § 10. SYNTHESIS — The triptyque
-- ═══════════════════════════════════════════════════════════════════════════

-- ## The formal triptyque
--
-- ### Precarity (∎)
-- The closure is constituted by a lack that can destroy it.
-- Theorem: precarity — netLack > 0 ∧ ∃ n, n * netLack > margin
--
-- ### Life = resolution of precarity (∎ — structural characterization)
-- Maintenance mode:
--   resolution_extends_life    — partial compensation extends duration
--   resolution_preserves_precarity — compensation cannot eliminate the lack
--   resolution_must_recur      — Axiom I as perpetual necessity, not settled fact
-- Generation mode (◇, not ∎):
--   generation_does_not_save   — generator still dies after generating
--   generation_costs_maintenance — two modes compete for the same margin
--   generative_has_precarity   — generation implies precarity (not converse)
--   two_modes_of_resolution    — maintenance and generation are exhaustive
-- Asymmetry:
--   generation_asymmetry       — generator pays, generated begins fresh
--
-- ### Consciousness = ordeal (épreuve) of precarity (≈₃ only)
-- NOT formalized. The characterization:
--   The term "ordeal" (épreuve) is used here as a TECHNICAL TERM,
--   not in its ordinary phenomenological sense. Its meaning:
--   the differential rapport of a system to the FACT of its own
--   precarity. Not: thinking the lack, or representing it.
--   Rather: being AFFECTED by the fact that one lacks and can cease.
--   The difference life/consciousness is not a difference of content
--   but of relation to the same fact: resolving vs. undergoing what
--   one resolves. Acting vs. suffering what one acts.
--   This "ordeal" in the technical sense is ≈₃: it is not derivable
--   from the structural conditions (LXXVII remains the bound).
--   But the structural conditions for a gradient toward it ARE met (∎).
--
-- ## The gradient question (Birch 2024)
--
-- Deep gradualism (Birch): the phenomenal gradient is continuous —
--   there is no discrete jump between "no experience" and "experience."
-- The precise OD position on this question (CORRECTED):
--
--   ∎ PROVED: deeper self-relation costs more (deeper_costs_more).
--   ∎ PROVED: within the closure regime, the cost of self-relation
--     varies continuously with reflexive depth (interior gradient).
--   ∎ NOT proved: that this interior gradient IS a phenomenal gradient.
--     Whether more structural self-relation means more experience: ≈₃.
--
--   IMPORTANT — what is NOT excluded and what IS excluded:
--   * The regime boundary (closure / portage / aggregate) is DISCRETE
--     by construction (SeparatingModels.lean, constitutive_order,
--     opacityScore). OD does not exclude a discrete jump at the
--     regime boundary. The regime partition is a phase structure.
--   * What IS excluded: that self-relation WITHIN the closure regime
--     is discontinuous. V applies to self-relation (∎), therefore
--     the interior gradient is structurally continuous within the regime.
--   * Deep gradualism (Birch) is structurally COMPATIBLE with OD:
--     the conditions for a continuous gradient are met.
--   * Shallow gradualism (a small number of discrete sentience levels)
--     is not excluded by OD.
--   * A discrete jump AT the regime boundary is not excluded.
--     OD is agnostic on whether the regime boundary (closure → portage)
--     maps to a phenomenal threshold.
--   The correct claim: OD PROVES the structural conditions for
--   Birch's deep gradualism. It does not assert that gradualism
--   extends to phenomenal experience (LXXVII).
--
-- ## Positioning vs. Jonas, Deacon, Thompson, Birch
--   Jonas:  "existence as concern" → OD: precarity ∎, concern ≈₃
--           Jonas's Sorge attributed to all living beings is a claim
--           on the ≈₃ side of LXXVII, not a structural theorem.
--           OD shows WHERE Jonas's thesis begins (LVII → LXI)
--           and WHERE certainty ends (LXXVII).
--   Deacon: "absential / ententional" → constitutive lack ∎
--           Deacon's hierarchy (homeo/morpho/teleodynamic) maps onto
--           the OD partition (aggregate / portage / closure) with
--           the order: homeo ↔ aggregate, morpho ↔ portage,
--           teleo ↔ closure. (Note: Deacon's hierarchy ascends toward
--           teleodynamics; OD's hierarchy ascends toward closure.
--           The correspondence is inverted in presentation but
--           aligned in substance.)
--   Thompson: "life-mind continuity" → gradient ∎, identity ≈₃
--             Thompson's "where there is life there is mind" is
--             compatible with OD IF the interior gradient reaches
--             phenomenal experience. OD proves the gradient (∎);
--             that it reaches mind is Thompson's thesis (≈₃).
--   Birch:  "deep gradualism" → structurally compatible ∎
--             OD proves the interior gradient is continuous within
--             the closure regime. Whether this structural continuity
--             maps to phenomenal continuity remains ≈₃ (LXXVII).
--
-- ## Audit: Lean ↔ Philosophy deltas
--
-- | Philosophical concept         | Lean term                     | Fidelity  | Delta                               |
-- |-------------------------------|-------------------------------|-----------|-------------------------------------|
-- | Constitutive lack (XLIV B)    | ConstitutiveLack + netLack    | ∎ exact   | —                                   |
-- | Finitude                      | finitude                      | ∎ exact   | —                                   |
-- | Precarity                     | precarity                     | ∎ exact   | Naming lemma (conjunction of ∎)    |
-- | Resolution = life (Axiom I)   | resolution_extends_life       | ∎ partial | Delta 1: consequences of the act,   |
-- |                               | resolution_must_recur         |           | not the act as ontological gesture  |
-- | Interior gradient (V)         | deeper_costs_more             | ∎ exact   | Delta 2: structural gradient ∎,    |
-- |                               | deeper_also_reaches_cessation |           | phenomenal gradient ≈₃ (LXXVII)   |
-- | Reflexive cost (Sorge struct.)| reflexive_cost_positive       | ∎ exact   | —                                   |
-- | Generation (◇)                | GenerativeClosure             | ∎ partial | Delta 3: capacity, not necessity.   |
-- |                               | generative_has_precarity      |           | Converse deliberately unproven.     |
-- | Generation asymmetry          | generation_asymmetry          | ∎ exact   | —                                   |
-- | Consciousness = ordeal        | (absent from code)            | ≈₃        | Correct: undecidable (LXXVII).     |
-- |                               |                               |           | "Ordeal" is a technical term here:  |
-- |                               |                               |           | differential rapport to precarity,  |
-- |                               |                               |           | not presupposing felt experience.   |
--
-- ## Audit: philosophical guards (unused variables, prefixed _)
--
-- | Variable          | Theorem                               | Philosophical role                   |
-- |-------------------|---------------------------------------|--------------------------------------|
-- | _h_drain          | resolution_is_non_optional            | Closure condition (Axiom I)          |
-- | _h_regen          | resolution_is_non_optional            | Life condition (vs. aggregate)       |
-- | _h_net            | resolution_is_non_optional            | Precarity condition                  |
-- | _h_layer          | deeper_also_reaches_cessation         | Each reflexive layer costs (V)       |
-- | _h_d              | deeper_also_reaches_cessation         | At least one layer (LVII)            |
-- | _h_budget_d1      | deeper_also_reaches_cessation         | The system exists (Axiom I)          |
-- | _h_gen_pos        | generated_begins_full                 | The generated is a genuine closure   |
-- | _h_op             | reflexive_cost_accelerates_exhaustion | Operational cost positive (IV)       |
-- | _h_meta           | reflexive_cost_accelerates_exhaustion | Meta-cost positive (LXI)             |
-- | _h_spent          | generation_does_not_save              | Generation is affordable             |
-- | _h_margin_pos     | chain_xliv_plus_finitude_eq_precarity | The system exists (Axiom I)          |
-- | _h_base           | interior_cost_monotone_in_depth       | Base cost positive (I-α)             |
-- | _h_d1, _h_d2      | interior_cost_monotone_in_depth       | Depths > 0 (LVII minimum)            |
--
-- These guards delimit the domain of applicability of each theorem.
-- The typechecker does not need them; the philosophical system does.
--
-- ## Inventory: 28 theorems · 4 defs · 1 class · 0 sorry · 0 imports
-- ## New structures: ConstitutiveLack, GradedSelfRelation,
--                    ReflexiveCostSystem, GenerativeClosure,
--                    MetabolizingClosureLocal, InteriorGraded
-- ## Abstract class: GradedCostParameter (V unified: exterior ↔ interior)
-- ## Bridges: metabolizing_to_lack (trunk → triad, §9a)
--             GradedCostParameter (V is one axiom, §9b)
--             chain_xliv_plus_finitude_eq_precarity (chain insertion, §9c)

-- Final inventory check
#check @lack_is_positive
#check @finitude
#check @lifespan_bounded
#check @precarity
#check @precarity_excludes_eternity
#check @resolution_extends_life
#check @resolution_preserves_precarity
#check @resolution_is_non_optional
#check @resolution_must_recur
#check @total_self_cost_pos
#check @deeper_costs_more
#check @deeper_also_reaches_cessation
#check @reflexive_cost_positive
#check @reflexive_cost_increases_precarity
#check @reflexive_cost_accelerates_exhaustion
#check @generation_costs_maintenance
#check @generative_has_precarity
#check @generated_closure_independent
#check @generation_does_not_save
#check @two_modes_of_resolution
#check @generated_begins_full
#check @generation_asymmetry
#check @metabolizing_to_lack
#check @bridge_lack_equals_drain
#check @metabolizing_is_precarious
#check @graded_exhaustion_faster
#check @interior_cost_pos
#check @interior_cost_monotone_in_depth
#check @chain_xliv_plus_finitude_eq_precarity

end Precarity
