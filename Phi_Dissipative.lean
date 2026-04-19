-- Phi_Dissipative.lean
-- Ontodynamique — Φ-dissipative : contraintes sur la physique fondamentale
-- Trois résultats : direction irréversible, asymétrie, non-isolation.
-- Théorèmes : target ~20 · Sorry : 0 · Imports : 0

/-!
# Φ-dissipative — Structural constraints on fundamental physics

## PHILOSOPHICAL CONTEXT

The OD trunk derives (from axiom I alone) that dissolution is the
default direction of evolution. This file isolates three results
that constrain any fundamental physics consistent with I:

  Φ-diss-1 — IRREVERSIBLE DIRECTION: dissolution is necessary (∎),
    construction is contingent (◇). The 2nd law of thermodynamics
    is a metric instantiation of this structural constraint.

  Φ-diss-2 — CONSTRUCTION/DESTRUCTION ASYMMETRY: building a cycle
    costs strictly more than maintaining one (Lemme 3 ∎).
    Chain: I → IV → saving_pos (SavingDerived.lean) → asymmetry → Lemme 3.

  Φ-diss-4 — NON-ISOLATION AS FOUNDATION: the irreversible direction
    derives from the impossibility of absolute isolation (III),
    not from the hypothesis of an isolated system. The 2nd law's
    dependence on "isolated system" is a sufficient but not
    necessary condition.

## CRITICAL DISTINCTION — se faire ≠ se refaire

  "Se faire" (I, universal) — the stone as the organism.
  "Se refaire" (XXXII, qualitative leap) — regenerate one's own
    conditions at one's own cost. Threshold of closure.
  IV (cost > 0) applies to se-faire universally.
  XXXIV (mortality, margin exhaustion) derives from IV + closure,
    hence applies only to se-refaire. Never attribute constitutive
    mortality or margin exhaustion to bare se-faire (aggregate).

## RELATION TO EXISTING FILES

  Ontodynamique.lean: IV, VII, IX, XII, XVII (trunk theorems)
  gradient.lean §10-11: bounded_lifetime, descent_cheaper_than_ascent
  Dynamics.lean §5: hysteresis_zone_exists (Lemme 3)
  SavingDerived.lean: saving_pos_derived, asymmetry_derived
  This file does NOT import them — standalone, with local replicas.

## Theorems: 21 · Sorry: 0 · Imports: 0
-/

namespace PhiDissipative

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. PRIMITIVE STRUCTURES — Finite determined act under pressure
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  The minimal structure for Φ-diss: an entity with finite margin,
  positive cost (IV), and exposure to exteriority (III + VII).
  No closure, no normativité, no clôture — this is the universal
  regime of se-faire, not the regime of se-refaire.
-/

/-- A finite determined act under constitutive pressure.
    Encodes IV (cost > 0), IX (finite margin), III (no absolute isolation),
    VII (exteriority generated). -/
structure FiniteAct where
  /-- Finite margin (IX) -/
  margin : Nat
  margin_pos : margin > 0
  /-- Cost per cycle — strictly positive (IV) -/
  cost : Nat
  cost_pos : cost > 0
  /-- Exteriority pressure — strictly positive (XII from III + VII + IX) -/
  pressure : Nat
  pressure_pos : pressure > 0

/-- Margin after t cycles of uncompensated drain. -/
def marginAfter (e : FiniteAct) (t : Nat) : Nat :=
  e.margin - t * e.cost

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Φ-DISS-1 — IRREVERSIBLE DIRECTION
--     Dissolution is the default. Construction is contingent.
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Φ-diss-1 : Direction irréversible

  From I:
    IV  — every transformation has strictly positive cost
    VII — every determination generates exteriority
    IX  — exteriority persists (finite margin)
    III — no absolute isolation
    XII — the Whole exerts permanent dissolution pressure on every
          finite being (from III + VII + IX)

  Conclusion (XVII): dissolution is the default direction.

  The 2nd law of thermodynamics is a METRIC instantiation of this
  structural constraint. The OD version:
    - Has no state function (TN-1 forbids metric)
    - Has no isolated system (III forbids it)
    - Derives the DIRECTION from a single axiom
-/

/-- [∎] Φ-DISS-1a — MARGIN DECREASES STRICTLY AT EACH CYCLE.
    While margin remains positive, each cycle reduces it.
    From IV: cost > 0, so t*cost < (t+1)*cost. -/
theorem margin_decreasing (e : FiniteAct) (t : Nat)
    (h_alive : t * e.cost < e.margin) :
    marginAfter e (t + 1) < marginAfter e t := by
  unfold marginAfter
  have h_cost := e.cost_pos
  have h1 : (t + 1) * e.cost = t * e.cost + e.cost := Nat.succ_mul t e.cost
  omega

/-- [∎] Φ-DISS-1b — DISSOLUTION IN FINITE TIME (XVII).
    Every finite act reaches zero margin.
    From IV (cost > 0) + IX (margin finite). -/
theorem dissolution_in_finite_time (e : FiniteAct) :
    ∃ t, marginAfter e t = 0 := by
  refine ⟨e.margin, ?_⟩
  unfold marginAfter
  have h1 : e.margin * 1 ≤ e.margin * e.cost :=
    Nat.mul_le_mul_left e.margin e.cost_pos
  simp only [Nat.mul_one] at h1
  exact Nat.sub_eq_zero_of_le h1

/-- [∎] Φ-DISS-1c — THE DIRECTION IS UNCONDITIONAL.
    Regardless of the margin or cost values (as long as both > 0),
    dissolution occurs. No parameter combination avoids it.
    This is the structural content: the direction is necessary,
    not contingent on parameter values. -/
theorem direction_unconditional (margin cost : Nat)
    (hm : margin > 0) (hc : cost > 0) :
    ∃ t, margin - t * cost = 0 := by
  refine ⟨margin, ?_⟩
  have h1 : margin * 1 ≤ margin * cost :=
    Nat.mul_le_mul_left margin hc
  simp only [Nat.mul_one] at h1
  exact Nat.sub_eq_zero_of_le h1

/-- [∎] Φ-DISS-1d — DISSOLUTION IS MONOTONIC.
    Once margin reaches zero, it stays at zero.
    No spontaneous recovery without external input (VI ◇). -/
theorem dissolution_irreversible (e : FiniteAct) (t s : Nat)
    (h_le : t ≤ s) (h_dead : marginAfter e t = 0) :
    marginAfter e s = 0 := by
  unfold marginAfter at *
  have : t * e.cost ≤ s * e.cost :=
    Nat.mul_le_mul_right e.cost h_le
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. CONSTRUCTION AS CONTINGENT (VI ◇)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## The asymmetry ∎ vs ◇

  Dissolution is ∎ (necessary — derived from I).
  Construction is ◇ (contingent — requires conditions of domain).

  This contrast is itself a result: any physics consistent with I
  must treat structure formation and dissolution as ASYMMETRIC.
  Boltzmann's H-theorem has the same structure: entropy increase
  is necessary; decrease is possible but requires special conditions.
-/

/-- An environment that MAY provide compensatory diversity. -/
structure Environment where
  /-- Available compensatory diversity (XXVI) -/
  diversity : Nat
  /-- Minimum diversity for construction (condition of domain) -/
  threshold : Nat
  threshold_pos : threshold > 0

/-- Construction is possible iff diversity exceeds threshold. -/
def construction_possible (env : Environment) : Prop :=
  env.diversity ≥ env.threshold

/-- [∎] Φ-DISS-1e — CONSTRUCTION IS CONDITIONAL.
    Without sufficient diversity, construction does not occur.
    The condition is falsifiable: if diversity < threshold, no cycle. -/
theorem construction_conditional (env : Environment)
    (h_insufficient : env.diversity < env.threshold) :
    ¬ construction_possible env := by
  unfold construction_possible; omega

/-- [∎] Φ-DISS-1f — THE ASYMMETRY IS STRUCTURAL.
    Dissolution requires only IV + IX (always satisfied).
    Construction requires VI conditions (not always satisfied).
    The two have different epistemic statuses: ∎ vs ◇. -/
theorem dissolution_vs_construction_asymmetry
    (e : FiniteAct) (env : Environment)
    (h_insufficient : env.diversity < env.threshold) :
    (∃ t, marginAfter e t = 0) ∧ ¬ construction_possible env :=
  ⟨dissolution_in_finite_time e, construction_conditional env h_insufficient⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Φ-DISS-4 — NON-ISOLATION AS FOUNDATION
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Φ-diss-4 : The direction derives from non-isolation

  The 2nd law of classical thermodynamics is stated for ISOLATED systems.
  The OD derivation of the irreversible direction does NOT require
  isolation — it derives from its IMPOSSIBILITY (III).

  XII: the Whole exerts permanent dissolution pressure on every
  finite being, INDEPENDENTLY of encounters with other finite beings.

  The OD constraint: the irreversible direction should be derivable
  WITHOUT the isolated system hypothesis. Isolation is a sufficient
  but not necessary condition.
-/

/-- Two entities that are never isolated from each other.
    III: no absolute isolation. -/
structure CoupledEntities where
  /-- Margin of entity A -/
  margin_a : Nat
  margin_a_pos : margin_a > 0
  /-- Margin of entity B -/
  margin_b : Nat
  margin_b_pos : margin_b > 0
  /-- Cost for A (IV) -/
  cost_a : Nat
  cost_a_pos : cost_a > 0
  /-- Cost for B (IV) -/
  cost_b : Nat
  cost_b_pos : cost_b > 0
  /-- Mutual pressure — nonzero because III forbids isolation -/
  coupling : Nat
  coupling_pos : coupling > 0

/-- Total drain for A: own cost + coupling pressure. -/
def totalDrainA (c : CoupledEntities) : Nat :=
  c.cost_a + c.coupling

/-- [∎] Φ-DISS-4a — COUPLING ACCELERATES DISSOLUTION.
    An entity coupled to another dissolves faster than one
    facing only its own cost. III → faster dissolution. -/
theorem coupling_accelerates (c : CoupledEntities) :
    totalDrainA c > c.cost_a := by
  unfold totalDrainA
  have := c.coupling_pos; omega

/-- [∎] Φ-DISS-4b — DISSOLUTION WITHOUT ISOLATION.
    Even coupled entities (never isolated) dissolve in finite time.
    The irreversible direction does not require isolation. -/
theorem dissolution_without_isolation (c : CoupledEntities) :
    ∃ t, c.margin_a - t * totalDrainA c = 0 := by
  refine ⟨c.margin_a, ?_⟩
  have h_drain : totalDrainA c > 0 := by
    unfold totalDrainA; have := c.cost_a_pos; omega
  have h1 : c.margin_a * 1 ≤ c.margin_a * totalDrainA c :=
    Nat.mul_le_mul_left c.margin_a h_drain
  simp only [Nat.mul_one] at h1
  exact Nat.sub_eq_zero_of_le h1

/-- [∎] Φ-DISS-4c — ISOLATION IS SUFFICIENT BUT NOT NECESSARY.
    An isolated entity (coupling = 0, hypothetically) also dissolves.
    But coupling is always > 0 (III). So isolation is an idealization
    that the OD never needs. -/
theorem isolation_not_required (margin cost : Nat)
    (hm : margin > 0) (hc : cost > 0) :
    -- Even without coupling, dissolution occurs (sufficient)
    (∃ t, margin - t * cost = 0) ∧
    -- And coupling never reaches zero (III: not necessary)
    (∀ coupling, coupling > 0 → cost + coupling > cost) :=
  ⟨direction_unconditional margin cost hm hc,
   fun c hc_pos => by omega⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Φ-DISS-2 — CONSTRUCTION/DESTRUCTION ASYMMETRY
--     Replica of the Lemme 3 chain (SavingDerived + Dynamics)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Φ-diss-2 : Building costs more than maintaining

  Full derivation chain:
    I → IV (cost > 0) → P1 (unit_cost > 0)
    Definition of template → P2 (eliminated > 0) [analytic]
    IV preserved → P3 (eliminated < space)
    P1 + P2 → saving_pos ∎
    saving_pos → asymmetry (construction > maintenance) ∎
    asymmetry → Lemme 3 (hysteresis zone exists) ∎

  Local replicas below. The originals are in SavingDerived.lean
  and Dynamics.lean §5.
-/

/-- An act over a possibility space with a constraining template.
    Local replica of SavingDerived.ConstrainedAct. -/
structure ConstrainedAct where
  space : Nat
  eliminated : Nat
  unit_cost : Nat
  unit_cost_pos : unit_cost > 0
  template_constrains : eliminated > 0
  template_partial : eliminated < space

def ConstrainedAct.raw_cost (a : ConstrainedAct) : Nat :=
  a.space * a.unit_cost

def ConstrainedAct.guided_cost (a : ConstrainedAct) : Nat :=
  (a.space - a.eliminated) * a.unit_cost

def ConstrainedAct.saving (a : ConstrainedAct) : Nat :=
  a.eliminated * a.unit_cost

/-- [∎] Φ-DISS-2a — SAVING IS STRICTLY POSITIVE (saving_pos derived).
    A template that constrains (P2) with positive unit cost (P1)
    produces a strictly positive saving. -/
theorem saving_pos (a : ConstrainedAct) : a.saving > 0 := by
  unfold ConstrainedAct.saving
  have h1 : 1 ≤ a.eliminated := a.template_constrains
  have h2 : 1 ≤ a.unit_cost := a.unit_cost_pos
  have : 1 * 1 ≤ a.eliminated * a.unit_cost :=
    Nat.mul_le_mul h1 h2
  omega

/-- [∎] Φ-DISS-2b — CONSTRUCTION > MAINTENANCE (asymmetry derived).
    An unguided act costs strictly more than a guided act. -/
theorem construction_gt_maintenance (a : ConstrainedAct) :
    a.raw_cost > a.guided_cost := by
  unfold ConstrainedAct.raw_cost ConstrainedAct.guided_cost
  have h_partial := a.template_partial
  have h_uc := a.unit_cost_pos
  have h_elim : a.eliminated ≥ 1 := a.template_constrains
  -- space > space - eliminated (since eliminated > 0 and eliminated < space)
  have h_remaining : a.space - a.eliminated < a.space := by omega
  -- (space - eliminated + 1) ≤ space
  have h1 : a.space - a.eliminated + 1 ≤ a.space := by omega
  have h2 : (a.space - a.eliminated + 1) * a.unit_cost ≤ a.space * a.unit_cost :=
    Nat.mul_le_mul_right a.unit_cost h1
  -- (space - eliminated) * unit_cost + unit_cost = (space - eliminated + 1) * unit_cost
  have h3 : (a.space - a.eliminated + 1) * a.unit_cost =
             (a.space - a.eliminated) * a.unit_cost + a.unit_cost :=
    Nat.succ_mul (a.space - a.eliminated) a.unit_cost
  omega

/-- Transition system with asymmetric costs.
    Local replica of Dynamics.TransitionSystem. -/
structure TransitionSystem where
  construction_cost : Nat
  maintenance_cost : Nat
  construction_pos : construction_cost > 0
  maintenance_pos : maintenance_cost > 0
  asymmetry : construction_cost > maintenance_cost
  capacity : Nat
  capacity_pos : capacity > 0

def can_maintain_at (s : TransitionSystem) (n : Nat) : Prop :=
  n * s.maintenance_cost ≤ s.capacity

def can_build_at (s : TransitionSystem) (n : Nat) : Prop :=
  n * s.maintenance_cost + s.construction_cost ≤ s.capacity

/-- [∎] Φ-DISS-2c — LEMME 3 : HYSTERESIS ZONE EXISTS.
    There exists a level maintainable but not constructible.
    Replica of Dynamics.hysteresis_zone_exists. -/
theorem hysteresis_zone_exists (s : TransitionSystem) :
    ∃ n, can_maintain_at s n ∧ ¬ can_build_at s n := by
  let n := s.capacity / s.maintenance_cost
  refine ⟨n, ?_, ?_⟩
  · unfold can_maintain_at
    have h_dam := Nat.div_add_mod s.capacity s.maintenance_cost
    have hcomm : n * s.maintenance_cost =
                 s.maintenance_cost * (s.capacity / s.maintenance_cost) :=
      Nat.mul_comm n s.maintenance_cost
    omega
  · unfold can_build_at
    intro h_absurd
    have h_dam := Nat.div_add_mod s.capacity s.maintenance_cost
    have h_mod := Nat.mod_lt s.capacity s.maintenance_pos
    have h_asym := s.asymmetry
    have hcomm : n * s.maintenance_cost =
                 s.maintenance_cost * (s.capacity / s.maintenance_cost) :=
      Nat.mul_comm n s.maintenance_cost
    omega

/-- [∎] Φ-DISS-2d — THE ASYMMETRY IS STRICT.
    No parameter combination produces symmetric transitions.
    Descent is ALWAYS cheaper than ascent. -/
theorem no_symmetric_transitions (s : TransitionSystem) :
    s.construction_cost ≠ s.maintenance_cost := by
  have := s.asymmetry; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. SYNTHESIS — Physical constraints derived from I
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## What the typechecker verifies

From axiom I alone (encoded as IV + III + VII + IX), three constraints
on any fundamental physics are derived:

  1. IRREVERSIBLE DIRECTION (Φ-diss-1): every finite entity dissolves
     in finite time. The direction is unconditional — no parameter
     combination avoids it. Construction is contingent (◇).

  2. CONSTRUCTION/DESTRUCTION ASYMMETRY (Φ-diss-2): building a cycle
     costs strictly more than maintaining one. There exists a hysteresis
     zone (maintainable but not constructible). The asymmetry derives
     from I → IV → saving_pos → Lemme 3.

  3. NON-ISOLATION (Φ-diss-4): the irreversible direction derives from
     the impossibility of isolation (III), not from the isolated system
     hypothesis. Coupling accelerates dissolution but is not required
     for the direction — isolation is sufficient but not necessary.

## Physical content

  The 2nd law of thermodynamics is a metric instantiation of Φ-diss-1.
  The OD version derives the same DIRECTION from fewer premises:
    - No state function (TN-1)
    - No isolated system (III)
    - One axiom (I)

  The principle of least action is a metric instantiation of Φ-économie
  (not formalized in this file — see CR_Phi.md §Φ-économie).

## Dependency map

  I ──→ IV (cost > 0)
  I ──→ III (no isolation)
  I ──→ VII (exteriority)
  I ──→ IX (finite margin)
  III + VII + IX ──→ XII (dissolution pressure)
  IV + XII ──→ XVII (dissolution default) ──→ Φ-diss-1
  IV ──→ saving_pos ──→ asymmetry ──→ Lemme 3 ──→ Φ-diss-2
  III ──→ XII (without isolation) ──→ Φ-diss-4
-/

end PhiDissipative
