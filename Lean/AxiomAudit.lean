/-!
# TEST 1 — Inter-axiom independence (I, IV, V)

The three posited axioms of the Ontodynamique system:
  I   = I-α (self-grounding) ∧ I-β (being=doing)
  IV  = every act has a positive cost
  V   = exteriority pressure (positive drain, finite margin)

Main result: the axioms are NOT all independent in the strict sense.
Two implications are FORCED by the formal structure:

  I-β₂ (cost > recovery) → IV (cost > 0)     [since recovery : Nat ≥ 0]
  I-β₃ (ops*soc ≤ margin, ops>0, soc>0) → I-α (margin > 0)

Consequence: full I ⟹ IV. IV is therefore a corollary of I, not
an independent axiom. This is philosophically correct: if being is
doing (I-β), then every act costs (IV). Axiom IV makes explicit
what is already contained in I.

This file proves:
  §A  Forced implications (2 theorems)
  §B  Independence of what CAN be separated (9 models, 27 theorems)
  §C  Synthesis

Theorems: 41
Sorry: 0
Imports: none
-/

namespace InterAxiomIndependence

-- ═══════════════════════════════════════════════════════════════════════════
-- Unified structure and predicates
-- ═══════════════════════════════════════════════════════════════════════════

/-- System carrying all fields needed for the three axioms. -/
structure TestSystem where
  margin : Nat
  cost : Nat
  drain : Nat
  -- I-β₁ (decomposition)
  total_cost : Nat
  drain_net : Nat
  regeneration : Nat
  -- I-β₂ (gradient endogeneity)
  recovery : Nat
  -- I-β₃ (reflexivity)
  self_op_cost : Nat
  operations : Nat

-- ── Predicates ──

/-- I-α: self-grounding — the system has a positive margin. -/
def has_I_alpha (s : TestSystem) : Prop := s.margin > 0

/-- I-β₁: additive decomposition + regeneration. -/
def has_I_beta1 (s : TestSystem) : Prop :=
  s.drain_net + s.regeneration = s.total_cost ∧ s.regeneration > 0

/-- I-β₂: gradient endogeneity (cost > recovery). -/
def has_I_beta2 (s : TestSystem) : Prop := s.cost > s.recovery

/-- I-β₃: reflexivity (the system operates on itself). -/
def has_I_beta3 (s : TestSystem) : Prop :=
  s.operations * s.self_op_cost ≤ s.margin ∧
  s.operations > 0 ∧ s.self_op_cost > 0

/-- Full I-β: all three components. -/
def has_I_beta (s : TestSystem) : Prop :=
  has_I_beta1 s ∧ has_I_beta2 s ∧ has_I_beta3 s

/-- Full I: self-grounding + being=doing. -/
def has_I (s : TestSystem) : Prop := has_I_alpha s ∧ has_I_beta s

/-- IV: every act has a positive cost. -/
def has_IV (s : TestSystem) : Prop := s.cost > 0

/-- V: exteriority pressure (positive drain). -/
def has_V (s : TestSystem) : Prop := s.drain > 0

-- Decidable instances for `decide` on concrete models
instance (s : TestSystem) : Decidable (has_I_alpha s) :=
  inferInstanceAs (Decidable (s.margin > 0))
instance (s : TestSystem) : Decidable (has_I_beta1 s) :=
  inferInstanceAs (Decidable (s.drain_net + s.regeneration = s.total_cost ∧ s.regeneration > 0))
instance (s : TestSystem) : Decidable (has_I_beta2 s) :=
  inferInstanceAs (Decidable (s.cost > s.recovery))
instance (s : TestSystem) : Decidable (has_I_beta3 s) :=
  inferInstanceAs (Decidable
    (s.operations * s.self_op_cost ≤ s.margin ∧ s.operations > 0 ∧ s.self_op_cost > 0))
instance (s : TestSystem) : Decidable (has_IV s) :=
  inferInstanceAs (Decidable (s.cost > 0))
instance (s : TestSystem) : Decidable (has_V s) :=
  inferInstanceAs (Decidable (s.drain > 0))
instance (s : TestSystem) : Decidable (has_I_beta s) :=
  inferInstanceAs (Decidable (has_I_beta1 s ∧ has_I_beta2 s ∧ has_I_beta3 s))
instance (s : TestSystem) : Decidable (has_I s) :=
  inferInstanceAs (Decidable (has_I_alpha s ∧ has_I_beta s))

-- ═══════════════════════════════════════════════════════════════════════════
-- §A. FORCED IMPLICATIONS — what CANNOT be separated
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Result A: two structural implications

These theorems show that the formal encoding FORCES certain relations.
This is not a defect — it is a property of the system: IV is contained
in I-β₂, and I-α is contained in I-β₃.
-/

/-- [∎] I-β₂ IMPLIES IV.
    If cost > recovery (Nat ≥ 0), then cost > 0.
    Gradient endogeneity contains cost positivity. -/
theorem beta2_implies_IV (s : TestSystem) (h : has_I_beta2 s) :
    has_IV s := by
  unfold has_I_beta2 at h; unfold has_IV; omega

/-- [∎] I-β₃ IMPLIES I-α.
    If ops * soc ≤ margin and ops > 0 and soc > 0, then margin > 0.
    Reflexivity contains self-grounding. -/
theorem beta3_implies_I_alpha (s : TestSystem) (h : has_I_beta3 s) :
    has_I_alpha s := by
  unfold has_I_beta3 at h; unfold has_I_alpha
  obtain ⟨h_le, h_ops, h_soc⟩ := h
  have h_prod : s.operations * s.self_op_cost > 0 := by
    have : 1 ≤ s.operations := h_ops
    have : 1 ≤ s.self_op_cost := h_soc
    have : 1 * 1 ≤ s.operations * s.self_op_cost :=
      Nat.mul_le_mul ‹1 ≤ s.operations› ‹1 ≤ s.self_op_cost›
    omega
  omega

/-- [∎] Corollary: full I implies IV.
    IV is not an independent axiom — it is already contained in I. -/
theorem I_implies_IV (s : TestSystem) (h : has_I s) :
    has_IV s := by
  unfold has_I at h
  obtain ⟨_, _, h_beta2, _⟩ := h
  exact beta2_implies_IV s h_beta2

/-- [∎] Corollary: full I-β implies I-α (internal redundancy).
    I-β₃ already provides I-α. -/
theorem I_beta_implies_I_alpha (s : TestSystem) (h : has_I_beta s) :
    has_I_alpha s := by
  unfold has_I_beta at h
  obtain ⟨_, _, h_beta3⟩ := h
  exact beta3_implies_I_alpha s h_beta3

-- ═══════════════════════════════════════════════════════════════════════════
-- §B. SEPARATING MODELS — what CAN be separated
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Result B: independence map

Since I ⟹ IV, the relevant question is not "are I, IV, V independent?"
(answer: no). The question is:
  (1) Are I-α alone, IV alone, V alone mutually independent?
  (2) Does I-β (full or partial) introduce dependencies?
  (3) Which combinations are realizable?

We exhibit 9 models covering the relevant combinations.
-/

-- ── B1: V alone (no I-α, no IV) ──

/-- B1a — V alone, without I-α or IV.
    Minimal witness: margin=0, positive drain. -/
def model_V_only : TestSystem :=
  { margin := 0, cost := 0, drain := 5,
    total_cost := 0, drain_net := 0, regeneration := 0,
    recovery := 0, self_op_cost := 0, operations := 0 }

theorem v_only_has_V      : has_V model_V_only      := by decide
theorem v_only_not_IV     : ¬has_IV model_V_only     := by decide
theorem v_only_not_Ialpha : ¬has_I_alpha model_V_only := by decide

/-- B1b — V without full I (I-β absent), but with I-α.
    Philosophically: a rock under erosion — positive margin,
    active drain, but no founding act (cost = 0 → no IV, no I-β). -/
def model_V_without_full_I : TestSystem :=
  { margin := 10, cost := 0, drain := 3,
    total_cost := 0, drain_net := 0, regeneration := 0,
    recovery := 0, self_op_cost := 0, operations := 0 }

theorem v_no_fullI_has_V      : has_V model_V_without_full_I      := by decide
theorem v_no_fullI_not_IV     : ¬has_IV model_V_without_full_I     := by decide
theorem v_no_fullI_has_Ialpha : has_I_alpha model_V_without_full_I  := by decide
theorem v_no_fullI_not_I      : ¬has_I model_V_without_full_I      := by native_decide

-- ── B2: IV alone (no I-α, no V) ──

/-- Positive cost, but margin=0 and drain=0. -/
def model_IV_only : TestSystem :=
  { margin := 0, cost := 5, drain := 0,
    total_cost := 0, drain_net := 0, regeneration := 0,
    recovery := 0, self_op_cost := 0, operations := 0 }

theorem iv_only_has_IV : has_IV model_IV_only := by decide
theorem iv_only_not_I_alpha : ¬has_I_alpha model_IV_only := by decide
theorem iv_only_not_V : ¬has_V model_IV_only := by decide

-- ── B3: I-α alone (no IV, no V) ──

/-- Positive margin, but cost=0 and drain=0. -/
def model_I_alpha_only : TestSystem :=
  { margin := 10, cost := 0, drain := 0,
    total_cost := 0, drain_net := 0, regeneration := 0,
    recovery := 0, self_op_cost := 0, operations := 0 }

theorem ia_only_has_I_alpha : has_I_alpha model_I_alpha_only := by decide
theorem ia_only_not_IV : ¬has_IV model_I_alpha_only := by decide
theorem ia_only_not_V : ¬has_V model_I_alpha_only := by decide

-- ── B4: I-α ∧ IV (no V) ──

def model_I_alpha_IV : TestSystem :=
  { margin := 10, cost := 5, drain := 0,
    total_cost := 0, drain_net := 0, regeneration := 0,
    recovery := 0, self_op_cost := 0, operations := 0 }

theorem ia_iv_has_I_alpha : has_I_alpha model_I_alpha_IV := by decide
theorem ia_iv_has_IV : has_IV model_I_alpha_IV := by decide
theorem ia_iv_not_V : ¬has_V model_I_alpha_IV := by decide

-- ── B5: I-α ∧ V (no IV) ──

def model_I_alpha_V : TestSystem :=
  { margin := 10, cost := 0, drain := 3,
    total_cost := 0, drain_net := 0, regeneration := 0,
    recovery := 0, self_op_cost := 0, operations := 0 }

theorem ia_v_has_I_alpha : has_I_alpha model_I_alpha_V := by decide
theorem ia_v_not_IV : ¬has_IV model_I_alpha_V := by decide
theorem ia_v_has_V : has_V model_I_alpha_V := by decide

-- ── B6: IV ∧ V (no I-α) ──

def model_IV_V : TestSystem :=
  { margin := 0, cost := 5, drain := 3,
    total_cost := 0, drain_net := 0, regeneration := 0,
    recovery := 0, self_op_cost := 0, operations := 0 }

theorem iv_v_not_I_alpha : ¬has_I_alpha model_IV_V := by decide
theorem iv_v_has_IV : has_IV model_IV_V := by decide
theorem iv_v_has_V : has_V model_IV_V := by decide

-- ── B7: I-α ∧ IV ∧ V (all three atoms, without I-β) ──

def model_all_atoms : TestSystem :=
  { margin := 10, cost := 5, drain := 3,
    total_cost := 5, drain_net := 5, regeneration := 0,
    recovery := 10, self_op_cost := 0, operations := 0 }

theorem all_has_I_alpha : has_I_alpha model_all_atoms := by decide
theorem all_has_IV : has_IV model_all_atoms := by decide
theorem all_has_V : has_V model_all_atoms := by decide
theorem all_not_I_beta : ¬has_I_beta model_all_atoms := by native_decide

-- ── B8: Full I ∧ V (and IV follows by §A) ──

/-- A fully ontodynamic system.
    margin=10, cost=10, drain=2,
    β₁: 7+3=10, regen=3>0
    β₂: 10>5
    β₃: 2*3=6 ≤ 10, ops=2>0, soc=3>0 -/
def model_full : TestSystem :=
  { margin := 10, cost := 10, drain := 2,
    total_cost := 10, drain_net := 7, regeneration := 3,
    recovery := 5, self_op_cost := 3, operations := 2 }

theorem full_has_I : has_I model_full := by native_decide

theorem full_has_V : has_V model_full := by decide

theorem full_has_IV_derived : has_IV model_full :=
  I_implies_IV model_full full_has_I

-- ── B9: I-β₁ ∧ I-β₂ without I-β₃, with I-α ∧ IV ∧ V ──
-- Shows I-β₃ is independent of the other two even with everything else present

def model_no_beta3 : TestSystem :=
  { margin := 10, cost := 10, drain := 2,
    total_cost := 10, drain_net := 7, regeneration := 3,
    recovery := 5, self_op_cost := 100, operations := 1 }

theorem no_b3_has_I_alpha : has_I_alpha model_no_beta3 := by native_decide
theorem no_b3_has_IV : has_IV model_no_beta3 := by native_decide
theorem no_b3_has_V : has_V model_no_beta3 := by native_decide
theorem no_b3_has_beta1 : has_I_beta1 model_no_beta3 := by native_decide
theorem no_b3_has_beta2 : has_I_beta2 model_no_beta3 := by native_decide
theorem no_b3_not_beta3 : ¬has_I_beta3 model_no_beta3 := by native_decide

-- ── B10: Full I without V ──

def model_I_no_V : TestSystem :=
  { margin := 10, cost := 10, drain := 0,
    total_cost := 10, drain_net := 7, regeneration := 3,
    recovery := 5, self_op_cost := 3, operations := 2 }

theorem i_noV_has_I : has_I model_I_no_V := by native_decide
theorem i_noV_not_V : ¬has_V model_I_no_V := by decide

-- ═══════════════════════════════════════════════════════════════════════════
-- §C. SYNTHESIS
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] I-α, IV, V are mutually independent (at the atomic level). -/
theorem atoms_independent :
    -- each alone
    (∃ s, has_I_alpha s ∧ ¬has_IV s ∧ ¬has_V s) ∧
    (∃ s, ¬has_I_alpha s ∧ has_IV s ∧ ¬has_V s) ∧
    (∃ s, ¬has_I_alpha s ∧ ¬has_IV s ∧ has_V s) ∧
    -- each pair without the third
    (∃ s, has_I_alpha s ∧ has_IV s ∧ ¬has_V s) ∧
    (∃ s, has_I_alpha s ∧ ¬has_IV s ∧ has_V s) ∧
    (∃ s, ¬has_I_alpha s ∧ has_IV s ∧ has_V s) :=
  ⟨⟨model_I_alpha_only, ia_only_has_I_alpha, ia_only_not_IV, ia_only_not_V⟩,
   ⟨model_IV_only, iv_only_not_I_alpha, iv_only_has_IV, iv_only_not_V⟩,
   ⟨model_V_only, v_only_not_Ialpha, v_only_not_IV, v_only_has_V⟩,
   ⟨model_I_alpha_IV, ia_iv_has_I_alpha, ia_iv_has_IV, ia_iv_not_V⟩,
   ⟨model_I_alpha_V, ia_v_has_I_alpha, ia_v_not_IV, ia_v_has_V⟩,
   ⟨model_IV_V, iv_v_not_I_alpha, iv_v_has_IV, iv_v_has_V⟩⟩

/-- [∎] Full I implies IV — IV is not an independent axiom. -/
theorem I_subsumes_IV : ∀ s : TestSystem, has_I s → has_IV s :=
  fun s h => I_implies_IV s h

/-- [∎] But IV does not imply I — the converse fails. -/
theorem IV_not_implies_I : ¬(∀ s : TestSystem, has_IV s → has_I s) := by
  intro h_all
  have h := h_all model_IV_only iv_only_has_IV
  exact absurd h.1 iv_only_not_I_alpha

/-- [∎] V is independent of I (in both directions). -/
theorem V_independent_of_I :
    (∃ s, has_I s ∧ ¬has_V s) ∧
    (∃ s, has_V s ∧ ¬has_I s) :=
  ⟨⟨model_I_no_V, i_noV_has_I, i_noV_not_V⟩,
   ⟨model_V_without_full_I, v_no_fullI_has_V,
    fun h => absurd h v_no_fullI_not_I⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- INVENTORY
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Result

### Forced implications (§A)
| Premise | Conclusion | Theorem |
|---------|------------|---------|
| I-β₂ | IV | `beta2_implies_IV` |
| I-β₃ | I-α | `beta3_implies_I_alpha` |
| I (full) | IV | `I_implies_IV` |
| I-β (full) | I-α | `I_beta_implies_I_alpha` |

### Independence (§B–§C)
| Atoms | I-α, IV, V mutually independent | `atoms_independent` (6 models) |
| I → IV | I subsumes IV | `I_subsumes_IV` |
| IV ↛ I | Converse fails | `IV_not_implies_I` |
| I ⊥ V | Independent in both directions | `V_independent_of_I` |

### Philosophical interpretation

The system does not have THREE independent axioms — it has TWO and a corollary:
  - **I** (being = act of its own necessity) — founding axiom
  - **V** (finitude, exteriority pressure) — structural axiom
  - **IV** (cost positivity) — COROLLARY of I

This STRENGTHENS parsimony, not fragility. The system is more
economical than advertised: I + V suffice; IV is a theorem, not a postulate.

### Counter
10 models · 41 theorems · 0 sorry · 0 imports
-/

end InterAxiomIndependence

-- ═══════════════════════════════════════════════════════════════════════════
-- H8 — INDEPENDENCE OF THE THREE I-β COMPONENTS
-- ═══════════════════════════════════════════════════════════════════════════

namespace BetaAudit

/-!
# TEST H8 — Independence of the three I-β components

I-β has three components:
  I-β₁ (decomposition): drain_net + regeneration = total_cost ∧ regeneration > 0
  I-β₂ (endogeneity)  : cost > recovery
  I-β₃ (reflexivity)  : ops * self_op_cost ≤ margin ∧ ops > 0 ∧ self_op_cost > 0

Independence proof by separating models:
  M₁ satisfies β₁ only, M₂ satisfies β₂ only, M₃ satisfies β₃ only.

If the 9 theorems compile, no component implies the others.
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- Unified structure and propositions
-- ═══════════════════════════════════════════════════════════════════════════

structure SystemUnified where
  margin : Nat
  total_cost : Nat
  drain_net : Nat
  regeneration : Nat
  recovery : Nat
  cost : Nat
  self_op_cost : Nat
  operations : Nat

def has_beta1 (s : SystemUnified) : Prop :=
  s.drain_net + s.regeneration = s.total_cost ∧ s.regeneration > 0

def has_beta2 (s : SystemUnified) : Prop :=
  s.cost > s.recovery

def has_beta3 (s : SystemUnified) : Prop :=
  s.operations * s.self_op_cost ≤ s.margin ∧ s.operations > 0 ∧ s.self_op_cost > 0

instance : DecidablePred has_beta1 := fun s => by
  unfold has_beta1; exact instDecidableAnd
instance : DecidablePred has_beta2 := fun s => by
  unfold has_beta2; exact Nat.decLt _ _
instance : DecidablePred has_beta3 := fun s => by
  unfold has_beta3; exact instDecidableAnd

-- ═══════════════════════════════════════════════════════════════════════════
-- Separating models — minimal independence
-- ═══════════════════════════════════════════════════════════════════════════

-- ── M₁: I-β₁ without I-β₂ or I-β₃ ──

/-- Additive decomposition (2+3=5, regen=3>0),
    but recovery > cost (5>2) and self_op_cost > margin (100>10). -/
def model_beta1_only : SystemUnified :=
  { margin := 10, total_cost := 5, drain_net := 2, regeneration := 3,
    recovery := 5, cost := 2, self_op_cost := 100, operations := 1 }

theorem m1_has_beta1 : has_beta1 model_beta1_only := by decide
theorem m1_not_beta2 : ¬ has_beta2 model_beta1_only := by decide
theorem m1_not_beta3 : ¬ has_beta3 model_beta1_only := by native_decide

-- ── M₂: I-β₂ without I-β₁ or I-β₃ ──

/-- Gradient endogeneity (cost=10 > recovery=3),
    but no decomposition (7+0≠5, regen=0) and cost > margin (100>10). -/
def model_beta2_only : SystemUnified :=
  { margin := 10, total_cost := 5, drain_net := 7, regeneration := 0,
    recovery := 3, cost := 10, self_op_cost := 100, operations := 1 }

theorem m2_not_beta1 : ¬ has_beta1 model_beta2_only := by decide
theorem m2_has_beta2 : has_beta2 model_beta2_only := by decide
theorem m2_not_beta3 : ¬ has_beta3 model_beta2_only := by native_decide

-- ── M₃: I-β₃ without I-β₁ or I-β₂ ──

/-- Reflexivity (2×3=6 ≤ 10),
    but no decomposition (7+0≠5, regen=0) and recovery > cost (5>2). -/
def model_beta3_only : SystemUnified :=
  { margin := 10, total_cost := 5, drain_net := 7, regeneration := 0,
    recovery := 5, cost := 2, self_op_cost := 3, operations := 2 }

theorem m3_not_beta1 : ¬ has_beta1 model_beta3_only := by native_decide
theorem m3_not_beta2 : ¬ has_beta2 model_beta3_only := by native_decide
theorem m3_has_beta3 : has_beta3 model_beta3_only := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Synthesis theorem
-- ═══════════════════════════════════════════════════════════════════════════

/-- The three I-β components are mutually independent.
    Proved by separating models: each component is satisfied by
    a system that violates the other two. -/
theorem beta_components_independent :
    (∃ s, has_beta1 s ∧ ¬ has_beta2 s ∧ ¬ has_beta3 s) ∧
    (∃ s, ¬ has_beta1 s ∧ has_beta2 s ∧ ¬ has_beta3 s) ∧
    (∃ s, ¬ has_beta1 s ∧ ¬ has_beta2 s ∧ has_beta3 s) :=
  ⟨⟨model_beta1_only, m1_has_beta1, m1_not_beta2, m1_not_beta3⟩,
   ⟨model_beta2_only, m2_not_beta1, m2_has_beta2, m2_not_beta3⟩,
   ⟨model_beta3_only, m3_not_beta1, m3_not_beta2, m3_has_beta3⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- Bonus: pairwise independence (no pair implies the third)
-- ═══════════════════════════════════════════════════════════════════════════

-- ── M₁₂: I-β₁ ∧ I-β₂ without I-β₃ ──

/-- Decomposition (2+3=5) AND endogeneity (10>3), but cost > margin (100>10). -/
def model_beta12 : SystemUnified :=
  { margin := 10, total_cost := 5, drain_net := 2, regeneration := 3,
    recovery := 3, cost := 10, self_op_cost := 100, operations := 1 }

theorem m12_has_beta1 : has_beta1 model_beta12 := by decide
theorem m12_has_beta2 : has_beta2 model_beta12 := by decide
theorem m12_not_beta3 : ¬ has_beta3 model_beta12 := by native_decide

-- ── M₁₃: I-β₁ ∧ I-β₃ without I-β₂ ──

/-- Decomposition (2+3=5) AND reflexivity (2×3=6≤10), but recovery > cost (5>2). -/
def model_beta13 : SystemUnified :=
  { margin := 10, total_cost := 5, drain_net := 2, regeneration := 3,
    recovery := 5, cost := 2, self_op_cost := 3, operations := 2 }

theorem m13_has_beta1 : has_beta1 model_beta13 := by decide
theorem m13_not_beta2 : ¬ has_beta2 model_beta13 := by decide
theorem m13_has_beta3 : has_beta3 model_beta13 := by native_decide

-- ── M₂₃: I-β₂ ∧ I-β₃ without I-β₁ ──

/-- Endogeneity (10>3) AND reflexivity (2×3=6≤10), but no decomposition (7+0≠5). -/
def model_beta23 : SystemUnified :=
  { margin := 10, total_cost := 5, drain_net := 7, regeneration := 0,
    recovery := 3, cost := 10, self_op_cost := 3, operations := 2 }

theorem m23_not_beta1 : ¬ has_beta1 model_beta23 := by decide
theorem m23_has_beta2 : has_beta2 model_beta23 := by decide
theorem m23_has_beta3 : has_beta3 model_beta23 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Complete synthesis theorem (total independence)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Total independence: no component nor any pair implies the remaining
    component(s). 6 separating models. -/
theorem beta_components_fully_independent :
    -- Singletons: each without the other two
    (∃ s, has_beta1 s ∧ ¬ has_beta2 s ∧ ¬ has_beta3 s) ∧
    (∃ s, ¬ has_beta1 s ∧ has_beta2 s ∧ ¬ has_beta3 s) ∧
    (∃ s, ¬ has_beta1 s ∧ ¬ has_beta2 s ∧ has_beta3 s) ∧
    -- Pairs: each pair without the third
    (∃ s, has_beta1 s ∧ has_beta2 s ∧ ¬ has_beta3 s) ∧
    (∃ s, has_beta1 s ∧ ¬ has_beta2 s ∧ has_beta3 s) ∧
    (∃ s, ¬ has_beta1 s ∧ has_beta2 s ∧ has_beta3 s) :=
  ⟨⟨model_beta1_only, m1_has_beta1, m1_not_beta2, m1_not_beta3⟩,
   ⟨model_beta2_only, m2_not_beta1, m2_has_beta2, m2_not_beta3⟩,
   ⟨model_beta3_only, m3_not_beta1, m3_not_beta2, m3_has_beta3⟩,
   ⟨model_beta12, m12_has_beta1, m12_has_beta2, m12_not_beta3⟩,
   ⟨model_beta13, m13_has_beta1, m13_not_beta2, m13_has_beta3⟩,
   ⟨model_beta23, m23_not_beta1, m23_has_beta2, m23_has_beta3⟩⟩

/-!
## Result H8

6 separating models, 18 theorems + 2 syntheses, 0 sorry.

The three I-β components are **totally independent**:
none implies the others, and no pair implies the third.

I-β is not a monolithic axiom — it is three modular commitments:
  I-β₁ (decomposition)  → buys XXXVIII-a, XXXVIII-b, XXXVIII-d
  I-β₂ (endogeneity)    → buys R-XVII (6 theorems)
  I-β₃ (reflexivity)    → buys H5-1, H5-3, H5-4

A reader may accept any subset.
-/

end BetaAudit
