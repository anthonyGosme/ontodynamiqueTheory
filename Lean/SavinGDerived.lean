/-!
# SavingDerived.lean — saving_pos DERIVED from template-as-constraint

## Problem

In Autodynamique.lean §15, `ActCost` posits three fields:
  - `raw_cost_pos : raw_cost > 0`           — IV
  - `saving_pos : template_saving > 0`      — POSITED (hidden postulate)
  - `saving_bound : template_saving < raw_cost` — IV preserved

The manuscript (l. 1395) claims saving_pos is "a refinement of IV,
not a fourth axiom." But in the Lean code, it IS a field — functionally
a postulate. This file closes the gap.

## Solution

Decompose the act into a POSSIBILITY SPACE:
  - An unguided act explores `space` possibilities (space > 0, from I)
  - Each possibility has incompressible cost (unit_cost > 0, from IV)
  - A template is a non-trivial constraint: it eliminates ≥ 1 possibility
  - A template is partial: it does not eliminate all possibilities

Then:
  raw_cost     = space × unit_cost
  guided_cost  = (space − eliminated) × unit_cost
  saving       = eliminated × unit_cost

And:
  saving > 0       ← eliminated > 0 ∧ unit_cost > 0    (DERIVED)
  saving < raw     ← eliminated < space ∧ unit_cost > 0 (DERIVED)
  guided_cost > 0  ← (space − eliminated) > 0 ∧ unit_cost > 0 (DERIVED)

## Epistemic status of the new primitives

| Field | Source | Status |
|-------|--------|--------|
| unit_cost > 0 | IV | Inherited — every act costs |
| eliminated > 0 | Definition of "template" | ANALYTIC — a constraint that constrains nothing is not a constraint |
| eliminated < space | IV preserved | The template does not annihilate the act |
| space > 0 | Derived from the above two | NOT INDEPENDENT |

The irreducible new content is: "a template constrains" — which is
analytic, not synthetic. A non-constraining template is a vacuous label.

## Theorems: 13, sorry: 0, imports: 0
-/

namespace SavingDerived

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Primitive structure — more fundamental than ActCost
-- ═══════════════════════════════════════════════════════════════════════════

/-- An act over a possibility space with a constraining template.

    Philosophical reading:
    - space      = number of distinct configurational possibilities
    - unit_cost  = incompressible cost per possibility (IV)
    - eliminated = possibilities removed by existing structure

    PRIMITIVE posits:
    (P1) unit_cost > 0      — IV: every possibility costs
    (P2) eliminated > 0     — ANALYTIC: a constraint constrains
    (P3) eliminated < space  — the act remains possible under template

    Note: space > 0 is DERIVED from P2 + P3 (not an independent posit).

    Under I' : `space`, `eliminated`, `unit_cost`, `template_constrains`,
    `template_partial` describe a single individuated act — un acte un.
    The template operates within the unity of the act (reducing its
    possibility space), not alongside it. The derivation `space > 0` from
    P2 + P3 is coherent with the architectonic un : a constrained act
    that still has possibility is a viable un. -/
structure ConstrainedAct where
  /-- Size of the unconstrained possibility space -/
  space : Nat
  /-- Number of possibilities the template eliminates -/
  eliminated : Nat
  /-- Incompressible cost per possibility (IV) -/
  unit_cost : Nat
  /-- (P1) IV: each possibility has positive cost -/
  unit_cost_pos : unit_cost > 0
  /-- (P2) A template is a non-trivial constraint: it eliminates ≥ 1.
      This is ANALYTIC — a constraint that constrains nothing is
      not a constraint. It is the definition of "template", not
      an empirical claim about templates. -/
  template_constrains : eliminated > 0
  /-- (P3) The template does not eliminate everything: the guided
      act is still possible. From IV: guided cost > 0. -/
  template_partial : eliminated < space

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Derived quantities
-- ═══════════════════════════════════════════════════════════════════════════

/-- Cost without template = full space × unit cost. -/
def ConstrainedAct.raw_cost (a : ConstrainedAct) : Nat :=
  a.space * a.unit_cost

/-- Cost with template = reduced space × unit cost. -/
def ConstrainedAct.guided_cost (a : ConstrainedAct) : Nat :=
  (a.space - a.eliminated) * a.unit_cost

/-- The saving = eliminated possibilities × unit cost. -/
def ConstrainedAct.saving (a : ConstrainedAct) : Nat :=
  a.eliminated * a.unit_cost

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Arithmetic helpers
-- ═══════════════════════════════════════════════════════════════════════════

/-- Product of two positives is positive. (Used in Dynamics.lean too.) -/
private theorem mul_pos (a b : Nat) (ha : a > 0) (hb : b > 0) :
    a * b > 0 := by
  have : 1 ≤ a := ha
  have : 1 ≤ b := hb
  have : 1 * 1 ≤ a * b := Nat.mul_le_mul ‹1 ≤ a› ‹1 ≤ b›
  omega

/-- Strict monotonicity of multiplication by a positive factor.
    a < b ∧ c > 0 → a * c < b * c. -/
private theorem mul_lt_mul_of_pos (a b c : Nat) (hab : a < b) (hc : c > 0) :
    a * c < b * c := by
  -- a + 1 ≤ b
  have h1 : a + 1 ≤ b := hab
  -- (a+1) * c ≤ b * c
  have h2 : (a + 1) * c ≤ b * c := Nat.mul_le_mul_right c h1
  -- (a+1) * c = a * c + c  (Nat.succ_mul)
  have h3 : (a + 1) * c = a * c + c := Nat.succ_mul a c
  -- combine: a*c + c ≤ b*c, c ≥ 1, so a*c < b*c
  omega

/-- Distributivity: (a + b) * c = a * c + b * c.
    Local proof to avoid dependency on specific lemma names. -/
private theorem add_mul_local (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction b with
  | zero => simp [Nat.zero_mul, Nat.add_zero]
  | succ n ih =>
    -- (a + (n+1)) * c = (a + n + 1) * c = (a + n) * c + c
    have h1 : a + (n + 1) = (a + n) + 1 := by omega
    rw [h1, Nat.succ_mul, ih, Nat.succ_mul]
    -- a * c + n * c + c = a * c + (n * c + c)
    omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Structural lemmas
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] space > 0 is DERIVED from P2 + P3 — not an independent posit. -/
theorem space_pos (a : ConstrainedAct) : a.space > 0 := by
  have := a.template_constrains  -- eliminated > 0
  have := a.template_partial     -- eliminated < space
  omega

/-- [∎] Remaining space after template is positive. -/
theorem remaining_pos (a : ConstrainedAct) : a.space - a.eliminated > 0 := by
  have := a.template_constrains
  have := a.template_partial
  omega

/-- [∎] COST DECOMPOSITION — raw = saving + guided.
    The template partitions the cost into what it eliminates and what remains. -/
theorem cost_decomposition (a : ConstrainedAct) :
    a.raw_cost = a.saving + a.guided_cost := by
  unfold ConstrainedAct.raw_cost ConstrainedAct.saving ConstrainedAct.guided_cost
  -- Goal: space * u = eliminated * u + (space - eliminated) * u
  have h_partial := a.template_partial  -- eliminated < space (needed for Nat sub)
  -- (eliminated + (space - eliminated)) * u = eliminated * u + (space - eliminated) * u
  have h_dist := add_mul_local a.eliminated (a.space - a.eliminated) a.unit_cost
  -- eliminated + (space - eliminated) = space  (requires eliminated ≤ space)
  have h_sum : a.eliminated + (a.space - a.eliminated) = a.space := by omega
  -- Substitute in h_dist: LHS becomes space * u
  rw [h_sum] at h_dist
  -- h_dist is now exactly our goal
  exact h_dist

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. THE THREE DERIVATIONS — the core result
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] SAVING_POS — DERIVED.
    The template produces a strictly positive saving.
    From: eliminated > 0 (P2, analytic) ∧ unit_cost > 0 (P1, IV).
    THIS IS THE THEOREM THAT REPLACES THE POSITED FIELD. -/
theorem saving_pos_derived (a : ConstrainedAct) :
    a.saving > 0 := by
  unfold ConstrainedAct.saving
  exact mul_pos a.eliminated a.unit_cost a.template_constrains a.unit_cost_pos

/-- [∎] RAW_COST_POS — raw cost is positive (IV). -/
theorem raw_cost_pos_derived (a : ConstrainedAct) :
    a.raw_cost > 0 := by
  unfold ConstrainedAct.raw_cost
  exact mul_pos a.space a.unit_cost (space_pos a) a.unit_cost_pos

/-- [∎] GUIDED_COST_POS — guided cost is positive (IV preserved).
    The template reduces cost but does not annihilate it. -/
theorem guided_cost_pos_derived (a : ConstrainedAct) :
    a.guided_cost > 0 := by
  unfold ConstrainedAct.guided_cost
  exact mul_pos (a.space - a.eliminated) a.unit_cost (remaining_pos a) a.unit_cost_pos

/-- [∎] SAVING_BOUND — saving < raw_cost.
    The template does not make the act free.
    From: eliminated < space (P3) ∧ unit_cost > 0 (P1). -/
theorem saving_bound_derived (a : ConstrainedAct) :
    a.saving < a.raw_cost := by
  unfold ConstrainedAct.saving ConstrainedAct.raw_cost
  exact mul_lt_mul_of_pos a.eliminated a.space a.unit_cost
    a.template_partial a.unit_cost_pos

/-- [∎] ASYMMETRY — raw_cost > guided_cost (construction > maintenance).
    Direct from cost_decomposition + saving_pos. -/
theorem asymmetry_derived (a : ConstrainedAct) :
    a.raw_cost > a.guided_cost := by
  have h_decomp := cost_decomposition a
  have h_saving := saving_pos_derived a
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. BRIDGE TO ActCost — backward compatibility
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Bridge

The existing codebase (Autodynamique.lean, Dynamics.lean, DPDRDerived.lean)
uses `ActCost` with `saving_pos` as a field. This section constructs an
`ActCost` from a `ConstrainedAct`, with ALL THREE FIELDS PROVEN.

After integration, every `ActCost` in the codebase can be replaced by
`ConstrainedAct.toActCost`, eliminating the posited `saving_pos` field
from the entire theorem chain.
-/

/-- ActCost replica (from Autodynamique.lean §15) for bridge construction.
    In the integrated codebase, this would be an import. -/
structure ActCost where
  raw_cost : Nat
  raw_cost_pos : raw_cost > 0
  template_saving : Nat
  saving_pos : template_saving > 0
  saving_bound : template_saving < raw_cost

/-- [∎] BRIDGE — Construct ActCost from ConstrainedAct.
    Every field that was POSITED in ActCost is now PROVEN.

    raw_cost     := space × unit_cost       (raw_cost_pos: PROVEN)
    saving       := eliminated × unit_cost  (saving_pos: PROVEN)
    saving_bound := saving < raw_cost       (PROVEN)

    This is the key deliverable: ActCost is no longer primitive.
    It is a DERIVED structure from ConstrainedAct. -/
def ConstrainedAct.toActCost (a : ConstrainedAct) : ActCost where
  raw_cost := a.raw_cost
  raw_cost_pos := raw_cost_pos_derived a
  template_saving := a.saving
  saving_pos := saving_pos_derived a
  saving_bound := saving_bound_derived a

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. Concrete witness — the bridge compiles
-- ═══════════════════════════════════════════════════════════════════════════

/-- Concrete example: space = 3, eliminated = 1, unit_cost = 2.
    raw = 6, guided = 4, saving = 2.
    Demonstrates that ConstrainedAct is satisfiable. -/
def exampleAct : ConstrainedAct where
  space := 3
  eliminated := 1
  unit_cost := 2
  unit_cost_pos := by omega
  template_constrains := by omega
  template_partial := by omega

/-- [∎] The example produces a valid ActCost. -/
theorem example_valid : (exampleAct.toActCost).raw_cost = 6 ∧
    (exampleAct.toActCost).template_saving = 2 := by
  constructor <;> rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- INVENTORY
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Theorem count: 13 theorems, 0 sorry, 0 imports

| # | Theorem | Content | Source |
|---|---------|---------|--------|
| 1 | space_pos | space > 0 | P2 + P3 |
| 2 | remaining_pos | space − eliminated > 0 | P2 + P3 |
| 3 | cost_decomposition | raw = saving + guided | Nat arithmetic |
| 4 | **saving_pos_derived** | **saving > 0** | **P1 + P2 (THE KEY)** |
| 5 | raw_cost_pos_derived | raw > 0 | P1 + derived space_pos |
| 6 | guided_cost_pos_derived | guided > 0 (IV preserved) | P1 + remaining_pos |
| 7 | saving_bound_derived | saving < raw | P1 + P3 |
| 8 | asymmetry_derived | raw > guided | decomposition + saving_pos |
| 9 | example_valid | witness satisfiable | concrete |
| + 3 private helpers | mul_pos, mul_lt_mul_of_pos, add_mul_local | arithmetic | |
| + 1 bridge | toActCost | ConstrainedAct → ActCost | all fields proven |

## What changed

BEFORE (Autodynamique.lean §15):
  `saving_pos : template_saving > 0`    — FIELD (posited)

AFTER (this file):
  `theorem saving_pos_derived`          — THEOREM (derived from P1 + P2)

## Primitive posits — what is truly irreducible

| Posit | Content | Justification |
|-------|---------|---------------|
| P1: unit_cost > 0 | Each possibility costs | IV (inherited) |
| P2: eliminated > 0 | A template constrains | ANALYTIC (definition) |
| P3: eliminated < space | Template is partial | IV preserved |

P1 and P3 are instances of IV (incompressible cost).
P2 is analytic: "template" MEANS "non-trivial constraint on possibilities."
A template with eliminated = 0 constrains nothing — it is not a template.

Therefore: saving_pos is derived from IV + the definition of "template."
The claim "everything derives from I and V" is restored, with the caveat
that "template" is defined as non-trivial constraint (analytic, not synthetic).

## Integration path

1. Add `ConstrainedAct` to Autodynamique.lean before §15
2. Replace `ActCost` fields with `ConstrainedAct.toActCost`
3. All downstream theorems (Dynamics.lean, DPDRDerived.lean) unchanged
4. Update Annexe F: saving_pos moves from "posited" to "derived"
5. Update manuscript l. 1395: "raffinement de IV" becomes exact
-/

end SavingDerived
