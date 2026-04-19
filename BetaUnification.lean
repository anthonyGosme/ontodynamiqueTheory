-- BetaUnification.lean
-- The three components of I-β derive from β₃ (reflexivity)
-- plus one identification: recovery is an auto-operation.
--
-- THE ARGUMENT:
--   β₃ says: the operator is the operated (self_op_cost > 0).
--   Recovery is an auto-operation (it transforms the system).
--   By β₃, auto-operating costs > 0. An auto-operation at cost 0
--   changes nothing — that is inertia, not an operation.
--   Therefore: recovering costs. The cost of recovery is drawn from
--   the same margin as the original cost (β₃: operator = operated).
--   Net recovery < gross recovery. Cost > net recovery. That is β₂.
--   The decomposition cost = drain + net_recovery is β₁.
--   IV (every operation costs) is then derived from β₂, not assumed.
--
-- RESULT: I-β is not three independent postulates arbitrarily grouped.
--   It is one engagement (β₃: operator = operated) whose arithmetic
--   consequences are β₂ and β₁. The independence proved in
--   AxiomAudit.lean measures the strength of each component in
--   isolation; this file shows that β₃ alone forces the other two.
--
-- Theorems: 9
-- Sorry: 0
-- Imports: none

namespace BetaUnification

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. THE IDENTIFICATION: recovery is an operation
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## The one non-formal step

The system calls this the "recovery-as-operation identification."
It says: when a system regenerates part of its cost, that
regeneration is itself a transformation — not a free relaxation.

The alternative (recovery is passive, thermodynamic, costless)
is the position of equilibrium physics. I rejects it: β₃ says
the operator is the operated, so every operation the system
performs on itself — including recovery — draws from the same
margin. There is no free reservoir.

Why self_op_cost > 0 is entailed, not smuggled: an auto-operation
at cost 0 changes nothing in the system — it is inertia (XIII),
not an operation. β₃ says "operates on itself"; if the operation
is indistinguishable from not operating, β₃ is vacuous. The
positivity of cost is what separates operating from persisting.

This identification is the bridge between β₃ (philosophical)
and β₂ (arithmetic). It is not a hidden axiom — it is what
"operator = operated" means when applied to recovery.
-/

/-- A system with reflexive cost: the operator is the operated,
    and recovery is an operation (therefore has overhead). -/
structure ReflexiveAct where
  /-- Total cost of the act -/
  total_cost : Nat
  total_cost_pos : total_cost > 0
  /-- Material available for recovery (gross, before overhead) -/
  gross_recovery : Nat
  gross_recovery_pos : gross_recovery > 0
  /-- Can't recover more than was spent -/
  recovery_bounded : gross_recovery ≤ total_cost
  /-- β₃ APPLIED: recovery is an auto-operation → overhead > 0.
      Not from IV — from β₃ directly. β₃ encodes `self_op_cost > 0`
      (AxiomAudit.lean). Why? Because an auto-operation at cost 0
      changes nothing — it is inertia (XIII), not an operation.
      "Operates on itself" means: draws from its own margin.
      No external reservoir, no free transformation. -/
  recovery_overhead : Nat
  recovery_overhead_pos : recovery_overhead > 0
  /-- Overhead can't exceed gross recovery -/
  overhead_bounded : recovery_overhead ≤ gross_recovery

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. β₂ FROM β₃ — cost > net recovery
-- ═══════════════════════════════════════════════════════════════════════════

/-- Net recovery: what's actually recovered after overhead. -/
def netRecovery (a : ReflexiveAct) : Nat :=
  a.gross_recovery - a.recovery_overhead

/-- [∎] Net recovery is strictly less than gross recovery.
    The overhead eats into the recovery. -/
theorem net_lt_gross (a : ReflexiveAct) :
    netRecovery a < a.gross_recovery := by
  unfold netRecovery
  have := a.recovery_overhead_pos
  have := a.overhead_bounded
  omega

/-- [∎] β₂ FROM β₃ — cost > net recovery.
    Proof: net recovery < gross recovery ≤ total cost.
    This is the arithmetic consequence of "recovering costs." -/
theorem beta2_from_reflexivity (a : ReflexiveAct) :
    a.total_cost > netRecovery a := by
  unfold netRecovery
  have := a.recovery_bounded
  have := a.recovery_overhead_pos
  have := a.overhead_bounded
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. β₁ FROM β₂ — the additive decomposition
-- ═══════════════════════════════════════════════════════════════════════════

/-- Drain net: the unrecovered cost. -/
def drainNet (a : ReflexiveAct) : Nat :=
  a.total_cost - netRecovery a

/-- [∎] DRAIN IS POSITIVE — from β₂.
    cost > net recovery → drain > 0. -/
theorem drain_pos (a : ReflexiveAct) :
    drainNet a > 0 := by
  unfold drainNet; have := beta2_from_reflexivity a; omega

/-- [∎] β₁ DECOMPOSITION — from β₂.
    total_cost = drain_net + net_recovery.
    This is the additive structure that β₁ encodes. -/
theorem beta1_decomposition (a : ReflexiveAct) :
    drainNet a + netRecovery a = a.total_cost := by
  unfold drainNet; have := beta2_from_reflexivity a; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. CLOSURE CONDITION — net recovery > 0
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## When is net recovery positive?

β₃ alone doesn't force net recovery > 0. If overhead = gross,
net recovery = 0. That system is an aggregate — it costs but
doesn't recover.

For a closure (XXXII), regeneration is definitionally positive.
So for closures: overhead < gross (strict), net recovery > 0.
The full β₁ (with regen_pos) holds for closures.

For aggregates: net recovery = 0, drain = total_cost. β₂ holds
trivially. β₁ holds with regen = 0 — which is exactly the
aggregate condition.
-/

/-- A reflexive act where recovery is effective (closure). -/
structure ClosureAct extends ReflexiveAct where
  /-- For a closure, overhead doesn't consume all recovery.
      Otherwise, recovery is vacuous and the system is an aggregate. -/
  overhead_strict : recovery_overhead < gross_recovery

/-- [∎] Net recovery is positive for closures. -/
theorem closure_regen_pos (a : ClosureAct) :
    netRecovery a.toReflexiveAct > 0 := by
  unfold netRecovery; have := a.overhead_strict; omega

/-- [∎] FULL β₁ FOR CLOSURES — decomposition with both terms positive. -/
theorem full_beta1_closure (a : ClosureAct) :
    drainNet a.toReflexiveAct > 0 ∧
    netRecovery a.toReflexiveAct > 0 ∧
    drainNet a.toReflexiveAct + netRecovery a.toReflexiveAct =
      a.total_cost :=
  ⟨drain_pos a.toReflexiveAct,
   closure_regen_pos a,
   beta1_decomposition a.toReflexiveAct⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. THE FULL CHAIN — β₃ → β₂ → β₁
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] THE CHAIN — all three β components from reflexivity.
    For closures: β₃ (in the structure) → β₂ → β₁ (all three positive). -/
theorem beta_chain (a : ClosureAct) :
    -- β₂: cost > net recovery
    a.total_cost > netRecovery a.toReflexiveAct ∧
    -- β₁: decomposition with drain > 0 and regen > 0
    drainNet a.toReflexiveAct + netRecovery a.toReflexiveAct =
      a.total_cost ∧
    drainNet a.toReflexiveAct > 0 ∧
    netRecovery a.toReflexiveAct > 0 :=
  ⟨beta2_from_reflexivity a.toReflexiveAct,
   beta1_decomposition a.toReflexiveAct,
   drain_pos a.toReflexiveAct,
   closure_regen_pos a⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. COMPATIBILITY — existing structures are recoverable
-- ═══════════════════════════════════════════════════════════════════════════

/-- Replica of MetabolizingClosure (standalone). -/
structure MetabolizingClosureCompat where
  margin : Nat
  total_cost : Nat
  total_cost_pos : total_cost > 0
  regeneration : Nat
  regen_pos : regeneration > 0
  drain_net : Nat
  drain_net_pos : drain_net > 0
  cost_decomposition : drain_net + regeneration = total_cost

/-- [∎] Every ClosureAct yields a MetabolizingClosure.
    The overhead is dropped — downstream code never uses it. -/
def toMetabolizing (a : ClosureAct) : MetabolizingClosureCompat where
  margin := a.toReflexiveAct.total_cost  -- conservative: margin ≥ cost
  total_cost := a.total_cost
  total_cost_pos := a.total_cost_pos
  regeneration := netRecovery a.toReflexiveAct
  regen_pos := closure_regen_pos a
  drain_net := drainNet a.toReflexiveAct
  drain_net_pos := drain_pos a.toReflexiveAct
  cost_decomposition := beta1_decomposition a.toReflexiveAct

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. THE AGGREGATE CASE — β₃ without closure
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] For aggregates (overhead = gross), net recovery = 0.
    drain = total_cost. β₂ holds trivially. -/
theorem aggregate_drain_equals_cost (a : ReflexiveAct)
    (h : a.recovery_overhead = a.gross_recovery) :
    drainNet a = a.total_cost ∧ netRecovery a = 0 := by
  constructor
  · unfold drainNet netRecovery; omega
  · unfold netRecovery; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. CONCRETE WITNESS
-- ═══════════════════════════════════════════════════════════════════════════

/-- Concrete closure. cost = 5, gross_recovery = 3, overhead = 1.
    net_recovery = 2, drain = 3. β₂: 5 > 2 ✓. β₁: 3 + 2 = 5 ✓. -/
def concreteClosure : ClosureAct where
  total_cost := 5; total_cost_pos := by omega
  gross_recovery := 3; gross_recovery_pos := by omega
  recovery_bounded := by omega
  recovery_overhead := 1; recovery_overhead_pos := by omega
  overhead_bounded := by omega
  overhead_strict := by omega

/-- [∎] Concrete verification. -/
theorem concrete_verified :
    netRecovery concreteClosure.toReflexiveAct = 2 ∧
    drainNet concreteClosure.toReflexiveAct = 3 ∧
    drainNet concreteClosure.toReflexiveAct +
      netRecovery concreteClosure.toReflexiveAct = 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- INVENTORY
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Summary — 9 theorems · 0 sorry · 0 imports

| # | Theorem | Content |
|---|---------|---------|
| 1 | net_lt_gross | Net recovery < gross recovery |
| 2 | beta2_from_reflexivity | β₂: cost > net recovery |
| 3 | drain_pos | Drain > 0 |
| 4 | beta1_decomposition | β₁: drain + regen = cost |
| 5 | closure_regen_pos | Net regen > 0 for closures |
| 6 | full_beta1_closure | Full β₁ (both terms positive) |
| 7 | beta_chain | All three β from reflexivity |
| 8 | toMetabolizing | Compatibility with existing code |
| 9 | aggregate_drain_equals_cost | Aggregate: regen = 0, drain = cost |
| 10 | concrete_verified | Witness: 5 = 3 + 2 |

### The chain

β₃ (operator = operated, self_op_cost > 0)
  + "recovery is an auto-operation" (identification)
  → recovery_overhead > 0           — by β₃, not by IV
  → net_recovery < gross_recovery
  → cost > net_recovery              — β₂ ∎
  → cost = drain + net_recovery, drain > 0  — β₁ ∎
  For closures: net_recovery > 0     — full β₁ ∎
  Separately: β₂ → IV               — (AxiomAudit.lean)

### Why self_op_cost > 0 is in β₃, not beside it

β₃ says: the operator is the operated. The encoding in
AxiomAudit.lean includes `self_op_cost > 0` as a field of β₃.
Is this additional content smuggled in, or is it entailed?

Argument: an auto-operation at cost 0 changes nothing in the
system. A transformation that changes nothing is not a
transformation — it is inertia (XIII). β₃ says "operates on
itself"; if "operates" is to mean anything beyond "persists",
the operation must draw from the margin. No external reservoir
(β₃: operator = operated) + operation ≠ inertia → cost > 0.

The step "no free reservoir → cost > 0" excludes reversible
internal transformations at zero net cost. The system accepts
this exclusion: I-β says being IS doing, not that being
CONTAINS a doing among other free rearrangements. Every
rearrangement is a doing, every doing costs. This is the
content of "être = se faire" applied to itself.

### What this means for the axiom count

No circularity. IV is not an input to the chain — it is an
output (via β₂). The chain reads:

  β₃ (with self_op_cost > 0, entailed)
    + identification (recovery = auto-operation)
    → β₂ ∎ → β₁ ∎ → IV ∎

The irreducible postulatory content of I-β is:
  β₃ (the operator is the operated)
  + the recovery-as-operation identification.
Everything else — β₂, β₁, IV, V — is derived.

9 theorems · 0 sorry · 0 imports
2 structures · 4 definitions · 1 concrete witness
-/

end BetaUnification