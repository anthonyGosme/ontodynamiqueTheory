/-!
# DPDR — Complete derivation with trunk bridges

## Architecture

§0 — Minimal trunk replicas (ActCost, derived theorems)
§1 — LXV (independent failure)
§2 — Bridges: the three hypotheses derived from trunk
§3 — Revised DPDR: everything is derived

Sorry: 0
Imports: none (standalone — replicas are documented)
-/

namespace DPDRDerived

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. MINIMAL TRUNK REPLICAS
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Verbatim replicas from Autodynamique.lean §15-§16

These structures and theorems are copied from the trunk for standalone
compilation. With real imports, they would be replaced by `import OntoDynamique`.
-/

/-- ActCost — cost of an act with template possibility.
    Replica from Autodynamique.lean §15. -/
structure ActCost where
  raw_cost : Nat
  raw_cost_pos : raw_cost > 0
  template_saving : Nat
  saving_pos : template_saving > 0
  saving_bound : template_saving < raw_cost

/-- Construction = raw cost (without template). -/
def ActCost.construction (a : ActCost) : Nat := a.raw_cost

/-- Maintenance = cost with template (raw - saving). -/
def ActCost.maintenance (a : ActCost) : Nat := a.raw_cost - a.template_saving

/-- [∎ TRUNK] DERIVED ASYMMETRY — construction > maintenance. -/
theorem asymmetry_from_trunk (a : ActCost) :
    a.construction > a.maintenance := by
  unfold ActCost.construction ActCost.maintenance
  have := a.saving_pos; have := a.saving_bound; omega

/-- [∎ TRUNK] POSITIVE MAINTENANCE — IV preserved under template. -/
theorem maintenance_pos_from_trunk (a : ActCost) :
    a.maintenance > 0 := by
  unfold ActCost.maintenance
  have := a.raw_cost_pos; have := a.saving_bound; omega

/-- [∎ TRUNK] CONSTRUCTION OVERHEAD > 0.
    construction - maintenance > 0. Direct corollary of asymmetry. -/
theorem overhead_from_trunk (a : ActCost) :
    a.construction - a.maintenance > 0 := by
  have := asymmetry_from_trunk a; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. LXV — INDEPENDENT FAILURE (helpers + theorems)
-- ═══════════════════════════════════════════════════════════════════════════

private theorem dead_above_quota (m d : Nat) (h_d : d > 0) :
    ¬ (m ≥ (m / d + 1) * d) := by
  intro h_abs
  have h1 := Nat.div_add_mod m d
  have h2 := Nat.mod_lt m h_d
  have h3 : (m / d + 1) * d = m / d * d + d := Nat.succ_mul (m / d) d
  have h4 : d * (m / d) = m / d * d := Nat.mul_comm d (m / d)
  omega

private theorem alive_below_quota (m d t : Nat)
    (_h_d : d > 0) (h_t : t ≤ m / d) :
    m ≥ t * d := by
  have := Nat.div_mul_le_self m d
  have : t * d ≤ m / d * d := Nat.mul_le_mul_right d h_t
  omega

structure NestedCycles where
  lower_margin : Nat
  lower_margin_pos : lower_margin > 0
  lower_drain : Nat
  lower_drain_pos : lower_drain > 0
  upper_margin : Nat
  upper_margin_pos : upper_margin > 0
  upper_drain : Nat
  upper_drain_pos : upper_drain > 0

def lowerAlive (nc : NestedCycles) (t : Nat) : Prop :=
  nc.lower_margin ≥ t * nc.lower_drain

def upperAlive (nc : NestedCycles) (t : Nat) : Prop :=
  nc.upper_margin ≥ t * nc.upper_drain

/-- [∎] LXV-a — THE UPPER CAN DIE BEFORE THE LOWER. -/
theorem independent_failure (nc : NestedCycles)
    (h_upper_first : nc.upper_margin / nc.upper_drain <
                     nc.lower_margin / nc.lower_drain) :
    ∃ t, ¬ upperAlive nc t ∧ lowerAlive nc t :=
  ⟨_, dead_above_quota nc.upper_margin nc.upper_drain nc.upper_drain_pos,
   alive_below_quota nc.lower_margin nc.lower_drain _ nc.lower_drain_pos (by omega)⟩

/-- [∎] LXV-b — CONVERSE. -/
theorem independent_failure_reverse (nc : NestedCycles)
    (h_lower_first : nc.lower_margin / nc.lower_drain <
                     nc.upper_margin / nc.upper_drain) :
    ∃ t, ¬ lowerAlive nc t ∧ upperAlive nc t :=
  ⟨_, dead_above_quota nc.lower_margin nc.lower_drain nc.lower_drain_pos,
   alive_below_quota nc.upper_margin nc.upper_drain _ nc.upper_drain_pos (by omega)⟩

/-- [∎] LXV-c — EACH CYCLE EXHAUSTS (XXXIV). -/
theorem each_cycle_mortal (nc : NestedCycles) :
    (∃ t, ¬ lowerAlive nc t) ∧ (∃ t, ¬ upperAlive nc t) :=
  ⟨⟨_, dead_above_quota nc.lower_margin nc.lower_drain nc.lower_drain_pos⟩,
   ⟨_, dead_above_quota nc.upper_margin nc.upper_drain nc.upper_drain_pos⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. BRIDGES — The three hypotheses derived from trunk
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## The three bridges

Each DPDRDerived hypothesis is a corollary of a trunk theorem.
The `DPDRFromTrunk` structure encodes the second-order loop as
two `ActCost` (one for valence, one for the loop), and derives
the three positivities.
-/

/-- Second-order loop modeled via two trunk ActCost.
    - valence_act: first-order cycle (LIX)
    - loop_act: second-order cycle (LXI) -/
structure DPDRFromTrunk where
  /-- ActCost of the valence cycle (first order, LIX) -/
  valence_act : ActCost
  /-- ActCost of the loop (second order, LXI) -/
  loop_act : ActCost

/-- BRIDGE 3 — valence_cost > 0 derived from IV via maintenance_pos. -/
def valence_cost (d : DPDRFromTrunk) : Nat := d.valence_act.maintenance

/-- [∎] BRIDGE 3 — valence_cost > 0 is a trunk corollary. -/
theorem valence_cost_derived (d : DPDRFromTrunk) :
    valence_cost d > 0 :=
  maintenance_pos_from_trunk d.valence_act

/-- BRIDGE 1 — loop_own_cost > 0 derived from IV via maintenance_pos. -/
def loop_own_cost (d : DPDRFromTrunk) : Nat := d.loop_act.maintenance

/-- [∎] BRIDGE 1 — loop_own_cost > 0 is a trunk corollary. -/
theorem loop_own_cost_derived (d : DPDRFromTrunk) :
    loop_own_cost d > 0 :=
  maintenance_pos_from_trunk d.loop_act

/-- BRIDGE 2 — construction_overhead > 0 derived from Lemma 2 via asymmetry. -/
def construction_overhead (d : DPDRFromTrunk) : Nat :=
  d.loop_act.construction - d.loop_act.maintenance

/-- [∎] BRIDGE 2 — construction_overhead > 0 is a trunk corollary. -/
theorem overhead_derived (d : DPDRFromTrunk) :
    construction_overhead d > 0 :=
  overhead_from_trunk d.loop_act

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. REVISED DPDR — Derived thresholds, complete prediction
-- ═══════════════════════════════════════════════════════════════════════════

/-- Valence threshold = valence maintenance cost. -/
def drVT (d : DPDRFromTrunk) : Nat := valence_cost d

/-- Loop maintenance threshold = valence + loop own cost. -/
def drLMT (d : DPDRFromTrunk) : Nat := valence_cost d + loop_own_cost d

/-- Loop construction threshold = maintain + overhead. -/
def drLBT (d : DPDRFromTrunk) : Nat :=
  valence_cost d + loop_own_cost d + construction_overhead d

/-- [∎] DERIVED NESTING — loop threshold > valence threshold.
    Corollary of loop_own_cost > 0 (Bridge 1). -/
theorem nesting_from_trunk (d : DPDRFromTrunk) :
    drVT d < drLMT d := by
  unfold drVT drLMT
  have := loop_own_cost_derived d; omega

/-- [∎] DERIVED HYSTERESIS — build > maintain.
    Corollary of construction_overhead > 0 (Bridge 2). -/
theorem hysteresis_from_trunk (d : DPDRFromTrunk) :
    drLMT d < drLBT d := by
  unfold drLMT drLBT
  have := overhead_derived d; omega

/-- [∎] ORDERED THRESHOLDS — valence < maintain < build. -/
theorem ordering_from_trunk (d : DPDRFromTrunk) :
    drVT d < drLMT d ∧ drLMT d < drLBT d :=
  ⟨nesting_from_trunk d, hysteresis_from_trunk d⟩

/-- [∎] PHASE 1: NEITHER VALENCE NOR LOOP. -/
theorem phase1 (d : DPDRFromTrunk) :
    ∃ m, ¬ (m ≥ drVT d) ∧ ¬ (m ≥ drLBT d) := by
  refine ⟨0, ?_, ?_⟩
  · unfold drVT; have := valence_cost_derived d; omega
  · unfold drLBT; have := valence_cost_derived d; omega

/-- [∎] PHASE 2: VALENCE WITHOUT LOOP. -/
theorem phase2 (d : DPDRFromTrunk) :
    ∃ m, m ≥ drVT d ∧ ¬ (m ≥ drLBT d) := by
  refine ⟨drLMT d, ?_, ?_⟩
  · show drLMT d ≥ drVT d
    have := nesting_from_trunk d; omega
  · show ¬ (drLMT d ≥ drLBT d)
    have := hysteresis_from_trunk d; omega

/-- [∎] PHASE 3: VALENCE AND LOOP. -/
theorem phase3 (d : DPDRFromTrunk) :
    ∃ m, m ≥ drVT d ∧ m ≥ drLBT d := by
  refine ⟨drLBT d, ?_, ?_⟩
  · have h1 := nesting_from_trunk d; have h2 := hysteresis_from_trunk d; omega
  · exact Nat.le_refl _

/-- [∎] PHASE 2 NECESSARY. -/
theorem phase2_necessary (d : DPDRFromTrunk) :
    drLBT d - drVT d > 1 := by
  unfold drVT drLBT
  have := loop_own_cost_derived d; have := overhead_derived d; omega

/-- [∎] VALENCE MONOTONICITY. -/
theorem valence_monotone (d : DPDRFromTrunk) (m₁ m₂ : Nat)
    (h_le : m₁ ≤ m₂) (h_active : m₁ ≥ drVT d) :
    m₂ ≥ drVT d := by
  omega

/-- [∎] COMPLETE PREDICTION. -/
theorem dpdr_prediction (d : DPDRFromTrunk) :
    (∃ m, ¬ (m ≥ drVT d) ∧ ¬ (m ≥ drLBT d)) ∧
    (∃ m, m ≥ drVT d ∧ ¬ (m ≥ drLBT d)) ∧
    (∃ m, m ≥ drVT d ∧ m ≥ drLBT d) :=
  ⟨phase1 d, phase2 d, phase3 d⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- SUMMARY
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Bridge report

### Scenario A — All three bridges compile. ✓

| Bridge | Hypothesis | Trunk theorem | Status |
|------|-----------|----------------|--------|
| 3 | `valence_cost > 0` | `maintenance_pos_derived` (IV) | ∎ corollary |
| 1 | `loop_own_cost > 0` | `maintenance_pos_derived` (IV) | ∎ corollary |
| 2 | `overhead > 0` | `asymmetry_derived` (Lemme 2) | ∎ corollary |

### Complete derivation chain

```
ActCost.raw_cost_pos (IV)       ──┐
ActCost.saving_pos (template)   ──┤→ maintenance_pos_derived → valence_cost > 0 (Pont 3)
ActCost.saving_bound (IV)       ──┤→ maintenance_pos_derived → loop_own_cost > 0 (Pont 1)
                                  └→ asymmetry_derived → overhead > 0 (Pont 2)
```

### Primitive fields (irreducible)

For each ActCost (valence and loop):
- `raw_cost_pos : raw_cost > 0` — IV (incompressible cost)
- `saving_pos : template_saving > 0` — a template helps
- `saving_bound : template_saving < raw_cost` — IV preserved

Total: 6 primitive fields (3 per ActCost × 2 ActCost).
All are instances or direct consequences of IV.

### Manuscript impact

The DPDR prediction is ∎ under trunk axioms. The three hypotheses
(valence_cost > 0, loop_own_cost > 0, construction_overhead > 0)
are corollaries of IV + Lemma 2. Nesting and hysteresis are derived
theorems. The only empirical condition is the existence of two ActCost
(one for valence, one for the loop) — i.e., the loop and valence are
cycles with templates, which is exactly LIX (∎) and LXI (∎).

### Counter
20 theorems (incl. 2 private, 3 trunk replicas) · 0 sorry · 0 imports
-/

end DPDRDerived
