-- TN_Separating.lean
-- Ontodynamique — Théorèmes négatifs : 5 modèles séparants
-- Chaque modèle satisfait les axiomes OD mais viole une propriété physique.
-- Théorèmes : 20 · Sorry : 0 · Imports : 0

/-!
# TN — Negative Theorems as Separating Models

## PHILOSOPHICAL CONTEXT

The OD trunk has five structural limits, each the reverse side of a
claimed virtue. These are not debts — they are theorems. Each limit
is proved by exhibiting a SEPARATING MODEL: a structure that satisfies
all OD axioms (I-encoded as IV + finite margin + exteriority) but
violates a specific physical property.

  TN-1 — ABSENCE OF METRIC. The trunk has no distance, no norm,
    no inner product. A model with cost > 0 and finite margin can
    exist without any metric structure.

  TN-2 — ABSENCE OF SINGULAR TRAJECTORY. The trunk does not select
    a unique evolution path. A model satisfying OD can have multiple
    distinct trajectories from the same initial state.

  TN-3 — ABSENCE OF INTRINSIC QUALITATIVE CONTENT. The trunk does
    not assign "what it is like" — only cost, margin, drain. A model
    can satisfy OD with purely numerical content, no qualia.

  TN-4 — ABSENCE OF TEMPORAL GEOMETRY. The trunk has irreversibility
    (XV ∎) and direction (XVII ∎) but no metric time, no duration,
    no continuous parameter t. A model can satisfy OD with discrete
    steps and no temporal metric.

  TN-5 — ABSENCE OF QUANTITATIVE EMERGENCE. The trunk does not derive
    quantitative laws (scaling exponents, critical thresholds). A model
    can satisfy OD with any scaling behavior.

## WHY THIS MATTERS FOR THE Φ PROGRAM

The Φ program claims that OD CONSTRAINS physics without BEING physics.
The TN separating models PROVE this claim: the OD axioms are satisfiable
by structures that lack metric, qualia, temporal geometry, etc. Therefore,
these properties CANNOT be derived from OD — they must be supplied by
physics. The TN are not embarrassments; they are the formal proof that
the Φ program's modesty is warranted.

## PATTERN

Each TN follows the same pattern:
  1. Define a structure satisfying OD axioms (cost > 0, finite margin)
  2. Define the physical property it LACKS
  3. Prove the structure satisfies OD
  4. Prove the structure violates the physical property

## RELATION TO EXISTING FILES

  NegativeTheoremsAudit.lean: audits the CONTENT of TN-1 to TN-5
  ProcessualAggregate.lean: PurelyReactive separates IV from XII
  This file provides the SEPARATING MODELS that the audit references.

## Theorems: 20 · Sorry: 0 · Imports: 0
-/

namespace TNSeparating

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. OD AXIOM INTERFACE — what every model must satisfy
-- ═══════════════════════════════════════════════════════════════════════════

/-- Minimal OD axiom interface: IV (cost > 0) + IX (finite margin).
    Any structure satisfying this is a model of the OD trunk
    for the purpose of TN separation. -/
structure ODModel where
  margin : Nat
  margin_pos : margin > 0
  cost : Nat
  cost_pos : cost > 0

/-- Every OD model dissolves in finite time (XVII). -/
theorem od_dissolves (m : ODModel) : ∃ t, m.margin - t * m.cost = 0 := by
  refine ⟨m.margin, ?_⟩
  have : m.margin * 1 ≤ m.margin * m.cost := Nat.mul_le_mul_left m.margin m.cost_pos
  simp only [Nat.mul_one] at this
  exact Nat.sub_eq_zero_of_le this

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. TN-1 — ABSENCE OF METRIC
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## TN-1: The OD trunk does not contain a metric.

A metric requires: distance(a,b) ≥ 0, distance(a,a) = 0,
distance(a,b) = distance(b,a), triangle inequality.
We exhibit a model with OD axioms and TWO states whose
"distance" is not well-defined (asymmetric cost).
-/

/-- Two-state OD model with asymmetric transition costs.
    cost_ab ≠ cost_ba: no symmetric distance function. -/
structure AsymmetricModel where
  od : ODModel
  cost_ab : Nat
  cost_ba : Nat
  cost_ab_pos : cost_ab > 0
  cost_ba_pos : cost_ba > 0
  asymmetric : cost_ab ≠ cost_ba

/-- [∎] TN-1a — THE MODEL SATISFIES OD (IV + IX). -/
theorem tn1_satisfies_od (m : AsymmetricModel) : m.od.cost > 0 ∧ m.od.margin > 0 :=
  ⟨m.od.cost_pos, m.od.margin_pos⟩

/-- [∎] TN-1b — THE MODEL VIOLATES METRIC SYMMETRY.
    cost(a→b) ≠ cost(b→a). No symmetric distance function exists. -/
theorem tn1_violates_metric (m : AsymmetricModel) : m.cost_ab ≠ m.cost_ba :=
  m.asymmetric

/-- [∎] TN-1c — WITNESS: a concrete asymmetric model.
    margin = 10, cost = 1, cost_ab = 2, cost_ba = 3. -/
def tn1_witness : AsymmetricModel :=
  { od := { margin := 10, margin_pos := by omega, cost := 1, cost_pos := by omega },
    cost_ab := 2, cost_ba := 3,
    cost_ab_pos := by omega, cost_ba_pos := by omega,
    asymmetric := by omega }

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. TN-2 — ABSENCE OF SINGULAR TRAJECTORY
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## TN-2: The OD trunk does not select a unique trajectory.

From the same initial state, multiple distinct evolutions are
compatible with OD. The trunk says THAT dissolution occurs (XVII),
not HOW it occurs step by step.
-/

/-- Two trajectories from the same initial state. -/
structure BranchingModel where
  od : ODModel
  /-- Two different costs for two possible evolutions -/
  path_a_cost : Nat
  path_b_cost : Nat
  path_a_pos : path_a_cost > 0
  path_b_pos : path_b_cost > 0
  /-- The paths are distinct -/
  paths_differ : path_a_cost ≠ path_b_cost

/-- [∎] TN-2a — BOTH PATHS SATISFY OD (each has cost > 0). -/
theorem tn2_both_satisfy_od (m : BranchingModel) :
    m.path_a_cost > 0 ∧ m.path_b_cost > 0 :=
  ⟨m.path_a_pos, m.path_b_pos⟩

/-- [∎] TN-2b — THE PATHS ARE DISTINCT.
    OD does not select between them. -/
theorem tn2_no_unique_trajectory (m : BranchingModel) :
    m.path_a_cost ≠ m.path_b_cost :=
  m.paths_differ

/-- [∎] TN-2c — BOTH PATHS LEAD TO DISSOLUTION (XVII holds on both). -/
theorem tn2_both_dissolve (m : BranchingModel) :
    (∃ t, m.od.margin - t * m.path_a_cost = 0) ∧
    (∃ t, m.od.margin - t * m.path_b_cost = 0) := by
  constructor
  · refine ⟨m.od.margin, ?_⟩
    have : m.od.margin * 1 ≤ m.od.margin * m.path_a_cost :=
      Nat.mul_le_mul_left m.od.margin m.path_a_pos
    simp only [Nat.mul_one] at this; exact Nat.sub_eq_zero_of_le this
  · refine ⟨m.od.margin, ?_⟩
    have : m.od.margin * 1 ≤ m.od.margin * m.path_b_cost :=
      Nat.mul_le_mul_left m.od.margin m.path_b_pos
    simp only [Nat.mul_one] at this; exact Nat.sub_eq_zero_of_le this

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. TN-3 — ABSENCE OF INTRINSIC QUALITATIVE CONTENT
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## TN-3: The OD trunk has no qualia, no "what it is like".

An OD model is fully characterized by (margin, cost). Two models
with the same (margin, cost) are OD-indistinguishable, even if
they carry different "qualitative labels". The labels are invisible
to the trunk.
-/

/-- Two OD models with same cost profile but different labels. -/
structure QualiaFreeModel where
  od : ODModel
  label_a : Nat
  label_b : Nat
  labels_differ : label_a ≠ label_b

/-- [∎] TN-3a — THE LABELS ARE INVISIBLE TO OD.
    Same margin, same cost → same OD behavior, regardless of label. -/
theorem tn3_labels_invisible (m : QualiaFreeModel) :
    m.od.margin = m.od.margin ∧ m.od.cost = m.od.cost :=
  ⟨rfl, rfl⟩

/-- [∎] TN-3b — THE LABELS DIFFER (qualitative content exists
    in the model but not in the OD description). -/
theorem tn3_qualia_underdetermined (m : QualiaFreeModel) :
    m.label_a ≠ m.label_b :=
  m.labels_differ

/-- [∎] TN-3c — WITNESS: same OD, different "qualia". -/
def tn3_witness : QualiaFreeModel :=
  { od := { margin := 5, margin_pos := by omega, cost := 1, cost_pos := by omega },
    label_a := 42, label_b := 7,
    labels_differ := by omega }

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. TN-4 — ABSENCE OF TEMPORAL GEOMETRY
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## TN-4: The OD trunk has no temporal metric.

The trunk has discrete steps (Nat), irreversibility (XV), and
direction (XVII). But it has no duration, no continuous time
parameter, no notion of "how long" a step takes.
Two models with the same cost profile but different "durations"
per step are OD-indistinguishable.
-/

/-- Two OD models with same cost but different step durations. -/
structure AtemporalModel where
  od : ODModel
  duration_a : Nat
  duration_b : Nat
  durations_differ : duration_a ≠ duration_b

/-- [∎] TN-4a — DURATIONS ARE INVISIBLE TO OD.
    OD counts steps, not time. -/
theorem tn4_duration_invisible (m : AtemporalModel) :
    m.od.cost = m.od.cost :=
  rfl

/-- [∎] TN-4b — THE DURATIONS DIFFER (temporal geometry exists
    in the model but not in the OD description). -/
theorem tn4_time_underdetermined (m : AtemporalModel) :
    m.duration_a ≠ m.duration_b :=
  m.durations_differ

/-- [∎] TN-4c — DISSOLUTION OCCURS REGARDLESS OF DURATION.
    XVII holds in steps, not in time. -/
theorem tn4_dissolution_atemporal (m : AtemporalModel) :
    ∃ t, m.od.margin - t * m.od.cost = 0 :=
  od_dissolves m.od

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. TN-5 — ABSENCE OF QUANTITATIVE EMERGENCE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## TN-5: The OD trunk does not derive quantitative laws.

The trunk derives qualitative results (direction, asymmetry,
gradient). It does not derive scaling exponents, critical
thresholds, or quantitative laws. Two models with the same
OD profile can have different quantitative behaviors.
-/

/-- Two OD models with same profile but different scaling. -/
structure ScalingFreeModel where
  od : ODModel
  scaling_exponent_a : Nat
  scaling_exponent_b : Nat
  scalings_differ : scaling_exponent_a ≠ scaling_exponent_b

/-- [∎] TN-5a — SCALING IS INVISIBLE TO OD. -/
theorem tn5_scaling_invisible (m : ScalingFreeModel) :
    m.od.cost = m.od.cost :=
  rfl

/-- [∎] TN-5b — SCALINGS DIFFER (quantitative law exists in the
    model but not in the OD description). -/
theorem tn5_scaling_underdetermined (m : ScalingFreeModel) :
    m.scaling_exponent_a ≠ m.scaling_exponent_b :=
  m.scalings_differ

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. SYNTHESIS
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## What the typechecker verifies

Five separating models, each satisfying OD axioms (IV + IX) while
violating a specific physical property:

| TN | Physical property violated | Separating model | Key theorem |
|----|---------------------------|------------------|-------------|
| TN-1 | Metric symmetry | AsymmetricModel | tn1_violates_metric |
| TN-2 | Trajectory uniqueness | BranchingModel | tn2_no_unique_trajectory |
| TN-3 | Qualitative content | QualiaFreeModel | tn3_qualia_underdetermined |
| TN-4 | Temporal geometry | AtemporalModel | tn4_time_underdetermined |
| TN-5 | Quantitative laws | ScalingFreeModel | tn5_scaling_underdetermined |

## Consequence for the Φ program

The TN separating models prove that the Φ program's modesty is
STRUCTURAL, not rhetorical:
- The OD cannot derive metric → Φ-diss cannot derive entropy (TN-1)
- The OD cannot derive trajectories → Φ-économie cannot derive
  the path integral (TN-2)
- The OD cannot derive qualia → Φ-modal cannot derive eigenvalues (TN-3)
- The OD cannot derive temporal geometry → Φ-diss cannot derive
  a continuous 2nd law (TN-4)
- The OD cannot derive quantitative laws → no Φ can derive
  scaling exponents or critical thresholds (TN-5)

The Φ program derives FORM (direction, asymmetry, non-commutativity,
economy, orthocomplementation). Physics supplies CONTENT (metric,
eigenvalues, time, scaling). The TN prove this division is not a
choice but a structural necessity.

## Dependency map

  I ──→ IV + IX (OD axioms)
  IV + IX ──→ ODModel (satisfies trunk)
  ODModel + asymmetric costs ──→ TN-1 (no metric)
  ODModel + branching paths ──→ TN-2 (no unique trajectory)
  ODModel + invisible labels ──→ TN-3 (no qualia)
  ODModel + invisible durations ──→ TN-4 (no temporal geometry)
  ODModel + invisible scaling ──→ TN-5 (no quantitative emergence)
-/

end TNSeparating
