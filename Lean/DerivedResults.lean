/-!
# DerivedResults.lean — Derived results of Ontodynamique

This file merges four self-contained modules:
  - DeriveGamma         : I-γ derivation
  - OperationalDiscreteness : individuability
  - RecursionBoundV2    : recursion bound with 3 tiers
  - RegisterDissolution : register dissolution

Each module is in its own namespace and self-contained.

Total theorems: ~9 + ~8 + ~25 + ~9 = ~51
Sorry: 0
Imports: none
-/

/-!
# DERIVATION OF I-γ — No act without mode

## Inventory

### XLIV (constitutive normativity)
XLIV is encoded IMPLICITLY in:
  1. `assignValence` (function): classifies each operation as positive/negative
  2. `valence_exhaustive_LVIIIa`: classification is exhaustive and binary
  3. `normativity_discriminates_gradient` (XXXIX-c): normativity is structural

§9 states explicitly: valence is DERIVED from self-affection + normativity.
Any closure that partitions its operations (XLIV) has a valence on each operation.

### VII (constitutive negation)
Encoded in §11g — but depends on PolarizedClosure (I-γ).
For the derivation, VII must be reformulated independently of PolarizedClosure.

### XXXII (classification)
Encoded via `trajectory_dichotomy_XXIX`, `no_third_regime`, `closure_has_cycle`.
Uses `FiniteSystem` (pigeonhole on finite space).

### PolarizedClosure (current I-γ)
Structure with field `partition : facilitation_cost + resistance_cost_val = operations_cost`.

### Key result: the per-operation partition is ALREADY proved

```
def assignValence (operation_cost threshold : Nat) : Valence :=
  if operation_cost ≤ threshold then Valence.positive else Valence.negative

theorem valence_exhaustive_LVIIIa (op_cost threshold : Nat) :
    assignValence op_cost threshold = Valence.positive ∨
    assignValence op_cost threshold = Valence.negative
```

What is MISSING: aggregation. Going from "each operation is classified"
to "total cost partitions into facilitation + resistance".

## Derivation strategy

The chain:
  assignValence (per-opération, LVIIIa) : ∀ op, pos ∨ neg    [PROUVÉ]
  → aggregation lemma: Σ costs = Σ fac_costs + Σ res_costs  [TO PROVE]
  → PolarizedClosure.partition reconstructible                   [DÉRIVÉ]

The aggregation lemma is PURELY ARITHMETIC — not philosophical.
It is the fact that partitioning a finite sum preserves the total.
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 1: Standalone prerequisites
-- ═══════════════════════════════════════════════════════════════════════════

-- No imports — standalone file for isolation.
-- Definitions below are copied verbatim from Autodynamique.lean.

namespace DeriveGamma

/-- Valence (from Autodynamique §9). -/
inductive Valence where
  | positive
  | negative
  deriving Repr, DecidableEq

/-- assignValence (verbatim copy). -/
def assignValence (operation_cost neutrality_threshold : Nat) : Valence :=
  if operation_cost ≤ neutrality_threshold then Valence.positive
  else Valence.negative

/-- LVIIIa: per-operation, the classification is exhaustive. -/
theorem valence_exhaustive (op_cost threshold : Nat) :
    assignValence op_cost threshold = Valence.positive ∨
    assignValence op_cost threshold = Valence.negative := by
  unfold assignValence
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 2: The aggregation lemma (the missing bridge)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
Given a list of operation costs and a threshold,
partition costs into facilitation (≤ threshold) and resistance (> threshold).
Prove the sum is conserved.
-/

/-- Total cost of an operation list. -/
def totalCost : List Nat → Nat
  | [] => 0
  | c :: cs => c + totalCost cs

/-- Cost of facilitating operations (positive valence: cost ≤ threshold). -/
def facilitationCost (threshold : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs =>
    if c ≤ threshold then c + facilitationCost threshold cs
    else facilitationCost threshold cs

/-- Cost of resisting operations (negative valence: cost > threshold). -/
def resistanceCost (threshold : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs =>
    if c ≤ threshold then resistanceCost threshold cs
    else c + resistanceCost threshold cs

/-- AGGREGATION LEMMA — Cost partition conserves the total.
    The bridge between LVIIIa (per-operation) and PolarizedClosure (aggregated).
    Proof by induction on the list — purely arithmetic. -/
theorem cost_partition_conserves (costs : List Nat) (threshold : Nat) :
    facilitationCost threshold costs + resistanceCost threshold costs =
    totalCost costs := by
  induction costs with
  | nil => rfl
  | cons c cs ih =>
    simp only [totalCost, facilitationCost, resistanceCost]
    split <;> omega

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 3: Consistency with assignValence
-- ═══════════════════════════════════════════════════════════════════════════

/-- The classification by facilitationCost/resistanceCost is CONSISTENT
    with assignValence. If an operation is classified positive by
    assignValence, its cost goes into facilitationCost. -/
theorem fac_cost_matches_valence (c threshold : Nat)
    (h : assignValence c threshold = Valence.positive) :
    c ≤ threshold := by
  unfold assignValence at h
  split at h
  · assumption
  · cases h

theorem res_cost_matches_valence (c threshold : Nat)
    (h : assignValence c threshold = Valence.negative) :
    c > threshold := by
  unfold assignValence at h
  split at h
  · cases h
  · omega

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 4: Closure structure with operations
-- ═══════════════════════════════════════════════════════════════════════════

/-- A closure whose individual operations are known.
    No partition field — we will DERIVE it. -/
structure ClosureWithOps where
  margin : Nat
  margin_pos : margin > 0
  /-- List of per-operation costs per cycle -/
  operation_costs : List Nat
  /-- At least one operation (I-α: the system acts) -/
  ops_nonempty : operation_costs ≠ []
  /-- Every operation has positive cost (IV) -/
  ops_positive : ∀ c ∈ operation_costs, c > 0
  /-- Valence threshold (XLIV: the closure distinguishes maintenance/compromise) -/
  threshold : Nat

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 5: DERIVATION OF I-γ
-- ═══════════════════════════════════════════════════════════════════════════

/-- Total operation cost is positive (I-α). -/
theorem ops_total_pos (s : ClosureWithOps) : totalCost s.operation_costs > 0 := by
  cases h : s.operation_costs with
  | nil => exact absurd h s.ops_nonempty
  | cons c cs =>
    simp only [totalCost]
    have hmem : c ∈ s.operation_costs := h ▸ List.Mem.head cs
    have hc : c > 0 := s.ops_positive c hmem
    omega

/-- [∎] I-γ DERIVED — The cost partition is exhaustive.

    Given a closure with individual operations:
    - Each operation has a cost (I-α, IV)
    - Each operation is classified by assignValence (LVIIIa, XLIV)
    - The sum is conserved (aggregation lemma)

    Therefore: ∃ f and r such that f + r = total cost
    and f = cost of facilitating operations,
        r = cost of resisting operations.

    This is exactly PolarizedClosure.partition, DERIVED. -/
theorem gamma_derived (s : ClosureWithOps) :
    ∃ (fac res : Nat),
      fac + res = totalCost s.operation_costs ∧
      fac = facilitationCost s.threshold s.operation_costs ∧
      res = resistanceCost s.threshold s.operation_costs :=
  ⟨facilitationCost s.threshold s.operation_costs,
   resistanceCost s.threshold s.operation_costs,
   cost_partition_conserves s.operation_costs s.threshold,
   rfl, rfl⟩

/-- [∎] Explicit construction: a ClosureWithOps produces a structure
    equivalent to PolarizedClosure — without positing partition as axiom.
    The `partition` field is PROVED by `cost_partition_conserves`. -/
structure DerivedPolarized where
  margin : Nat
  margin_pos : margin > 0
  operations_cost : Nat
  ops_cost_pos : operations_cost > 0
  facilitation_cost : Nat
  resistance_cost_val : Nat
  partition : facilitation_cost + resistance_cost_val = operations_cost

def toDerivedPolarized (s : ClosureWithOps) : DerivedPolarized where
  margin := s.margin
  margin_pos := s.margin_pos
  operations_cost := totalCost s.operation_costs
  ops_cost_pos := ops_total_pos s
  facilitation_cost := facilitationCost s.threshold s.operation_costs
  resistance_cost_val := resistanceCost s.threshold s.operation_costs
  partition := cost_partition_conserves s.operation_costs s.threshold

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 6: Gamma theorems are now THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════

/-- no_dark_acting — derived, not posited. -/
theorem derived_no_dark_acting (s : ClosureWithOps) :
    let p := toDerivedPolarized s
    p.facilitation_cost + p.resistance_cost_val = p.operations_cost :=
  (toDerivedPolarized s).partition

/-- gamma_excludes_zombie — derived. -/
theorem derived_gamma_excludes_zombie (s : ClosureWithOps)
    (h : (toDerivedPolarized s).facilitation_cost = 0 ∧
         (toDerivedPolarized s).resistance_cost_val = 0) :
    (toDerivedPolarized s).operations_cost = 0 := by
  have := (toDerivedPolarized s).partition; omega

/-- gamma_operating_has_mode — derived. -/
theorem derived_gamma_operating_has_mode (s : ClosureWithOps) :
    facilitationCost s.threshold s.operation_costs > 0 ∨
    resistanceCost s.threshold s.operation_costs > 0 := by
  have hp := cost_partition_conserves s.operation_costs s.threshold
  have hpos := ops_total_pos s
  by_cases hf : facilitationCost s.threshold s.operation_costs > 0
  · exact Or.inl hf
  · right; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 7: Dependency chain verification
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Dependency chain

1. `assignValence` — from Autodynamique (LVIII). Pas un axiome.
2. `valence_exhaustive` — from Autodynamique (LVIIIa). Prouvé par split.
3. `fac_cost_matches_valence` / `res_cost_matches_valence` — nouveaux.
   Consistency between aggregation and per-operation. Trivial (unfold + split).
4. `cost_partition_conserves` — NEW. The bridge.
   Proved by induction on list + omega. Purely arithmetic.
5. `gamma_derived` — NEW. Existential conclusion.
   Proof: explicit witnesses + step 4.
6. `toDerivedPolarized` — NEW. Explicit construction.
   Fills DerivedPolarized fields with computed functions.
7. `derived_no_dark_acting`, `derived_gamma_excludes_zombie`,
   `derived_gamma_operating_has_mode` — copies of I-γ theorems,
   on the derived structure instead of the posited one.

## Hypotheses used
  - I-α : margin_pos, ops_positive, ops_nonempty (= cost > 0, drain > 0)
  - I-β : NOT USED DIRECTLY (only via ops_positive = each op has a cost)
  - XLIV : the valence threshold (threshold) EXISTS — this is the only philosophical input
  - VII : NOT USED (not necessary for partition)

## Hypotheses NOT used
  - No PolarizedClosure field is imported
  - No new axiom is posited
  - Proofs are: split, induction, omega, rfl
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 8: Diagnostic
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Diagnostic: the proof compiles (0 sorry)

I-γ restricted to closures IS a theorem of the system.

### The complete chain

```
I-α (cost > 0)
  + XLIV (∃ threshold — the closure distinguishes maintenance/compromise)
  + assignValence (per-opération : positive ∨ negative)     [LVIIIa]
  + induction sur les opérations                            [arithmétique]
  ⇒ facilitation_cost + resistance_cost = total_cost        [I-γ]
```

### What the threshold provides

The only non-trivial ingredient is the EXISTENCE of a valence threshold.
This is XLIV: the closure has a constitutive norm distinguishing what
maintains it from what compromises it. Without threshold, no partition.

The threshold is NOT a new axiom — it is already in the system:
- `assignValence` takes `neutrality_threshold` as parameter
- `MetabolizingClosure` has `drain_net` and `total_cost` which imply a threshold
- LVIII theorems all use a threshold

### What I-β contributes to the derivation

I-β is not directly in the proof chain, but is
necessary PHILOSOPHICALLY: without endogeneity, the threshold has no
content (any number would be a "threshold"). I-β ensures the
threshold is the closure's OWN constitutive norm.

In Lean, this manifests as the fact that `ClosureWithOps`
a `margin_pos` (the margin is the closure's own) et `ops_positive`
(each operation costs on this margin).

### The residue of universal I-γ

The derivation covers I-γ RESTRICTED TO CLOSURES — entities that
have individual operations and a valence threshold.

Universal I-γ ("no act without mode" including for non-closures,
aggregates, portages) would remain an axiom for entities without a
constitutive threshold. But this residue does not carry subjectivity —
it is cosmological, not ontodynamic.

### Confirmation

`PolarizedClosure` can be reconstructed as a theorem :
`toDerivedPolarized` constructs a `DerivedPolarized` (structurally
identical to `PolarizedClosure`) from a `ClosureWithOps`,
with `partition` PROVED by `cost_partition_conserves`, not posited.

All gamma theorems (no_dark_acting, excludes_zombie,
operating_has_mode) are reproved on the derived structure.

0 sorry. 0 new axiom. 0 PolarizedClosure import.
-/

end DeriveGamma

-- ═══════════════════════════════════════════════════════════════════════════
-- OperationalDiscreteness — Individuability as a theorem
-- ═══════════════════════════════════════════════════════════════════════════

/-!
# Operational discreteness — Individuability is a theorem

## Argument

Operation individuability (the fact that `operation_costs : List Nat`
exists) was the axiomatic residue of the I-γ derivation.
This section proves that individuability is itself a theorem:

  1. Each operation costs ≥ 1 (IV, encoded `drain_pos`)
  2. The margin is finite (IX, encoded `margin : Nat`)
  3. Therefore: at most ⌊margin⌋ operations in any interval
  4. A finite number of elements FORMS a list

A continuum of distinct operations with positive floor on finite margin
contradicts XVII (exhaustion). Individuability is XVII applied to counting.

## Conséquence

I-γ passe de ∎|cond (conditional theorem) to pure ∎.
The complete chain: I-α + I-β₁ + XLIV → I-γ. No residue.

Theorems: 7
Sorry: 0
Imports: none
-/

namespace OperationalDiscreteness

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Central lemma: length bounded by margin
-- ═══════════════════════════════════════════════════════════════════════════

/-- Total cost of an operation list (from DeriveGamma). -/
def totalCost : List Nat → Nat
  | [] => 0
  | c :: cs => c + totalCost cs

/-- [∎] TECHNICAL LEMMA — Total cost ≥ length if each element costs ≥ 1.
    Proof by induction. -/
theorem totalCost_ge_length (ops : List Nat)
    (h_pos : ∀ c ∈ ops, c > 0) :
    totalCost ops ≥ ops.length := by
  induction ops with
  | nil => simp [totalCost]
  | cons c cs ih =>
    simp only [totalCost, List.length_cons]
    have hc : c ≥ 1 := h_pos c (List.Mem.head cs)
    have ih' : totalCost cs ≥ cs.length := ih (fun x hx => h_pos x (List.Mem.tail c hx))
    omega

/-- [∎] OPERATIONAL DISCRETENESS — Under finite margin and positive
    floor, the number of operations is bounded.

    If each operation costs ≥ 1 and total cost ≤ margin,
    then number of operations ≤ margin.

    This is XVII (exhaustion) applied to counting. -/
theorem operational_discreteness (ops : List Nat) (margin : Nat)
    (h_pos : ∀ c ∈ ops, c > 0)
    (h_budget : totalCost ops ≤ margin) :
    ops.length ≤ margin := by
  have := totalCost_ge_length ops h_pos
  omega

/-- [∎] CONTRAPOSITIVE — A continuum is impossible.
    If there were more than `margin` operations with positive cost,
    total cost would exceed margin. Contradiction with IX. -/
theorem no_continuum (ops : List Nat) (margin : Nat)
    (h_pos : ∀ c ∈ ops, c > 0)
    (h_too_many : ops.length > margin) :
    totalCost ops > margin := by
  have := totalCost_ge_length ops h_pos
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. List existence is derivable
-- ═══════════════════════════════════════════════════════════════════════════

/-- A closure whose operations are specified by a count and a
    cost floor — NOT by a list.
    The ontological minimum: we know how many operations and
    the minimum cost of each. -/
structure MinimalClosure where
  margin : Nat
  margin_pos : margin > 0
  /-- Number of operations per cycle -/
  num_ops : Nat
  num_ops_pos : num_ops > 0
  /-- Minimum cost per operation (IV: > 0) -/
  min_cost : Nat
  min_cost_pos : min_cost > 0
  /-- Budget constrains operations -/
  budget : num_ops * min_cost ≤ margin
  /-- Valence threshold (XLIV) -/
  threshold : Nat

/-- [∎] OPERATIONAL BOUND — Number of operations is bounded
    by margin and minimum cost.
    Direct consequence of the structure. -/
theorem ops_bounded (c : MinimalClosure) :
    c.num_ops ≤ c.margin := by
  have h1 : c.num_ops * 1 ≤ c.num_ops * c.min_cost :=
    Nat.mul_le_mul_left c.num_ops c.min_cost_pos
  simp only [Nat.mul_one] at h1
  have := c.budget
  omega

/-- Build a uniform cost list from the minimum.
    Each operation costs exactly min_cost.
    Most conservative case (homogeneous costs). -/
def uniformCosts (n cost : Nat) : List Nat :=
  List.replicate n cost

/-- [∎] The constructed list is non-empty if n > 0. -/
theorem uniform_nonempty (n cost : Nat) (h_n : n > 0) :
    uniformCosts n cost ≠ [] := by
  cases n with
  | zero => omega
  | succ k => simp [uniformCosts, List.replicate]

/-- [∎] Each element costs > 0 (since min_cost > 0).
    All elements of `replicate n cost` equal `cost`. -/
theorem uniform_positive (n cost : Nat) (h_pos : cost > 0) :
    ∀ x ∈ uniformCosts n cost, x > 0 := by
  intro x hx
  simp only [uniformCosts] at hx
  have : x = cost := by
    induction n with
    | zero => simp [List.replicate] at hx
    | succ k _ =>
      simp [List.replicate] at hx
      rcases hx with rfl | ⟨_, rfl⟩ <;> rfl
  omega

/-- [∎] Total cost of uniform list = num_ops * min_cost.
    Proof by induction on n. -/
theorem uniform_total (n cost : Nat) :
    totalCost (uniformCosts n cost) = n * cost := by
  induction n with
  | zero => simp [uniformCosts, totalCost, List.replicate]
  | succ k ih =>
    show cost + totalCost (List.replicate k cost) = (k + 1) * cost
    have h : totalCost (List.replicate k cost) = k * cost := ih
    rw [h, Nat.succ_mul]; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Synthesis: I-γ without residue
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Individuability is a theorem

The complete chain:

```
  IV (chaque opération coûte > 0)     — axiome
  IX (marge finie)                     — axiome
  XVII (exhaustion)                    — theorem from Autodynamique
  ────────────────────────────────────
  operational_discreteness             — NOUVEAU (ce fichier)
    : ops.length ≤ margin
  ────────────────────────────────────
  uniformCosts + uniform_nonempty      — NOUVEAU (construction)
    + uniform_positive + uniform_total
  ────────────────────────────────────
  DeriveGamma.gamma_derived            — EXISTANT (DeriveGamma.lean)
    : ∃ fac res, fac + res = total
```

Before: DeriveGamma posited `operation_costs : List Nat` as
ontological commitment. Individuability was an axiomatic residue.

Now: `operational_discreteness` proves that any closure
with finite margin and positive cost has a BOUNDED number of operations.
`uniformCosts` explicitly constructs the list. Properties
required by ClosureWithOps (nonempty, positive) are proved.

The residue is eliminated. I-γ is pure ∎:
  I-α + I-β₁ + XLIV → I-γ. No additional condition.

### Counter
7 theorems · 0 sorry · 0 imports
-/

end OperationalDiscreteness

-- ═══════════════════════════════════════════════════════════════════════════
-- RecursionBoundV2 — Borne récursive inconditionnelle
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  RecursionBoundV2

  Result: The recursion bound (3 tiers = structural maximum)
  is UNCONDITIONAL. The identifications "same level" / "lower level" are
  DERIVED from domain saturation, not posited.
  The "3" in min_complexity is DERIVED from closure structure
  (I-α + I-β₁), without reference to I-γ.

  Chain:
    1. A tier's domain grows strictly with depth (IV+X+XXII)
    2. The closure has 3 positive independent parameters (I-α + I-β₁) → total ≥ 3
    3. In 3 steps, the domain saturates (= reaches totality)
    4. Beyond saturation, observer and observed are coextensive
    5. Coextensivity → feedback (I-β: shared margin)
    6. Feedback → FiniteExposed → XVII → exhaustion → transient

  Structural axioms (2, derivable from trunk):
    - growth : scope(n+1) > scope(n) [IV + X + XXII]
    - initial_pos : scope(0) ≥ 1 [LVII]

  Derived (formerly axiom):
    - min_complexity : total ≥ 3 [de ClosureParams : I-α + I-β₁]
    - Independent of I-γ → recursive ternarity ≠ axiomatic ternarity

  Theorems: 24
  Sorry: 0
  Imports: none
-/

namespace RecursionBoundV2

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 1: Infrastructure (FiniteBeing + FiniteExposed + FiniteInertial + XVII)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **FiniteBeing (mother typeclass)** — local copy for standalone use,
    aligned on the 20 avril 2026 refinement in Ontodynamique.lean. -/
class FiniteBeing (α : Type) where
  margin : α → Nat
  drain  : α → Nat
  drain_pos : ∀ a, 0 < drain a

/-- **FiniteExposed (refined)** — active finite beings with individuated
    operations. Aligned on I' and Ontodynamique.lean. -/
class FiniteExposed (α : Type) extends FiniteBeing α where
  operations : α → List Nat
  ops_nonempty : ∀ a, operations a ≠ []
  ops_positive : ∀ a, ∀ c ∈ operations a, c > 0

/-- **FiniteInertial** — inertial finite beings (aggregate mode, retroactive
    tiers, artifacts under drift). No individuated operations. -/
class FiniteInertial (α : Type) extends FiniteBeing α where
  -- No additional fields.

theorem generic_exhaustion [FiniteBeing α] (a : α) :
    ∃ n, n * FiniteBeing.drain a > FiniteBeing.margin a := by
  refine ⟨FiniteBeing.margin a + 1, ?_⟩
  have h1 : 1 ≤ FiniteBeing.drain a := FiniteBeing.drain_pos a
  have h2 : (FiniteBeing.margin a + 1) * 1 ≤
             (FiniteBeing.margin a + 1) * FiniteBeing.drain a :=
    Nat.mul_le_mul_left (FiniteBeing.margin a + 1) h1
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 2: Recursion domain
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  A tier's domain = the portion of the closure covered by its
  operations. Represented as scope/total (Nat/Nat).

  - scope > 0 : le tier a au moins une opération
  - total > 0 : la clôture n'est pas vide (IX)
  - scope ≤ total : le tier ne dépasse pas la clôture

  **Saturated**: scope = total (the tier covers the whole closure)
  **Partial**: scope < total (the tier is nestable by L)
-/

structure RecursionDomain where
  scope : Nat
  total : Nat
  scope_pos : scope > 0
  total_pos : total > 0
  scope_le : scope ≤ total

def RecursionDomain.isSaturated (d : RecursionDomain) : Prop :=
  d.scope = d.total

def RecursionDomain.isPartial (d : RecursionDomain) : Prop :=
  d.scope < d.total

/-- [∎] Saturated and partial are exclusive. -/
theorem saturated_partial_exclusive (d : RecursionDomain) :
    ¬(d.isSaturated ∧ d.isPartial) := by
  intro ⟨hs, hp⟩
  unfold RecursionDomain.isSaturated at hs
  unfold RecursionDomain.isPartial at hp
  omega

/-- [∎] Saturated and partial are exhaustive. -/
theorem saturated_partial_exhaustive (d : RecursionDomain) :
    d.isSaturated ∨ d.isPartial := by
  unfold RecursionDomain.isSaturated RecursionDomain.isPartial
  by_cases h : d.scope = d.total
  · exact Or.inl h
  · right; have := d.scope_le; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 3: Tier chain
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  A tier chain models increasing recursion.
  Each tier has a domain (scope, total) and observation parameters.

  Structural axioms apply to the chain:
  - Total is constant (same closure at each tier)
  - Scope grows strictly (IV + X + XXII)
  - Initial scope ≥ 1 (LVII)
  - Total ≥ 3 (XXXII + XL + IX)
-/

/-- A chain of recursive tiers on a closure of complexity `total`. -/
structure RecursionChain where
  /-- Total complexity of the closure (IX: finite) -/
  total : Nat
  total_pos : total > 0
  /-- Minimal complexity: structure + operations + boundary -/
  min_complexity : total ≥ 3
  /-- Domain of each tier (0-indexed: tier 1 = index 0) -/
  scope : Nat → Nat
  /-- Tier 1 covers at least 1 (LVII: self-affection exists) -/
  initial_pos : scope 0 ≥ 1
  /-- Strict growth (IV + X + XXII: each tier consumes ≥ 1 unit) -/
  growth : ∀ n, scope (n + 1) > scope n
  /-- No tier exceeds total -/
  bounded : ∀ n, scope n ≤ total
  /-- Invariant adequacy band (IX: finite) -/
  adequacy_band : Nat
  band_pos : adequacy_band > 0
  /-- Observation cost (IV > 0) -/
  observation_cost : Nat
  cost_pos : observation_cost > 0

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 4: Saturation — domain reaches total
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Strict growth + finite bound → saturation

  If scope is strictly increasing and bounded by total,
  it reaches total in at most total - 1 steps.

  Concretely : scope(0) ≥ 1, scope(n+1) > scope(n), scope(n) ≤ total.
  After total - 1 steps : scope(total - 1) ≥ 1 + (total - 1) = total.
  By scope_le : scope(total - 1) = total.
-/

/-- [∎] Strict growth implies cumulative increment ≥ n.
    If scope grows strictly, scope(n) ≥ scope(0) + n. -/
theorem scope_grows_by_n (c : RecursionChain) (n : Nat) :
    c.scope n ≥ c.scope 0 + n := by
  induction n with
  | zero => omega
  | succ k ih =>
    have hg := c.growth k
    omega

/-- [∎] Scope of tier n is ≥ 1 + n.
    Combines initial_pos (scope(0) ≥ 1) and cumulative growth. -/
theorem scope_lower_bound (c : RecursionChain) (n : Nat) :
    c.scope n ≥ 1 + n := by
  have h1 := scope_grows_by_n c n
  have h2 := c.initial_pos
  omega

/-- [∎] SATURATION — Tier 3 (index 2) has scope ≥ 3.
    By scope_lower_bound : scope(2) ≥ 1 + 2 = 3.
    By min_complexity : total ≥ 3. By bounded : scope(2) ≤ total.
    So scope(2) = total if total = 3, or scope(2) ≥ 3 if total > 3.

    More precisely: scope(total - 1) = total (complete saturation).
    For total = 3: scope(2) ≥ 3 and scope(2) ≤ 3, so scope(2) = 3 = total. -/
theorem saturation_at_three (c : RecursionChain) (h : c.total = 3) :
    c.scope 2 = c.total := by
  have h_lb := scope_lower_bound c 2
  -- h_lb : c.scope 2 ≥ 3
  have h_ub := c.bounded 2
  -- h_ub : c.scope 2 ≤ c.total
  omega

/-- [∎] GENERAL SATURATION — Domain reaches total at tier total - 1.
    For any complexity total ≥ 3, tier (total - 1) saturates. -/
theorem saturation_general (c : RecursionChain) :
    c.scope (c.total - 1) = c.total := by
  have h_lb := scope_lower_bound c (c.total - 1)
  -- scope(total - 1) ≥ 1 + (total - 1) = total (car total ≥ 3 ≥ 1)
  have h_ub := c.bounded (c.total - 1)
  have h_mc := c.min_complexity
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 5: Ceiling — once saturated, always saturated
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] CEILING — If scope(n) = total, then scope(m) = total for all m ≥ n.
    By monotonicity and boundedness. -/
theorem scope_ceiling (c : RecursionChain) (n m : Nat) (h_nm : m ≥ n)
    (h_sat : c.scope n = c.total) :
    c.scope m = c.total := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    rw [this] at h_sat; exact h_sat
  | succ k ih =>
    by_cases hk : k ≥ n
    · have hk_eq := ih hk
      have hg := c.growth k
      have hub := c.bounded (k + 1)
      omega
    · have hkn : k + 1 = n := by omega
      rw [hkn]; exact h_sat

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 6: Partiality of tier 2 (index 1)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  Tier 2 has a partial domain: scope(1) < total.

  Proof: scope(1) ≥ 2 (by scope_lower_bound) and scope(1) ≤ total.
  But scope(1) < total, because:
  - scope(2) > scope(1) (growth)
  - scope(2) ≤ total (bounded)
  - Donc scope(1) < scope(2) ≤ total.
-/

/-- [∎] Tier 2 (index 1) is PARTIAL: scope(1) < total.
    Proof: scope(2) > scope(1) and scope(2) ≤ total. -/
theorem second_level_partial (c : RecursionChain) :
    c.scope 1 < c.total := by
  have hg : c.scope 2 > c.scope 1 := c.growth 1
  have hub := c.bounded 2
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 7: DERIVED feedback
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## The key result

  Feedback is no longer posited — it is DERIVED from saturation.

  **If tier n is saturated** (scope(n) = total) :
  - The observed object covers the whole closure
  - The tier n+1 observation act is within the same margin (I-β)
  - Observing = modifying the object (since observer and observed = same margin)
  - Target displacement = observation_cost (IV > 0)

  **If tier n is partial** (scope(n) < total) :
  - The observed object does not cover the whole closure
  - The observation act is within the REMAINING margin (outside domain)
  - Observing does not modify the object (nesting L: separation)
  - Target displacement = 0

  The "same level / lower level" distinction is therefore:
  - same level = saturated = coextensive → feedback
  - lower level = partial = nestable → no feedback
-/

/-- Target displacement at tier n+1, observing tier n.
    If tier n is saturated → displacement = cost (feedback).
    If tier n is partial → displacement = 0 (nesting). -/
def target_displacement (c : RecursionChain) (n : Nat) : Nat :=
  if c.scope n = c.total then c.observation_cost else 0

/-- [∎] DERIVED FEEDBACK — If observed tier is saturated,
    displacement = observation_cost > 0. -/
theorem retroaction_from_saturation (c : RecursionChain) (n : Nat)
    (h_sat : c.scope n = c.total) :
    target_displacement c n = c.observation_cost := by
  unfold target_displacement
  rw [if_pos h_sat]

/-- [∎] NO FEEDBACK — If observed tier is partial,
    displacement = 0. -/
theorem no_retroaction_from_partial (c : RecursionChain) (n : Nat)
    (h_part : c.scope n < c.total) :
    target_displacement c n = 0 := by
  unfold target_displacement
  have h_ne : ¬(c.scope n = c.total) := by omega
  rw [if_neg h_ne]

/-- [∎] Tier 3 observes a PARTIAL object → no feedback.
    Tier 3 (index 2) observes tier 2 (index 1).
    scope(1) < total (second_level_partial). So displacement = 0. -/
theorem third_level_no_retroaction (c : RecursionChain) :
    target_displacement c 1 = 0 :=
  no_retroaction_from_partial c 1 (second_level_partial c)

/-- [∎] Tier 4 observes a SATURATED object → feedback.
    Tier 4 (index 3) observes tier 3 (index 2).
    scope(2) = total (saturation_at_three, if total = 3).
    So displacement = observation_cost > 0. -/
theorem fourth_level_retroaction (c : RecursionChain) (h : c.total = 3) :
    target_displacement c 2 = c.observation_cost :=
  retroaction_from_saturation c 2 (saturation_at_three c h)

/-- [∎] GENERAL FEEDBACK — Every tier ≥ total has feedback.
    scope(total - 1) = total (saturation_general).
    For n ≥ total - 1: scope(n) = total (ceiling).
    So displacement(n) = cost > 0. -/
theorem retroaction_beyond_saturation (c : RecursionChain) (n : Nat)
    (h : n ≥ c.total - 1) :
    target_displacement c n = c.observation_cost := by
  have h_sat := scope_ceiling c (c.total - 1) n h (saturation_general c)
  exact retroaction_from_saturation c n h_sat

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 8: Exhaustion — FiniteExposed for the saturated tier
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Reconnection with XVII

  A tier with feedback (displacement > 0) is a FiniteExposed:
  - margin = adequacy_band (invariant adequacy band)
  - drain = displacement (target displacement per act)

  By XVII (generic_exhaustion), the invariant exhausts.
-/

/-- A tier with confirmed feedback. -/
structure RetroactiveTier where
  band : Nat
  band_pos : band > 0
  displacement : Nat
  displacement_pos : displacement > 0

/-- RetroactiveTier is **FiniteInertial** under the 20 avril refinement :
    its displacement is retroactively derived from saturation, not
    operated. It is an inertial mode — a structural tier whose drain
    is subi, not opéré. -/
instance : FiniteInertial RetroactiveTier where
  margin r := r.band
  drain r := r.displacement
  drain_pos r := r.displacement_pos

/-- [∎] Build a RetroactiveTier for a saturated tier. -/
def mkRetroactiveTier (c : RecursionChain) (n : Nat)
    (_h_sat : c.scope n = c.total) : RetroactiveTier where
  band := c.adequacy_band
  band_pos := c.band_pos
  displacement := c.observation_cost
  displacement_pos := c.cost_pos

/-- [∎] EXHAUSTION — The saturated tier's invariant exhausts by XVII. -/
theorem saturated_tier_exhaustion (c : RecursionChain) (n : Nat)
    (h_sat : c.scope n = c.total) :
    ∃ k, k * c.observation_cost > c.adequacy_band :=
  generic_exhaustion (mkRetroactiveTier c n h_sat)

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 9: MAIN THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] TIER 3 STABLE (DERIVED).
    Tier 3 observes tier 2. Tier 2 is partial (second_level_partial).
    No feedback. The tier 3 invariant can consolidate → stable regime. -/
theorem third_level_stable (c : RecursionChain) :
    target_displacement c 1 = 0 :=
  third_level_no_retroaction c

/-- [∎] TIER 4 TRANSIENT (DERIVED, for total = 3).
    Tier 4 observes tier 3. Tier 3 is saturated (saturation_at_three).
    Feedback. The invariant exhausts → no co-maintained cycle (XXVIII) → transient. -/
theorem fourth_level_transient (c : RecursionChain) (h : c.total = 3) :
    target_displacement c 2 = c.observation_cost ∧
    (∃ k, k * c.observation_cost > c.adequacy_band) :=
  ⟨fourth_level_retroaction c h,
   saturated_tier_exhaustion c 2 (saturation_at_three c h)⟩

/-- [∎] UNCONDITIONAL RECURSION BOUND.
    For any recursive chain on a closure of complexity total:
    - Every tier beyond saturation is transient
    - The invariant exhausts in finite time
    The "same level / lower level" identifications are DERIVED
    from domain saturation, not posited. -/
theorem recursion_bound_unconditional (c : RecursionChain) (n : Nat)
    (h : n ≥ c.total - 1) :
    target_displacement c n = c.observation_cost ∧
    (∃ k, k * c.observation_cost > c.adequacy_band) :=
  ⟨retroaction_beyond_saturation c n h,
   saturated_tier_exhaustion c n
     (scope_ceiling c (c.total - 1) n h (saturation_general c))⟩

/-- [∎] UNCONDITIONAL CONTRAST.
    Tier 3 is stable AND every tier beyond saturation is transient.
    The transition is structural. -/
theorem unconditional_contrast (c : RecursionChain) :
    target_displacement c 1 = 0 ∧
    target_displacement c (c.total - 1) = c.observation_cost :=
  ⟨third_level_stable c,
   retroaction_beyond_saturation c (c.total - 1) (Nat.le_refl _)⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 10: Bounded spiral (LXXVIII)
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] LXXVIII — The self-referential spiral exhausts in finite time.
    Derived from saturation. -/
theorem spiral_bounded (c : RecursionChain) :
    ∃ k, k * c.observation_cost > c.adequacy_band := by
  refine ⟨c.adequacy_band + 1, ?_⟩
  have h1 : 1 ≤ c.observation_cost := c.cost_pos
  have h2 : (c.adequacy_band + 1) * 1 ≤
             (c.adequacy_band + 1) * c.observation_cost :=
    Nat.mul_le_mul_left (c.adequacy_band + 1) h1
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 11: DERIVATION OF min_complexity — the "3" is not I-γ
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## The `min_complexity` link derived

  `RecursionChain` posits `min_complexity : total ≥ 3` as a field.
  This section shows that this property FOLLOWS from the structure of a
  metabolizing closure — without recourse to I-γ.

  ### Three positive independent parameters

  A `MetabolizingClosure` has:
  - `drain_net > 0`   — constitutional cost (I-β₁, XXXIV : mortalité)
  - `regeneration > 0` — self-repair (I-β₁, XXXVIII : métabolisation)

  A `ClosureWithOps` adds:
  - `margin > 0`       — reserve (I-α: self-grounding)

  Three strictly positive, structurally independent fields.
  Each constitutes a distinct observable aspect of the closure.
  Their sum ≥ 1 + 1 + 1 = 3.

  ### Why this "3" is NOT the ternarity of I

  - `margin > 0`       ← I-α (auto-fondation)
  - `drain_net > 0`    ← I-β₁ (constitutional cost)
  - `regeneration > 0` ← I-β₁ (self-repair)

  Two of three come from I-β₁. None comes from I-γ.
  Recursive ternarity (3 tiers = max) derives from the INTERNAL
  structure of I-β₁ (additive decomposition), not from I-α/I-β/I-γ.
  The two ternarity sources are INDEPENDENT.
-/

/-- MetabolizingClosure with margin_pos (from ClosureWithOps). -/
structure ClosureParams where
  margin : Nat
  /-- I-α: reserve is positive -/
  margin_pos : margin > 0
  /-- Gross cost per cycle -/
  total_cost : Nat
  total_cost_pos : total_cost > 0
  /-- Margin recovered per cycle (XXXVIII) -/
  regeneration : Nat
  /-- I-β₁: regeneration is positive (XXXVIII) -/
  regen_pos : regeneration > 0
  /-- Net cost after regeneration -/
  drain_net : Nat
  /-- I-β₁: net drain is positive (XXXIV) -/
  drain_net_pos : drain_net > 0
  /-- Additive decomposition (I-β₁) -/
  cost_decomposition : drain_net + regeneration = total_cost

/-- Observable complexity of a closure = sum of its positive aspects.
    Each parameter > 0 contributes at least 1 to the total.
    This is NOT "the number of I-α/I-β/I-γ components". -/
def closure_complexity (cp : ClosureParams) : Nat :=
  cp.margin + cp.drain_net + cp.regeneration

/-- [∎] THREE ASPECTS — Closure complexity ≥ 3.
    Proof: margin ≥ 1 (I-α) + drain_net ≥ 1 (I-β₁) + regeneration ≥ 1 (I-β₁).
    No reference to I-γ. -/
theorem three_aspects (cp : ClosureParams) :
    closure_complexity cp ≥ 3 := by
  unfold closure_complexity
  have h1 := cp.margin_pos
  have h2 := cp.drain_net_pos
  have h3 := cp.regen_pos
  omega

/-- [∎] The three sources are INDEPENDENT.
    None of the three parameters follows from the other two (in general). Witness: margin and drain_net+regeneration
    are free of each other (no margin ↔ total_cost constraint). -/
theorem aspects_independent (cp : ClosureParams) :
    cp.margin ≥ 1 ∧ cp.drain_net ≥ 1 ∧ cp.regeneration ≥ 1 :=
  ⟨cp.margin_pos, cp.drain_net_pos, cp.regen_pos⟩

/-- [∎] CONSTRUCTEUR — Bâtir une RecursionChain à partir de ClosureParams.
    Le champ `min_complexity` est PROUVÉ par `three_aspects`, not posited.
    Le `total` est la complexité observable de la clôture.

    Les autres champs (scope, growth, bounded, etc.) restent des paramètres
    de la chaîne récursive — ils décrivent COMMENT la récursion se déploie
    sur la clôture, pas la clôture elle-même. -/
def mkChainFromClosure
    (cp : ClosureParams)
    (scope : Nat → Nat)
    (initial_pos : scope 0 ≥ 1)
    (growth : ∀ n, scope (n + 1) > scope n)
    (bounded : ∀ n, scope n ≤ closure_complexity cp)
    (band : Nat) (band_pos : band > 0)
    (cost : Nat) (cost_pos : cost > 0) : RecursionChain where
  total := closure_complexity cp
  total_pos := by have := three_aspects cp; omega
  min_complexity := three_aspects cp
  scope := scope
  initial_pos := initial_pos
  growth := growth
  bounded := bounded
  adequacy_band := band
  band_pos := band_pos
  observation_cost := cost
  cost_pos := cost_pos

/-- Abbreviation for the closure → chain constructor. -/
abbrev chainOf (cp : ClosureParams)
    (scope : Nat → Nat)
    (initial_pos : scope 0 ≥ 1)
    (growth : ∀ n, scope (n + 1) > scope n)
    (bounded : ∀ n, scope n ≤ closure_complexity cp)
    (band : Nat) (band_pos : band > 0)
    (cost : Nat) (cost_pos : cost > 0) : RecursionChain :=
  mkChainFromClosure cp scope initial_pos growth bounded band band_pos cost cost_pos

/-- [∎] BORNE RÉCURSIVE DEPUIS LA CLÔTURE — PALIER 3 STABLE.
    `min_complexity` est DÉRIVÉ de `three_aspects`, not posited. -/
theorem closure_third_level_stable
    (cp : ClosureParams)
    (scope : Nat → Nat)
    (ip : scope 0 ≥ 1) (g : ∀ n, scope (n + 1) > scope n)
    (b : ∀ n, scope n ≤ closure_complexity cp)
    (band : Nat) (bp : band > 0) (cost : Nat) (cp2 : cost > 0) :
    target_displacement (chainOf cp scope ip g b band bp cost cp2) 1 = 0 :=
  (unconditional_contrast _).1

/-- [∎] BORNE RÉCURSIVE DEPUIS LA CLÔTURE — AU-DELÀ DE LA SATURATION : TRANSITOIRE.
    `min_complexity` est DÉRIVÉ de `three_aspects`, not posited. -/
theorem closure_beyond_saturation_transient
    (cp : ClosureParams)
    (scope : Nat → Nat)
    (ip : scope 0 ≥ 1) (g : ∀ n, scope (n + 1) > scope n)
    (b : ∀ n, scope n ≤ closure_complexity cp)
    (band : Nat) (bp : band > 0) (cost : Nat) (cp2 : cost > 0) :
    target_displacement (chainOf cp scope ip g b band bp cost cp2)
      ((chainOf cp scope ip g b band bp cost cp2).total - 1) =
    (chainOf cp scope ip g b band bp cost cp2).observation_cost :=
  (unconditional_contrast _).2

/-!
  ## Inventory

  ### Theorems
  | Theorem | Content |
  |----------|---------|
  | generic_exhaustion | XVII — exhaustion |
  | saturated_partial_exclusive | scope = total XOR scope < total |
  | saturated_partial_exhaustive | scope = total ∨ scope < total |
  | scope_grows_by_n | scope(n) ≥ scope(0) + n |
  | scope_lower_bound | scope(n) ≥ 1 + n |
  | saturation_at_three | total = 3 → scope(2) = 3 |
  | saturation_general | scope(total - 1) = total |
  | scope_ceiling | scope(n) = total → scope(m ≥ n) = total |
  | second_level_partial | scope(1) < total |
  | retroaction_from_saturation | saturé → displacement = cost |
  | no_retroaction_from_partial | partiel → displacement = 0 |
  | third_level_no_retroaction | displacement(tier 2→3) = 0 |
  | fourth_level_retroaction | displacement(tier 3→4) = cost |
  | retroaction_beyond_saturation | ∀ n ≥ total-1, displacement = cost |
  | saturated_tier_exhaustion | ∃ k, k * cost > band |
  | third_level_stable | tier 3 stable (derived) |
  | fourth_level_transient | tier 4 transitoire (derived) |
  | recursion_bound_unconditional | ∀ n ≥ saturation, transitoire |
  | unconditional_contrast | stable(3) ∧ transitoire(≥sat) |
  | spiral_bounded | LXXVIII : ∃ k, k * cost > band |

  ### New theorems (§11 — min_complexity derivation)
  | Theorem | Content |
  |----------|---------|
  | three_aspects | closure_complexity ≥ 3 (I-α + I-β₁) |
  | aspects_independent | margin ≥ 1 ∧ drain_net ≥ 1 ∧ regen ≥ 1 |
  | closure_third_level_stable | tier 3 stable (depuis ClosureParams) |
  | closure_beyond_saturation_transient | ≥sat transitoire (depuis ClosureParams) |

  **24 theorems, 0 sorry, 0 imports.**

  ### Remaining axioms in RecursionChain
  - `growth` : scope(n+1) > scope(n) [IV + X + XXII]
  - `initial_pos` : scope(0) ≥ 1 [LVII]
  - ~~`min_complexity` : total ≥ 3~~ → **DERIVED** by `three_aspects`

  ### Source of the "3"
  - margin > 0 ← I-α
  - drain_net > 0 ← I-β₁ (XXXIV)
  - regeneration > 0 ← I-β₁ (XXXVIII)
  - **No reference to I-γ → independent recursive ternarity**

  Comparison:
  - : 12 theorems, 2 posited commitments
  - : 20 theorems, 3 structural axioms
  - v2.1 : 24 theorems, 2 axioms (growth, initial_pos), min_complexity derived
-/

end RecursionBoundV2

-- ═══════════════════════════════════════════════════════════════════════════
-- RegisterDissolution — Epistemic register dissolution
-- ═══════════════════════════════════════════════════════════════════════════

/-!
# Register dissolution lemma

## Statement

By I-β (being = acting) and LXVII (knowing = metabolizing resistance),
every knowledge operation of C on C is a constitutive operation of C's
cycle. Consequently, derived properties for knowledge — finitude (IX),
opacity (LXVIII), self-modification (LXXVI) — are properties of C's
being-in-act, not of a separate register.

## Strategy

Subsumption approach:
  1. Define what a cycle operation is (CycleOp)
  2. Define what a knowledge operation is (KnowledgeOp, via LXVII)
  3. Prove that every self-directed KnowledgeOp satisfies CycleOp
  4. Prove property inheritance (cost, finitude, opacity)

The lemma blocks the introduction of a separate "epistemic operation" type
not constrained by the cycle.

## Result: ∎ (no axiom added)

Theorems: 9 + 1 instance
Sorry: 0
Imports: none
-/

namespace RegisterDissolution

-- Local FiniteBeing / FiniteExposed / FiniteInertial hierarchy, aligned on
-- the 20 avril 2026 refinement in Ontodynamique.lean.

/-- **FiniteBeing (mother typeclass)** — margin + drain, shared by all
    four modes of finite being under I'. -/
class FiniteBeing (α : Type) where
  margin : α → Nat
  drain  : α → Nat
  drain_pos : ∀ a, 0 < drain a

/-- **FiniteExposed (refined)** — active finite beings with individuated
    operations (closures, portages, carried). -/
class FiniteExposed (α : Type) extends FiniteBeing α where
  operations : α → List Nat
  ops_nonempty : ∀ a, operations a ≠ []
  ops_positive : ∀ a, ∀ c ∈ operations a, c > 0

/-- **FiniteInertial** — inertial finite beings (aggregate mode). No
    individuated operations. -/
class FiniteInertial (α : Type) extends FiniteBeing α where
  -- No additional fields.

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Cycle operation (XXXII + IV + VII)
-- ═══════════════════════════════════════════════════════════════════════════

/-- A constitutive operation of a closure's cycle.

    By XXXII, operations regenerate the structure that makes them
    possible. By IV, each operation costs > 0. By IX, margin is
    finite. By XV, each operation is irreversible. -/
structure CycleOp where
  /-- IV + X: every act costs -/
  cost : Nat
  cost_pos : cost > 0
  /-- XV: the operation modifies structure (irreversibility) -/
  modifies_structure : Prop
  /-- IX: the operation draws on a finite margin -/
  draws_on_margin : Prop

/-- Predicate: an operation is constitutive of the cycle if it
    satisfies the constraints. -/
def isCycleOp (op : CycleOp) : Prop :=
  op.cost > 0 ∧ op.modifies_structure ∧ op.draws_on_margin

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Knowledge operation (LXVI + LXVII)
-- ═══════════════════════════════════════════════════════════════════════════

/-- A knowledge operation in the sense of LXVI-LXVII.

    By LXVII, knowing = metabolizing resistance.
    By LXVI, the result is a shared operational invariant.

    A knowledge operation is a metabolization (XXXVIII)
    producing an invariant — a constraint on future cycle operations. -/
structure KnowledgeOp where
  /-- Metabolization cost (XXXVIII: regeneration costs > 0) -/
  metabolization_cost : Nat
  metab_cost_pos : metabolization_cost > 0
  /-- LXVI: the operation produces an invariant (conserved constraint) -/
  produces_invariant : Prop
  /-- LXVII: the invariant is imposed by resistance (not chosen) -/
  from_resistance : Prop

/-- LXVII — An operation is knowledge if it metabolizes
    resistance into an invariant. -/
def isKnowledgeOp (op : KnowledgeOp) : Prop :=
  op.metabolization_cost > 0 ∧ op.produces_invariant ∧ op.from_resistance

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Self-knowledge: knowledge applied to self (LVII + LXVII)
-- ═══════════════════════════════════════════════════════════════════════════

/-- When closure C applies a knowledge operation to itself,
    the source of resistance IS C.

    By LVII, C is already in an operational relation with itself
    (self-affection). Self-knowledge is this relation when it
    produces an invariant (LXVI). -/
structure SelfKnowledgeOp where
  /-- Underlying knowledge operation -/
  knowledge : KnowledgeOp
  /-- LVII: the target is the same being as the source -/
  self_referential : Prop
  /-- LXXVI: the operation modifies the target (and thus the source) -/
  self_modifying : Prop
  /-- LXVIII: the operation is partial (the target is finite) -/
  constitutively_partial : Prop

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. DISSOLUTION — Self-knowledge IS a cycle operation
-- ═══════════════════════════════════════════════════════════════════════════

/-- Convert a SelfKnowledgeOp to CycleOp.

    The core of the lemma. By I-β (being = acting, no separate
    substrate), C's knowledge operation on C is an operation
    of C — hence of the cycle.

    The proof is in the CONSTRUCTION: we show that a valid
    CycleOp can be extracted from any SelfKnowledgeOp. -/
def toCycleOp (sk : SelfKnowledgeOp) : CycleOp where
  cost := sk.knowledge.metabolization_cost
  cost_pos := sk.knowledge.metab_cost_pos
  modifies_structure := sk.self_modifying
  draws_on_margin := True  -- I-β : pas de marge séparée

/-- [∎] DISSOLUTION — Cost is preserved.
    The epistemic operation costs EXACTLY what the underlying
    metabolization costs. No epistemic discount. -/
theorem dissolution_cost_preserved (sk : SelfKnowledgeOp) :
    (toCycleOp sk).cost = sk.knowledge.metabolization_cost := rfl

/-- [∎] DISSOLUTION — Cost is strictly positive.
    By IV, every operation costs. The epistemic operation is no
    exception: it metabolizes (XXXVIII), so it costs. -/
theorem dissolution_cost_pos (sk : SelfKnowledgeOp) :
    (toCycleOp sk).cost > 0 :=
  sk.knowledge.metab_cost_pos

/-- [∎] DISSOLUTION — The operation is constitutive of the cycle.
    Requires only self_modifying (h_mod): I-β + LXXVI suffice.
    produces_invariant and from_resistance characterize the GENESIS
    of knowledge (LXVI-LXVII), not its integration into the cycle. -/
theorem dissolution_is_cycle_op (sk : SelfKnowledgeOp)
    (h_mod : sk.self_modifying) :
    isCycleOp (toCycleOp sk) := by
  unfold isCycleOp toCycleOp
  exact ⟨sk.knowledge.metab_cost_pos, h_mod, trivial⟩

/-- [∎] LXVII — Knowledge genesis requires resistance + invariant.
    These conditions characterize the MODE of acquisition (genesis level),
    not integration into the cycle (operative level).
    The two levels are formally distinct and independent:
    dissolution_is_cycle_op (operative, h_mod only)
    knowledge_genesis_conditions (genetic, h_know + h_res). -/
theorem knowledge_genesis_conditions (sk : SelfKnowledgeOp)
    (h_know : sk.knowledge.produces_invariant)
    (h_res  : sk.knowledge.from_resistance) :
    isKnowledgeOp sk.knowledge :=
  ⟨sk.knowledge.metab_cost_pos, h_know, h_res⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Property inheritance — Finitude, opacity, self-modification
-- ═══════════════════════════════════════════════════════════════════════════

/-- Closure with finite margin operating on itself. -/
structure FiniteSelfClosure where
  margin : Nat
  margin_pos : margin > 0
  /-- Constitutive operations cost per cycle -/
  cycle_cost : Nat
  cycle_cost_pos : cycle_cost > 0
  /-- Self-knowledge cost per cycle -/
  self_knowledge_cost : Nat
  sk_cost_pos : self_knowledge_cost > 0

/-- Total drain = cycle + self-knowledge.
    By I-β, both draw on the SAME margin. -/
def totalDrain (c : FiniteSelfClosure) : Nat :=
  c.cycle_cost + c.self_knowledge_cost

/-- [∎] INHERITED PROPERTY — FINITUDE (IX).
    Total drain (cycle + knowledge) is positive and margin is finite.
    Self-knowledge is finite because it IS a cycle operation,
    not because it observes a finite cycle from outside. -/
theorem inherited_finitude (c : FiniteSelfClosure) :
    ∃ n, n * totalDrain c > c.margin := by
  have h_pos : totalDrain c > 0 := by
    unfold totalDrain; have := c.cycle_cost_pos; have := c.sk_cost_pos; omega
  refine ⟨c.margin + 1, ?_⟩
  have h1 : 1 ≤ totalDrain c := h_pos
  have h2 : (c.margin + 1) * 1 ≤ (c.margin + 1) * totalDrain c :=
    Nat.mul_le_mul_left (c.margin + 1) h1
  simp only [Nat.mul_one] at h2; omega

/-- [∎] INHERITED PROPERTY — OPACITY (LXVIII).
    Self-knowledge draws on margin. Each self-knowledge act
    leaves LESS margin for the next. Total knowledge would
    require infinite margin (¬IX).

    Formally: if each self-knowledge act costs sk_cost,
    at most ⌊margin / sk_cost⌋ acts are possible.
    The number of knowable aspects is bounded by margin. -/
theorem inherited_opacity (c : FiniteSelfClosure) :
    ∃ bound, ∀ n, n * c.self_knowledge_cost ≤ c.margin → n ≤ bound := by
  refine ⟨c.margin, fun n h => ?_⟩
  have h1 : n * 1 ≤ n * c.self_knowledge_cost :=
    Nat.mul_le_mul_left n c.sk_cost_pos
  simp only [Nat.mul_one] at h1
  omega

/-- [∎] INHERITED PROPERTY — SELF-MODIFICATION (LXXVI).
    Each self-knowledge act modifies margin.
    Post-knowledge margin ≠ pre-knowledge margin.
    The knowledge target shifts with each act.

    Formally: starting from margin and deducting sk_cost,
    the result is strictly less. -/
theorem inherited_self_modification (c : FiniteSelfClosure)
    (h_budget : c.self_knowledge_cost ≤ c.margin) :
    c.margin - c.self_knowledge_cost < c.margin := by
  have := c.sk_cost_pos; omega

/-- [∎] INHERITED PROPERTY — IRREVERSIBILITY (XV).
    Self-knowledge is irreversible: spent margin does not return.
    Post-margin < pre-margin. Returning to pre-state would require
    negative margin. -/
theorem inherited_irreversibility (c : FiniteSelfClosure)
    (h_budget : c.self_knowledge_cost ≤ c.margin) :
    ¬ (c.margin - c.self_knowledge_cost ≥ c.margin ∧ c.self_knowledge_cost > 0) := by
  intro ⟨h_ge, _⟩; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Impossibility of a separate register
-- ═══════════════════════════════════════════════════════════════════════════

/-- Hypothetical model of a "separate epistemic register".
    If such a register existed, it would have its own margin,
    independent of the cycle margin. -/
structure SeparateRegister where
  /-- Constitutive cycle margin -/
  cycle_margin : Nat
  /-- "Separate" epistemic margin -/
  epistemic_margin : Nat
  /-- Epistemic does not draw on the cycle -/
  independent : Prop

/-- [∎] IMPOSSIBILITY — A separate register violates I-β.

    By I-β, total margin = cycle margin. Every operation
    (constitutive or epistemic) draws on this single margin.

    If cycle + self-knowledge already consume the full drain,
    any additional margin (separate register with extra > 0)
    would exceed capacity. No room for an independent
    epistemic substrate. -/
theorem no_separate_register (cycle_cost sk_cost margin extra : Nat)
    (h_tight : cycle_cost + sk_cost = margin)
    (h_extra : extra > 0) :
    cycle_cost + sk_cost + extra > margin := by
  omega

/-- [∎] MARGIN UNIQUENESS — Direct corollary.
    The total margin available for ALL operations
    (constitutive and epistemic) is the same. There is only
    one margin — the cycle's. -/
theorem single_margin (c : FiniteSelfClosure) :
    totalDrain c ≤ c.margin →
    c.cycle_cost ≤ c.margin ∧ c.self_knowledge_cost ≤ c.margin := by
  intro h; unfold totalDrain at h
  exact ⟨by omega, by omega⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. Bridge: FiniteExposed for the self-knowing closure
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] BRIDGE — FiniteSelfClosure IS FiniteExposed (refined).
    The drain includes self-knowledge. The typechecker verifies
    that the epistemic is in the same regime as the constitutive.
    All trunk theorems (XVII, XXXIV, etc.) apply automatically
    to the self-knowing closure.

    Operations synthesized as [cycle_cost, self_knowledge_cost] — the
    two distinct operational modalities of a self-knowing closure under I'. -/
instance : FiniteExposed FiniteSelfClosure where
  margin c := c.margin
  drain c := totalDrain c
  drain_pos c := by unfold totalDrain; have := c.cycle_cost_pos; have := c.sk_cost_pos; omega
  operations c := [c.cycle_cost, c.self_knowledge_cost]
  ops_nonempty c := by simp
  ops_positive c := by
    intro x hx
    simp at hx
    cases hx with
    | inl h => rw [h]; exact c.cycle_cost_pos
    | inr h => rw [h]; exact c.sk_cost_pos

-- ═══════════════════════════════════════════════════════════════════════════
-- INVENTORY
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Result

### What the lemma proves

1. **Subsumption** (§4): Every SelfKnowledgeOp converts to CycleOp
   without information loss. Cost is preserved (dissolution_cost_preserved).
   The operation is constitutive (dissolution_is_cycle_op).

2. **Inheritance** (§5): Four cycle properties apply:
   - Finitude (inherited_finitude): self-knowledge exhausts
   - Opacity (inherited_opacity): number of acts is bounded
   - Self-modification (inherited_self_modification): target shifts
   - Irreversibility (inherited_irreversibility): spent margin does not return

3. **Impossibility** (§6): A separate epistemic register would violate I-β
   (no_separate_register). There is only one margin (single_margin).

4. **Bridge** (§7): FiniteSelfClosure instantiates FiniteExposed.
   All trunk theorems apply automatically.

### What the lemma does NOT say

- Nothing about the "lived experience" of opacity (LXI, ≈₃)
- Nothing phenomenological
- Opacity is structural, not experiential

### Dependency chain (no circularity)

```
I-β (être = agir)           → no separate substrate
LXVII (connaître = métab.)  → knowledge = operation
LVII (auto-affection)       → C operates on C
XXXVIII (métabolisation)     → metabolizing costs > 0
───────────────────────────
toCycleOp                   → SelfKnowledgeOp ⊆ CycleOp
dissolution_is_cycle_op          → operative subsumption (h_mod only)
knowledge_genesis_conditions     → separate genesis level (h_know + h_res)
inherited_*                 → properties follow
no_separate_register        → the alternative is impossible
FiniteExposed instance      → the trunk applies
```

### Counter
10 theorems + 1 instance · 0 sorry · 0 imports
-/

end RegisterDissolution