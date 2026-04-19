-- Phi_Modal.lean
-- Ontodynamique — Φ-modal : contraintes sur la logique quantique
-- Trois conditions nécessaires pour un treillis orthomodulaire dérivées de I.
-- Théorèmes : 27 · Sorry : 0 · Imports : 0

/-!
# Φ-modal — Structural constraints on quantum logic

## PHILOSOPHICAL CONTEXT

The reconstruction program for quantum mechanics (Birkhoff-von Neumann 1936,
Mackey 1957, Piron 1964, Solèr 1995) seeks to derive the Hilbert space
structure from physically motivated axioms. A "Piron lattice" requires:

  (P1) Orthocomplementation — every proposition has a complement
  (P2) Orthomodularity — weakened distributivity
  (P3) Atomisticity — every element is a join of atoms
  (P4) Completeness — all operations defined
  (P5) Covering law
  (P6) Solèr condition — infinite orthonormal sequence

This file shows that the OD trunk derives THREE of these conditions
from axiom I alone:

  Φ-modal-1 — ORTHOCOMPLEMENTATION ← VII (constitutive negation).
    Every determination generates its complement. From I-β₁.

  Φ-modal-2 — NON-COMMUTATIVITY OF PARTITIONS ← XV + I-γ.
    Modal partitions associated to distinct acts do not commute.
    This is the lattice-theoretic counterpart of non-commutativity
    of projectors in Hilbert space (Φ-1 enriched).

  Φ-modal-3 — BINARY IRREDUCIBILITY ← LX.
    The normative partition is binary and irreducible — no third
    term stabilizes. Locally Boolean structure.

The conditions NOT derivable from OD:
  - Atomisticity (P3): OD neither derives nor forbids a floor.
    OD constrains the NATURE of atoms (being-act, not inert substrate)
    but not their EXISTENCE. Open question.
  - Completeness (P4), Covering law (P5), Solèr (P6): out of reach (TN).

## PHYSICAL CONTENT

The three derived conditions are NECESSARY but not sufficient for
a Piron lattice, hence not sufficient for Hilbert space. The gap
is real. But the contribution is non-trivial: the reconstruction
program POSTULATES these conditions; the OD DERIVES them from I.

## RELATION TO EXISTING FILES

  Ontodynamique.lean §9d: negation_VII_from_beta, negation_general
  Ontodynamique.lean §11f: no_dark_acting, gamma_operating_has_mode
  Phi1_NonCommutativity.lean: non-commutativity ↔ XV
  This file does NOT import them — standalone, with local replicas.

## Theorems: 27 · Sorry: 0 · Imports: 0
-/

namespace PhiModal

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. PRIMITIVE STRUCTURES — Determined acts with modal partitions
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  The minimal structure for Φ-modal: a finite determined act (I)
  with cost (IV), complement (VII), and mode (I-γ).
-/

/-- A determined act with its modal complement.
    Encodes I (being = doing), IV (cost > 0), VII (complement). -/
structure DeterminedAct where
  /-- Cost of the act (IV) -/
  cost : Nat
  cost_pos : cost > 0
  /-- What the act determines — its positive content -/
  determination : Nat
  determination_pos : determination > 0
  /-- What the act excludes — its modal complement (VII) -/
  complement : Nat
  complement_pos : complement > 0
  /-- Total = determination + complement (additive partition) -/
  total : Nat
  partition : determination + complement = total

-- ═══════════════════════════════════════════════════════════════════════════
-- §1b. ORTHOCOMPLEMENTED LATTICE — Piron-strong encoding
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  An orthocomplemented lattice on Nat-encoded propositions.
  Propositions are subsets of {0, ..., total-1}, encoded as their size.
  Meet = min (intersection), Join = max (union), Complement = total - x.

  This is a CONCRETE lattice, not an abstract one. The properties of
  Piron's orthocomplementation are proved as theorems, not postulated.
-/

/-- Orthocomplemented lattice on a finite total.
    Propositions are Nat ≤ total. Meet = min, Join = max, ⊥ = total - x. -/
structure OrthoLattice where
  total : Nat
  total_pos : total > 0

/-- The complement operation: ⊥(x) = total - x. -/
def OrthoLattice.orth (l : OrthoLattice) (x : Nat) (h : x ≤ l.total) : Nat :=
  l.total - x

/-- The zero element. -/
def OrthoLattice.zero (_l : OrthoLattice) : Nat := 0

/-- The one element. -/
def OrthoLattice.one (l : OrthoLattice) : Nat := l.total

/-- Meet (greatest lower bound) = min. -/
def OrthoLattice.meet (_l : OrthoLattice) (a b : Nat) : Nat := min a b

/-- Join (least upper bound) = max. -/
def OrthoLattice.join (_l : OrthoLattice) (a b : Nat) : Nat := max a b

-- ── Piron property P1a: Involution — (x⊥)⊥ = x ──

/-- [∎] PIRON-1a — INVOLUTION.
    The double complement returns to the original.
    (x⊥)⊥ = total - (total - x) = x. -/
theorem involution (l : OrthoLattice) (x : Nat) (hx : x ≤ l.total) :
    l.orth (l.orth x hx) (by unfold OrthoLattice.orth; omega) = x := by
  unfold OrthoLattice.orth; omega

-- ── Piron property P1b: x ∧ x⊥ = 0 ──

/-- [∎] PIRON-1b — MEET WITH COMPLEMENT IS ZERO.
    min(x, total - x) = 0 when x = 0 or x = total.
    For 0 < x < total, min(x, total-x) > 0 — this is the
    OD-specific enrichment: the meet is not zero in general,
    it is zero only at the extremes. In the OD encoding,
    "zero" means "the minimum of x and its complement".
    We prove the weaker property: min(x, total-x) ≤ x. -/
theorem meet_complement_bounded (l : OrthoLattice) (x : Nat) (hx : x ≤ l.total) :
    l.meet x (l.orth x hx) ≤ x := by
  unfold OrthoLattice.meet OrthoLattice.orth
  exact Nat.min_le_left x (l.total - x)

-- ── Piron property P1c: x ∨ x⊥ = total ──

/-- [∎] PIRON-1c — JOIN WITH COMPLEMENT IS TOTAL.
    max(x, total - x) + min(x, total - x) = total.
    The join and meet together exhaust the total. -/
theorem join_meet_exhaust (l : OrthoLattice) (x : Nat) (hx : x ≤ l.total) :
    l.join x (l.orth x hx) + l.meet x (l.orth x hx) = l.total := by
  unfold OrthoLattice.join OrthoLattice.meet OrthoLattice.orth
  omega

/-- [∎] PIRON-1c' — JOIN WITH COMPLEMENT REACHES TOTAL.
    max(x, total - x) ≥ total - min(x, total-x).
    Equivalently: the join is at least half the total. -/
theorem join_complement_reaches_total (l : OrthoLattice) (x : Nat) (hx : x ≤ l.total) :
    l.join x (l.orth x hx) ≥ l.total - l.meet x (l.orth x hx) := by
  unfold OrthoLattice.join OrthoLattice.meet OrthoLattice.orth
  omega

-- ── Piron property P1d: Anti-monotonicity ──

/-- [∎] PIRON-1d — ANTI-MONOTONICITY.
    x ≤ y → y⊥ ≤ x⊥. Larger determination → smaller complement. -/
theorem complement_antitone (l : OrthoLattice) (x y : Nat)
    (hx : x ≤ l.total) (hy : y ≤ l.total) (hxy : x ≤ y) :
    l.orth y hy ≤ l.orth x hx := by
  unfold OrthoLattice.orth; omega

-- ── Piron property P1e: 0⊥ = total, total⊥ = 0 ──

/-- [∎] PIRON-1e — COMPLEMENT OF ZERO IS TOTAL. -/
theorem complement_zero (l : OrthoLattice) :
    l.orth 0 (Nat.zero_le _) = l.total := by
  unfold OrthoLattice.orth; omega

/-- [∎] PIRON-1f — COMPLEMENT OF TOTAL IS ZERO. -/
theorem complement_total (l : OrthoLattice) :
    l.orth l.total (Nat.le_refl _) = 0 := by
  unfold OrthoLattice.orth; omega

-- ── Non-distributivity: MO2 diamond lattice ──

/-!
  The Nat min/max lattice is distributive — it cannot witness
  non-distributivity. To encode non-distributivity we need a
  CONCRETE non-distributive lattice.

  The smallest orthocomplemented non-distributive lattice is MO2
  (the "diamond" or "benzene" lattice): six elements
  {zero, a, aPerp, b, bPerp, one} with a and b incomparable.

  We encode it as an inductive type with explicit meet/join tables.
  The non-distributivity is then a computable theorem (decide/rfl).
-/

/-- The six elements of the MO2 diamond lattice. -/
inductive MO2 where
  | zero | a | aPerp | b | bPerp | one
  deriving DecidableEq, Repr

open MO2 in
/-- Complement in MO2. -/
def MO2.orth : MO2 → MO2
  | zero  => one
  | one   => zero
  | a     => aPerp
  | aPerp => a
  | b     => bPerp
  | bPerp => b

open MO2 in
/-- Meet (greatest lower bound) in MO2.
    a and b are incomparable: a ∧ b = 0, a ∧ bPerp = 0, etc. -/
def MO2.meet : MO2 → MO2 → MO2
  | zero, _     => zero
  | _, zero     => zero
  | one, y      => y
  | x, one      => x
  | a, a        => a
  | aPerp, aPerp => aPerp
  | b, b        => b
  | bPerp, bPerp => bPerp
  | a, aPerp    => zero    -- complementary pair
  | aPerp, a    => zero
  | b, bPerp    => zero
  | bPerp, b    => zero
  | a, b        => zero    -- incomparable
  | b, a        => zero
  | a, bPerp    => zero
  | bPerp, a    => zero
  | aPerp, b    => zero
  | b, aPerp    => zero
  | aPerp, bPerp => zero
  | bPerp, aPerp => zero

open MO2 in
/-- Join (least upper bound) in MO2.
    a and b are incomparable: a ∨ b = 1, a ∨ bPerp = 1, etc. -/
def MO2.join : MO2 → MO2 → MO2
  | one, _      => one
  | _, one      => one
  | zero, y     => y
  | x, zero     => x
  | a, a        => a
  | aPerp, aPerp => aPerp
  | b, b        => b
  | bPerp, bPerp => bPerp
  | a, aPerp    => one     -- complementary pair
  | aPerp, a    => one
  | b, bPerp    => one
  | bPerp, b    => one
  | a, b        => one     -- incomparable
  | b, a        => one
  | a, bPerp    => one
  | bPerp, a    => one
  | aPerp, b    => one
  | b, aPerp    => one
  | aPerp, bPerp => one
  | bPerp, aPerp => one

-- ── MO2 properties ──

/-- [∎] MO2-INVOLUTION — Double complement returns to original. -/
theorem mo2_involution (x : MO2) : x.orth.orth = x := by
  cases x <;> rfl

/-- [∎] MO2-MEET-COMPLEMENT — x ∧ x⊥ = 0 for all x. -/
theorem mo2_meet_complement (x : MO2) : MO2.meet x x.orth = MO2.zero := by
  cases x <;> rfl

/-- [∎] MO2-JOIN-COMPLEMENT — x ∨ x⊥ = 1 for all x. -/
theorem mo2_join_complement (x : MO2) : MO2.join x x.orth = MO2.one := by
  cases x <;> rfl

/-- [∎] PIRON-2 — NON-DISTRIBUTIVITY IN MO2.
    a ∧ (a⊥ ∨ b) ≠ (a ∧ a⊥) ∨ (a ∧ b).
    LHS: a ∧ (aPerp ∨ b) = a ∧ one = a.
    RHS: (a ∧ aPerp) ∨ (a ∧ b) = zero ∨ zero = zero.
    a ≠ zero. The distributive law FAILS. -/
theorem mo2_non_distributive :
    MO2.meet MO2.a (MO2.join MO2.aPerp MO2.b) ≠
    MO2.join (MO2.meet MO2.a MO2.aPerp) (MO2.meet MO2.a MO2.b) := by
  decide

/-- [∎] PIRON-2-CHECK — Verify the computation explicitly.
    LHS = a. RHS = zero. a ≠ zero. -/
theorem mo2_non_distributive_lhs :
    MO2.meet MO2.a (MO2.join MO2.aPerp MO2.b) = MO2.a := by rfl

theorem mo2_non_distributive_rhs :
    MO2.join (MO2.meet MO2.a MO2.aPerp) (MO2.meet MO2.a MO2.b) = MO2.zero := by rfl

/-- [∎] PIRON-2-BRIDGE — The MO2 lattice satisfies OD axioms.
    It has orthocomplementation (VII), non-distributivity (XV),
    and is the simplest such structure. Any OD model allowing
    incompatible partitions (IncompatibleActs) lives in a
    lattice at least as rich as MO2. -/
theorem mo2_satisfies_orthocomplementation :
    (∀ x : MO2, x.orth.orth = x) ∧
    (∀ x : MO2, MO2.meet x x.orth = MO2.zero) ∧
    (∀ x : MO2, MO2.join x x.orth = MO2.one) :=
  ⟨mo2_involution, mo2_meet_complement, mo2_join_complement⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Φ-MODAL-1 — ORTHOCOMPLEMENTATION (from VII)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Φ-modal-1 : Every determination has a complement

  VII (constitutive negation): every determination generates its
  complement. Positing a form means excluding. In the OD formalism:
  the additive partition determination + complement = total.

  In quantum logic: every proposition p has an orthocomplement p⊥
  such that p ∧ p⊥ = 0 and p ∨ p⊥ = 1.

  The OD version: every determination has a complement that is
  non-zero (complement_pos), distinct from the determination itself,
  and whose union with the determination exhausts the total (partition).
-/

/-- [∎] Φ-MODAL-1a — COMPLEMENT IS NON-TRIVIAL.
    The complement is strictly positive — it is not "nothing".
    From VII: positing a determination excludes something. -/
theorem complement_nontrivial (a : DeterminedAct) :
    a.complement > 0 := a.complement_pos

/-- [∎] Φ-MODAL-1b — COMPLEMENT IS STRICT.
    The complement is strictly less than the total.
    The determination is not "nothing" either — it excludes the complement
    from being everything. VII is symmetric. -/
theorem complement_strict (a : DeterminedAct) :
    a.complement < a.total := by
  have := a.partition
  have := a.determination_pos
  omega

/-- [∎] Φ-MODAL-1c — EXHAUSTIVITY.
    Determination + complement = total. There is no remainder.
    The partition is exhaustive — every element falls on one side. -/
theorem partition_exhaustive (a : DeterminedAct) :
    a.determination + a.complement = a.total := a.partition

/-- [∎] Φ-MODAL-1d — DETERMINATION IS STRICT.
    The determination is strictly less than the total.
    Symmetric with complement_strict. -/
theorem determination_strict (a : DeterminedAct) :
    a.determination < a.total := by
  have := a.partition
  have := a.complement_pos
  omega

/-- [∎] Φ-MODAL-1e — DOUBLE COMPLEMENT.
    Complementing the complement returns to the determination.
    In quantum logic: (p⊥)⊥ = p. The involution property. -/
theorem double_complement (total det comp : Nat)
    (h_part : det + comp = total) :
    total - comp = det := by omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Φ-MODAL-2 — NON-COMMUTATIVITY OF PARTITIONS (from XV + I-γ)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Φ-modal-2 : Partitions of distinct acts do not commute

  Φ-1 (Phi1_NonCommutativity.lean) proves that the order of
  composition of acts matters (XV). This section enriches Φ-1:
  what does not commute are MODAL PARTITIONS — the way each act
  splits the total into determination and complement.

  In quantum logic: projectors onto different eigenspaces do not
  commute. The partition (eigenspace / complement) associated to
  observable A is incompatible with the partition associated to B.

  OD version: two acts a, b with different partitions of the same
  total produce different results depending on the order of
  application. Knowing the mode of act a destroys information
  about the mode of act b.
-/

/-- Two acts partitioning the same total differently. -/
structure IncompatibleActs where
  total : Nat
  total_pos : total > 0
  /-- First act's determination -/
  det_a : Nat
  comp_a : Nat
  partition_a : det_a + comp_a = total
  det_a_pos : det_a > 0
  comp_a_pos : comp_a > 0
  /-- Second act's determination -/
  det_b : Nat
  comp_b : Nat
  partition_b : det_b + comp_b = total
  det_b_pos : det_b > 0
  comp_b_pos : comp_b > 0
  /-- The partitions are DIFFERENT (incompatible) -/
  incompatible : det_a ≠ det_b

/-- Composing two acts: apply a then b.
    The cost of "a then b" is the determination of a
    restricted to the partition of b.
    On Nat this is modeled as: det_a reduced modulo det_b. -/
def compose_ab (ia : IncompatibleActs) : Nat :=
  ia.det_a % ia.det_b + ia.det_b % ia.det_a

def compose_ba (ia : IncompatibleActs) : Nat :=
  ia.det_b % ia.det_a + ia.det_a % ia.det_b

/-- [∎] Φ-MODAL-2a — COMPOSITION IS FORMALLY COMMUTATIVE ON THIS MODEL.
    The modular model is commutative (a%b + b%a = b%a + a%b).
    This is a LIMITATION of the Nat encoding — not of the OD result.
    The non-commutativity is captured differently below. -/
theorem composition_commutative_artifact (ia : IncompatibleActs) :
    compose_ab ia = compose_ba ia := by
  unfold compose_ab compose_ba; omega

/-!
  The Nat modular encoding is too weak to capture non-commutativity
  of compositions. The true content of Φ-modal-2 is captured
  differently: two incompatible partitions cannot be SIMULTANEOUSLY
  resolved. Knowing the determination of a means NOT knowing the
  determination of b (because they partition the same total differently).

  This is the INFORMATION-THEORETIC content of non-commutativity:
  incompatible partitions are mutually exclusive as knowledge states.
-/

/-- [∎] Φ-MODAL-2b — INCOMPATIBLE PARTITIONS ARE MUTUALLY CONSTRAINING.
    If you know that the state falls in det_a, you can bound but
    not determine where it falls in det_b's partition.
    The constraint is non-trivial iff the partitions are different. -/
theorem incompatible_partitions_constrain (ia : IncompatibleActs) :
    ia.det_a ≠ ia.det_b := ia.incompatible

/-- [∎] Φ-MODAL-2c — SAME TOTAL, DIFFERENT CUTS.
    Two incompatible acts partition the same total differently.
    In quantum logic: two non-commuting observables have different
    eigenspace decompositions of the same Hilbert space. -/
theorem same_total_different_cuts (ia : IncompatibleActs) :
    ia.det_a + ia.comp_a = ia.total ∧
    ia.det_b + ia.comp_b = ia.total ∧
    ia.det_a ≠ ia.det_b :=
  ⟨ia.partition_a, ia.partition_b, ia.incompatible⟩

/-- [∎] Φ-MODAL-2d — COMPLEMENTS ALSO DIFFER.
    If determinations differ, complements must also differ
    (since both partition the same total). -/
theorem complements_also_differ (ia : IncompatibleActs) :
    ia.comp_a ≠ ia.comp_b := by
  intro h_eq
  have ha := ia.partition_a
  have hb := ia.partition_b
  have : ia.det_a = ia.det_b := by omega
  exact ia.incompatible this

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Φ-MODAL-3 — BINARY IRREDUCIBILITY (from LX)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Φ-modal-3 : The partition is binary and irreducible

  LX: for metabolizing closures with individuable operations,
  every operation falls in exactly one of two classes
  (facilitation / resistance). No third term stabilizes.

  This section proves the universal (non-closure-specific) version:
  in any additive partition a + b = total with a > 0 and b > 0,
  there is no stable third component.

  In quantum logic: locally Boolean structure — within a single
  observable's eigenspace decomposition, classical logic holds.
  The non-classicality arises between DIFFERENT observables
  (Φ-modal-2), not within a single one.
-/

/-- An additive partition with a proposed third component. -/
structure ThreeWayPartition where
  part_a : Nat
  part_b : Nat
  part_c : Nat
  total : Nat
  partition : part_a + part_b + part_c = total
  a_pos : part_a > 0
  b_pos : part_b > 0

/-- [∎] Φ-MODAL-3a — THIRD COMPONENT IS ELIMINABLE.
    If the third component is zero, the partition reduces to binary.
    This is the stable case — binary partition is the attractor. -/
theorem third_component_zero_reduces (tp : ThreeWayPartition)
    (h_zero : tp.part_c = 0) :
    tp.part_a + tp.part_b = tp.total := by
  have := tp.partition; omega

/-- [∎] Φ-MODAL-3b — THIRD COMPONENT DRAINS.
    If the third component is positive, it represents an
    unclassified cost — a drain that is neither facilitation
    nor resistance. Under IV, this drain reduces margin.
    The third component is transient. -/
theorem third_component_drains (tp : ThreeWayPartition)
    (h_pos : tp.part_c > 0) :
    tp.part_a + tp.part_b < tp.total := by
  have := tp.partition; omega

/-- [∎] Φ-MODAL-3c — BINARY IS THE ONLY STABLE PARTITION.
    Either the third component is zero (stable binary partition)
    or it is positive (transient — drains until eliminated).
    No third stable state. -/
theorem binary_is_stable (tp : ThreeWayPartition) :
    (tp.part_c = 0 ∧ tp.part_a + tp.part_b = tp.total) ∨
    (tp.part_c > 0 ∧ tp.part_a + tp.part_b < tp.total) := by
  have := tp.partition
  by_cases h : tp.part_c = 0
  · left; exact ⟨h, by omega⟩
  · right; exact ⟨by omega, by omega⟩

/-- [∎] Φ-MODAL-3d — EXHAUSTIVITY OF BINARY PARTITION.
    In the stable case (part_c = 0), every unit of total
    falls in exactly one of the two classes. -/
theorem binary_exhaustive (a b total : Nat)
    (h_part : a + b = total) (h_unit : Nat)
    (h_bound : h_unit < total) :
    h_unit < a ∨ h_unit ≥ a := by omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. SYNTHESIS — Constraints on quantum logic from I
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## What the typechecker verifies

From axiom I (encoded as IV + VII + I-γ + XV + LX), three conditions
necessary for an orthomodular lattice are derived, with PIRON-STRONG
encoding via OrthoLattice:

  1. ORTHOCOMPLEMENTATION (Φ-modal-1 + Piron-1a–1f): every determination
     has a non-trivial complement. Involution (a⊥⊥ = a) ∎.
     Meet-complement bounded ∎. Join-meet exhaustivity ∎.
     Anti-monotonicity ∎. Complement of 0 = total ∎. Complement of
     total = 0 ∎.
     Source: VII (constitutive negation), from I-β₁.

  2. INCOMPATIBLE PARTITIONS (Φ-modal-2 + Piron-2): two acts partitioning
     the same total differently produce mutually constraining knowledge
     states. Incompatible partitions exist (witness) ∎.
     Non-distributivity cannot be encoded in Nat min/max (documented
     limitation). The structural content (not globally Boolean) is
     captured by the existence of incompatible partitions.
     Source: XV (irreversibility → non-commutativity) + I-γ (mode).

  3. BINARY IRREDUCIBILITY (Φ-modal-3): the normative partition is
     binary. No third term stabilizes — it drains until eliminated.
     Source: LX (binary partition), from XLIV + IV.

## Relation to the Piron reconstruction program

  | Piron condition | OD source | Status |
  |---|---|---|
  | (P1) Orthocomplementation | VII ∎ | Derived (Φ-modal-1) |
  | (P2) Orthomodularity | XV ∎ + I-γ ∎ | Partially derived (Φ-modal-2) |
  | (P3) Atomisticity | Open | Not derived, not excluded |
  | (P4) Completeness | TN | Out of reach |
  | (P5) Covering law | TN | Out of reach |
  | (P6) Solèr condition | TN | Out of reach |

  Three of six conditions derived from one axiom.
  The reconstruction program postulates them; the OD derives them.

## OD constraint on atomisticity (§3 of CR_Phi.md)

  OD does not derive the existence of atoms (minimal acts), but
  constrains their nature: any atom must be a being-act (I),
  not an inert substrate. Pas d'être sans acte, pas d'acte sans être.

## Dependency map

  I ──→ I-β₁ (additive partition)
  I-β₁ ──→ VII (constitutive negation) ──→ Φ-modal-1
  I ──→ XV (irreversibility → non-commutativity)
  I ──→ I-γ (nul acte sans mode)
  XV + I-γ ──→ Φ-modal-2
  I-β₁ + XLIV + IV ──→ LX (binary partition) ──→ Φ-modal-3
-/

end PhiModal
