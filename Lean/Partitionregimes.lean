/-!
# Three partitions, one question: how many axes are independent?
# (0 imports, checkable with `lean PartitionRegimes.lean`)

Three properties of a finite entity, each read off a SEPARATE structural field so
that no definition presupposes another:

  B  — a regenerating loop: a cycle reproduces the conditions it depends on.
  C  — Rosen closure to efficient causation: it produces its own catalysts.
  R  — (weak) endorsement: the cost of a perturbation falls on an internal reserve.

The article offers three candidate structures for the regimes of unity:

  (3) trichotomy      — a decision TREE: ask B first (no loop -> aggregate), then,
                        within B, ask endorsement (self vs carriage). Three outcomes.
  (4) quadripartition — a GRID crossing two axes (here C x R). Four cells.
  (8) three axes      — a CUBE: B, C, R all independent. Up to eight cells.

This file settles which is fundamental and what the others are.

RESULTS.
  * The three axes are pairwise independent and all eight cells are inhabited
    (`cube_inhabited`): the CUBE is coherent and is the general structure.
  * The trichotomy is the cube's projection that asks B first and folds every
    non-looping entity into "aggregate". It yields exactly three outcomes
    (`tri_exhaustive`, `tri_exclusive`). It is FAITHFUL iff endorsement entails a
    loop. Under the STRONG reading of endorsement (pay FOR the regeneration,
    `Rstrong := B and R`), that entailment holds and the fourth "endorses-only"
    cell is empty (`endorses_only_empty_strong`) — trichotomy, nothing lost.
    Under the WEAK reading (pay from a reserve, no regeneration required) the
    "endorses-only" cell is INHABITED (`endorses_only_real_weak`, a spinning top),
    and the tree then CONFLATES an endorsing thing with an inert one
    (`tree_conflates_weak`).
  * The quadripartition is the cube's projection onto (C, R), ignoring B
    (`quad_CR_inhabited`). Four cells; it is the frame used against Rosen.

MORAL. None of the three is "true" in the absolute. The cube is fundamental; 3 and
4 are projections selected by (a) which axes you cross and (b) where you place the
joint in the definition of "endorse". The article's trichotomy is legitimate
PROVIDED the strong, regeneration-entailing reading of endorsement is made explicit
— which this file shows is exactly the condition that empties the fourth cell.

As always: Lean certifies the logical (in)dependences and the coherence of each
structure; the FIDELITY of B, C, R to their intended notions is argued in prose.
-/

namespace Partition

structure Entity where
  requires : List Nat          -- catalysts required as efficient causes
  produces : List Nat          -- catalysts the cycle itself makes
  loop_regenerates : Bool      -- a cycle reproduces the conditions it depends on
  reserve : Nat                -- internal store
  perturb_cost : Nat           -- cost a perturbation imposes

-- Three axes, each reading its OWN fields only. None mentions another.
@[reducible] def C (e : Entity) : Prop :=            -- Rosen closure (catalyst graph)
  e.requires.all (fun c => e.produces.contains c) = true
@[reducible] def B (e : Entity) : Prop :=            -- regenerating loop
  e.loop_regenerates = true
@[reducible] def R (e : Entity) : Prop :=            -- weak endorsement: pays from reserve
  e.reserve ≥ e.perturb_cost ∧ e.reserve > 0

-- Strong endorsement: paying FOR the regeneration presupposes the regeneration.
-- This is the ONE place a dependency is introduced, and it is the definitional
-- content of the strong reading, not a trick.
@[reducible] def Rstrong (e : Entity) : Prop := B e ∧ R e

-- A generator: set the three axes freely by three booleans.
@[reducible] def ent (b c r : Bool) : Entity :=
  { requires := [0],
    produces := (if c then [0] else ([] : List Nat)),
    loop_regenerates := b,
    reserve := (if r then 10 else 0),
    perturb_cost := 3 }

@[reducible] def e000 := ent false false false   -- ¬B ¬C ¬R : inert (stone-like)
@[reducible] def e001 := ent false false true    -- ¬B ¬C  R : spinning top (endorses only)
@[reducible] def e010 := ent false true  false   -- ¬B  C ¬R
@[reducible] def e011 := ent false true  true    -- ¬B  C  R
@[reducible] def e100 := ent true  false false    --  B ¬C ¬R : whirlpool (loop, not closed)
@[reducible] def e101 := ent true  false true     --  B ¬C  R
@[reducible] def e110 := ent true  true  false    --  B  C ¬R : autocatalytic set in flow
@[reducible] def e111 := ent true  true  true     --  B  C  R : organism (the self)

-- ═══════════════════════════════════════════════════════════════════════════
-- Pairwise independence of the three axes (both directions)
-- ═══════════════════════════════════════════════════════════════════════════

/-- [■] Weak endorsement does not require a loop: R holds, B fails. (spinning top) -/
theorem R_without_B : R e001 ∧ ¬ B e001 := by decide
/-- [■] A loop need not endorse. (whirlpool) -/
theorem B_without_R : B e100 ∧ ¬ R e100 := by decide
/-- [■] Rosen-closed yet not endorsing. (autocatalytic set in a flow reactor) -/
theorem C_without_R : C e110 ∧ ¬ R e110 := by decide
/-- [■] Endorsing yet not Rosen-closed. -/
theorem R_without_C : R e101 ∧ ¬ C e101 := by decide
/-- [■] A loop need not be Rosen-closed. (whirlpool: topological loop, no catalyst production) -/
theorem B_without_C : B e100 ∧ ¬ C e100 := by decide
/-- [■] Rosen-closed without a regenerating loop. -/
theorem C_without_B : C e010 ∧ ¬ B e010 := by decide

-- ═══════════════════════════════════════════════════════════════════════════
-- The cube: all eight combinations are inhabited
-- ═══════════════════════════════════════════════════════════════════════════

/-- [■] THE CUBE. Every combination of (B, C, R) is realized: the three axes are
    fully independent, so the eight-cell cube is the general, coherent structure. -/
theorem cube_inhabited :
    (¬ B e000 ∧ ¬ C e000 ∧ ¬ R e000) ∧
    (¬ B e001 ∧ ¬ C e001 ∧   R e001) ∧
    (¬ B e010 ∧   C e010 ∧ ¬ R e010) ∧
    (¬ B e011 ∧   C e011 ∧   R e011) ∧
    (  B e100 ∧ ¬ C e100 ∧ ¬ R e100) ∧
    (  B e101 ∧ ¬ C e101 ∧   R e101) ∧
    (  B e110 ∧   C e110 ∧ ¬ R e110) ∧
    (  B e111 ∧   C e111 ∧   R e111) := by decide

-- ═══════════════════════════════════════════════════════════════════════════
-- The trichotomy: a tree on (B then R). Three outcomes.
-- ═══════════════════════════════════════════════════════════════════════════

@[reducible] def aggregate  (e : Entity) : Prop := ¬ B e
@[reducible] def selfRegime (e : Entity) : Prop := B e ∧ R e
@[reducible] def carriage   (e : Entity) : Prop := B e ∧ ¬ R e

/-- [■] The tree yields exactly three exhaustive outcomes. -/
theorem tri_exhaustive (e : Entity) :
    aggregate e ∨ selfRegime e ∨ carriage e := by
  unfold aggregate selfRegime carriage
  by_cases hB : B e
  · by_cases hR : R e
    · exact Or.inr (Or.inl ⟨hB, hR⟩)
    · exact Or.inr (Or.inr ⟨hB, hR⟩)
  · exact Or.inl hB

/-- [■] The three outcomes are pairwise exclusive. -/
theorem tri_exclusive (e : Entity) :
    ¬ (aggregate e ∧ selfRegime e) ∧
    ¬ (aggregate e ∧ carriage e) ∧
    ¬ (selfRegime e ∧ carriage e) := by
  unfold aggregate selfRegime carriage
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hnB, hB, _⟩; exact hnB hB
  · rintro ⟨hnB, hB, _⟩; exact hnB hB
  · rintro ⟨⟨_, hR⟩, _, hnR⟩; exact hnR hR

-- ═══════════════════════════════════════════════════════════════════════════
-- When is the trichotomy faithful? The definition of endorsement decides.
-- ═══════════════════════════════════════════════════════════════════════════

/-- [■] Strong endorsement entails a loop — by definition of "pay FOR regeneration". -/
theorem Rstrong_imp_B (e : Entity) : Rstrong e → B e := fun h => h.1

/-- [■] Under STRONG endorsement the fourth cell is empty: nothing endorses without
    a loop. The trichotomy loses nothing — it is the faithful structure. -/
theorem endorses_only_empty_strong : ¬ ∃ e : Entity, Rstrong e ∧ ¬ B e := by
  rintro ⟨e, hRs, hnB⟩; exact hnB hRs.1

/-- [■] Under WEAK endorsement the fourth cell is inhabited: the spinning top
    endorses (pays from its own reserve) yet has no regenerating loop. -/
theorem endorses_only_real_weak : R e001 ∧ ¬ B e001 := by decide

/-- [■] ...and then the tree CONFLATES it with an inert thing: e001 (endorses) and
    e000 (inert) are both classed "aggregate" though they differ on endorsement.
    This is the information the trichotomy discards under the weak reading, and the
    cube keeps. -/
theorem tree_conflates_weak :
    aggregate e000 ∧ aggregate e001 ∧ (¬ R e000 ∧ R e001) := by decide

/-- [■] The self is the same set under both readings of endorsement
    (Rstrong = B ∧ R, and B holds), so the disagreement is only about how
    non-looping, reserve-bearing things are classed — never about the self. -/
theorem self_same_under_both (e : Entity) :
    selfRegime e ↔ (B e ∧ Rstrong e) := by
  unfold selfRegime Rstrong
  constructor
  · rintro ⟨hB, hR⟩; exact ⟨hB, hB, hR⟩
  · rintro ⟨hB, _, hR⟩; exact ⟨hB, hR⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- The quadripartition: projection onto (C, R), ignoring B. Four cells.
-- ═══════════════════════════════════════════════════════════════════════════

/-- [■] All four combinations of (C, R) are inhabited: the grid used against Rosen
    is coherent, and it is a DIFFERENT projection of the cube than the trichotomy
    (it crosses C×R, where the tree branches on B then R). -/
theorem quad_CR_inhabited :
    (¬ C e000 ∧ ¬ R e000) ∧ (¬ C e001 ∧   R e001) ∧
    (  C e010 ∧ ¬ R e010) ∧ (  C e011 ∧   R e011) := by decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Audit
-- ═══════════════════════════════════════════════════════════════════════════

#print axioms cube_inhabited
#print axioms tri_exhaustive
#print axioms tri_exclusive
#print axioms endorses_only_empty_strong
#print axioms endorses_only_real_weak
#print axioms tree_conflates_weak
#print axioms quad_CR_inhabited
#print axioms self_same_under_both

end Partition
