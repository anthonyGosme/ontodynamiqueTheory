/-!
# Rosen vs Endorsement — the decisive independence test
# (companion to gradient.lean; 0 imports, checkable with `lean RosenEndorsement.lean`)

The article claims, in §6.2, that the endorsement of cost SEPARATES what Rosen's
closure to efficient causation ranks TOGETHER — i.e. that cost does work *beyond*
closure. The prior `endorsement_separates` (gradient.lean, §16) cannot support this:
it has no catalyst graph at all. Its `FiniteEntity` carries only a cost split, and
"closure" is *defined as* that split, so the theorem separates two values of the one
field it owns. It is `decide`-trivial and says nothing about Rosen.

This file settles the question honestly by modeling the two axes as genuinely
separate structures. NEITHER definition mentions the other:

  • Axis 1  RosenClosed  — a property of the CATALYST graph only:
       every catalyst the cycle requires as an efficient cause is produced by
       the cycle itself. (Substrates / material causes are omitted on purpose:
       closure to efficient causation is about catalysts, which are produced,
       not about raw matter, which may always be imported.)

  • Axis 2  EndogenousEndorsement — a property of the ENERGETIC profile only:
       the irreversible cost of a perturbation is borne by an INTERNAL margin
       (a store), rather than falling on a live external flow.

The single decidable question is then:

      Can an entity be RosenClosed and yet NOT endorse endogenously?

  – If a witness exists, the axes are independent: closure does NOT entail
    endorsement, so no closure-only criterion can yield the endorsement verdict.
    The door to "surpassing Rosen" is OPEN.
  – If every such witness were contradictory, then `RosenClosed → Endorsement`
    would be provable, cost would be redundant on the closure axis, and the
    surpassing claim would have to be dropped.

RESULT (below): the witness exists and is named `selfCatalyzingFlow` — a system
that manufactures all its own catalysts yet carries no margin, so a perturbation's
cost falls on its feed. Rosen calls it a full (M,R) system; the endorsement
criterion calls it a carriage. That divergence is the surpassing, and it is
machine-checked.

WHAT LEAN SETTLES, AND WHAT IT DOES NOT.
Lean proves the two axes are LOGICALLY independent: there is no conceptual
entailment either way (all four combinations are inhabited without contradiction).
This is enough to refute "closure entails endorsement" as a conceptual truth, and
hence to establish that closure is not SUFFICIENT for the endorsement verdict — [■].
Lean does NOT prove that closed-but-unbuffered systems are physically instantiated;
that is empirical — [♢]. The definitions' FIDELITY to Rosen and to the intended
notion of endorsement is, as always, argued in prose, not by the checker.
-/

namespace RosenEndorsement

-- ═══════════════════════════════════════════════════════════════════════════
-- Axis 1 — Rosen closure to efficient causation (catalyst graph ONLY)
-- ═══════════════════════════════════════════════════════════════════════════

/-- A minimal metabolic network over an index of catalysts.
    `requires` : indices of catalysts the cycle needs as efficient causes.
    `produces` : indices of catalysts the cycle itself makes.
    This is a minimal rendering of closure to efficient causation. Richer (M,R)
    structure (replacement maps, etc.) only ADDS constraints; adding constraints
    can never manufacture an independence witness, so the direction that matters
    here (closed ∧ ¬endorse) is robust as long as closure stays silent about
    energy storage — which it does. -/
structure Network where
  requires : List Nat
  produces : List Nat

/-- Closure to efficient causation: every required catalyst is internally produced.
    Depends on the catalyst graph ALONE. No mention of cost, margin, or energy.
    (`@[reducible]` only lets `decide` synthesize the decidability instance; it adds
    no mathematical content.) -/
@[reducible] def RosenClosed (net : Network) : Prop :=
  net.requires.all (fun c => net.produces.contains c) = true

-- ═══════════════════════════════════════════════════════════════════════════
-- Axis 2 — Endorsement (energetic profile ONLY)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The energetic profile, independent of the catalyst graph.
    `margin`        : the internal store able to bear an irreversible cost.
    `reconfig_cost` : the cost a perturbation imposes.
    `energy_external` : where the throughput comes from. Kept for honesty and to
       match §4.5: energetic autarky is UNIVERSAL and does NOT sort — organism and
       whirlpool alike draw energy from outside — so the verdict must not, and does
       not, turn on this field. -/
structure EnergyProfile where
  margin : Nat
  reconfig_cost : Nat
  energy_external : Bool

/-- Endogenous endorsement: an internal margin covers the reconfiguration cost, so
    the irreversible trace falls ON the entity. Depends on the energetic profile
    ALONE — no mention of catalysts, production, or the graph. -/
@[reducible] def EndogenousEndorsement (p : EnergyProfile) : Prop :=
  p.margin ≥ p.reconfig_cost ∧ p.margin > 0

-- ═══════════════════════════════════════════════════════════════════════════
-- The entity carries BOTH axes as independent components
-- ═══════════════════════════════════════════════════════════════════════════

structure Entity where
  net : Network
  profile : EnergyProfile

@[reducible] def closed   (e : Entity) : Prop := RosenClosed e.net
@[reducible] def endorses (e : Entity) : Prop := EndogenousEndorsement e.profile

/-- The individuation verdict of the present account: strong unity (a `self`) iff
    the entity endorses the cost on its own margin. This is the paper's criterion.
    It turns on `endorses` — the ENERGETIC axis — not on `closed`. That is the
    thesis; its legitimacy rests on the independence proved below, not on this
    definition. -/
inductive Verdict where
  | self       -- strong unity: endorses on its own margin
  | carriage   -- borrowed unity: cost falls outside
  deriving DecidableEq, Repr

def verdict (e : Entity) : Verdict :=
  if e.profile.margin ≥ e.profile.reconfig_cost ∧ e.profile.margin > 0
  then Verdict.self else Verdict.carriage

-- ═══════════════════════════════════════════════════════════════════════════
-- The four combinations (the independence square)
-- ═══════════════════════════════════════════════════════════════════════════

/-- CLOSED + MARGIN. Produces its own catalyst, store covers the cost. The self. -/
def organism : Entity :=
  { net := { requires := [0], produces := [0] },
    profile := { margin := 10, reconfig_cost := 3, energy_external := true } }

/-- CLOSED + NO MARGIN — the decisive witness. Produces every catalyst it requires
    (Rosen-closed, exactly like the organism) yet carries no store, so a
    perturbation's cost falls on the feed. A self-regenerating chemistry in a flow
    reactor. Rosen: a full (M,R) system. Endorsement: a carriage. -/
def selfCatalyzingFlow : Entity :=
  { net := { requires := [0], produces := [0] },
    profile := { margin := 0, reconfig_cost := 3, energy_external := true } }

/-- NOT CLOSED + MARGIN. Imports its catalyst, but carries a store — a
    battery-backed dissipative structure. -/
def bufferedNonClosed : Entity :=
  { net := { requires := [0], produces := [] },
    profile := { margin := 10, reconfig_cost := 3, energy_external := true } }

/-- NOT CLOSED + NO MARGIN. The whirlpool: makes none of its "catalysts", no store. -/
def whirlpool : Entity :=
  { net := { requires := [0], produces := [] },
    profile := { margin := 0, reconfig_cost := 3, energy_external := true } }

/-- [■] THE INDEPENDENCE SQUARE. All four cells of (RosenClosed × Endorsement) are
    inhabited. Closure sorts the left column from the right; endorsement sorts top
    from bottom; the two vary freely. The verdict cannot be a function of closure. -/
theorem square_inhabited :
    ( closed organism           ∧  endorses organism) ∧
    ( closed selfCatalyzingFlow ∧ ¬ endorses selfCatalyzingFlow) ∧
    (¬ closed bufferedNonClosed ∧  endorses bufferedNonClosed) ∧
    (¬ closed whirlpool         ∧ ¬ endorses whirlpool) := by
  decide

-- ═══════════════════════════════════════════════════════════════════════════
-- The decisive results
-- ═══════════════════════════════════════════════════════════════════════════

/-- [■] THE DECISIVE RESULT. Rosen closure does NOT entail endogenous endorsement:
    a closed entity may fail to endorse. Hence `closed → endorses` is FALSE, the
    two axes are independent, and a criterion built on closure alone cannot deliver
    the endorsement verdict. `selfCatalyzingFlow` is the witness that opens the door. -/
theorem closure_does_not_entail_endorsement :
    ¬ (∀ e : Entity, closed e → endorses e) := by
  intro h
  have hc : closed selfCatalyzingFlow := by decide
  have he : endorses selfCatalyzingFlow := h selfCatalyzingFlow hc
  revert he
  decide

/-- [■] THE CONVERSE. Endorsing does not entail being closed: `bufferedNonClosed`
    endorses yet is not Rosen-closed. With the previous theorem, the axes are FULLY
    independent — neither determines the other. -/
theorem endorsement_does_not_entail_closure :
    ¬ (∀ e : Entity, endorses e → closed e) := by
  intro h
  have he : endorses bufferedNonClosed := by decide
  have hc : closed bufferedNonClosed := h bufferedNonClosed he
  revert hc
  decide

/-- [■] SENSE A, correctly witnessed — the pair the argument actually needs.
    `organism` and `selfCatalyzingFlow` are BOTH Rosen-closed: Rosen's criterion
    cannot tell them apart. Yet the endorsement criterion assigns opposite verdicts,
    `self` vs `carriage`. THIS is "endorsement separates what closure ranks
    together" — and note it is NOT the organism/whirlpool pair of §6, which Rosen
    already separates (the whirlpool is not closed), and which therefore proves only
    the weaker claim that cost is present where Rosen is silent. -/
theorem endorsement_separates_within_closure :
    closed organism ∧ closed selfCatalyzingFlow ∧
    verdict organism = Verdict.self ∧
    verdict selfCatalyzingFlow = Verdict.carriage := by
  decide

/-- [■] The honest core of the original `endorsement_separates`, correctly scoped:
    equal perturbation cost, opposite verdict, by the endorsement split alone (and
    here the two entities are ALSO both closed, so this is strictly stronger than
    the original while claiming strictly less than it did). This is orthogonality to
    COST; the stronger orthogonality to CLOSURE is the theorem above. -/
theorem equal_cost_opposite_verdict :
    organism.profile.reconfig_cost = selfCatalyzingFlow.profile.reconfig_cost ∧
    verdict organism ≠ verdict selfCatalyzingFlow := by
  refine ⟨rfl, ?_⟩
  decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Functional independence: the verdict is a function of the energetic axis alone
-- ═══════════════════════════════════════════════════════════════════════════

/-- [■] The verdict depends on the energetic profile ALONE: entities sharing a
    profile share a verdict, whatever their catalyst graph. So closure contributes
    NOTHING to the verdict — on its own, Rosen's axis is verdict-irrelevant. -/
theorem verdict_ignores_closure (e₁ e₂ : Entity)
    (h : e₁.profile = e₂.profile) : verdict e₁ = verdict e₂ := by
  unfold verdict; rw [h]

/-- [■] Symmetrically, closure depends on the catalyst graph alone, untouched by
    the energetic profile. Stated for completeness of the orthogonality. -/
theorem closed_ignores_profile (e₁ e₂ : Entity)
    (h : e₁.net = e₂.net) : closed e₁ = closed e₂ := by
  unfold closed; rw [h]

-- ═══════════════════════════════════════════════════════════════════════════
-- Audit — reproduce the axiom footprint of every cited result
-- ═══════════════════════════════════════════════════════════════════════════

#print axioms square_inhabited
#print axioms closure_does_not_entail_endorsement
#print axioms endorsement_does_not_entail_closure
#print axioms endorsement_separates_within_closure
#print axioms equal_cost_opposite_verdict
#print axioms verdict_ignores_closure
#print axioms closed_ignores_profile

end RosenEndorsement
