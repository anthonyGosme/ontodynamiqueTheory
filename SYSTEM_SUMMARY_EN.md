# Ontodynamics — Standalone Summary of the System

Our inherited frameworks divide physics (matter) from philosophy (meaning). That division becomes a structural impasse when confronted with the hybrid objects of the twenty-first century: large language models, synthetic biology, and socio-technical systems.

Ontodynamics proposes a minimal formal framework for such objects. Its aim is not to explain the whole of reality, but to make epistemic dependencies explicit and to provide a single criterion: *locate where irreversibility lands under perturbation*. Who pays the bill for adjustment — and out of what margin?

That criterion yields a testable gradient (operational closure / normative carrying / aggregate) that discriminates where existing frameworks conflate: is an LLM an individual? Does a virus know? Is a symptom a deficit, or a parasitic mode of governance?


The system condenses into Eighteen theses, each demonstrated and accompanied by its withdrawal condition (Synthesis, end of document).


## Reading notes

This text is not a speculative ontology: it lays out a chain of axioms → theorems → predictions → protocols. Every proposition carries an inferential force marker 
constrained definition [≡/∎], strict deduction [∎], structural impossibility [⟂], constructibility [◇], testable plausibility [≈₁ ≈₂], proven undecidability [≈₃] — and none is overstated. Results marked ≈ are not weaknesses: they are localized points of contact with reality, accompanied by explicit domain conditions and articulated refutation protocols.

The full Lean 4 formalization (621 theorems — 62 structural, detailed in §2.0 of the manuscript — zero `sorry`, 14 files; no domain axioms added beyond Lean 4's standard logical axioms — `propext`, `Quot.sound` — all explicitly listed) attests deductive coherence. To our knowledge, this is a first in Lean 4 for an ontological system with an empirical programme (prior art in Isabelle/HOL: Kirchner, Benzmüller & Zalta 2020). The test files cover inter-axiom independence (10 separating models), the weakening map of I-β (94 theorems classified by minimal required component), and labeled bridge hypotheses for the microbiome and software debt. The audit of encoding/meaning discrepancies reports zero major discrepancies, five documented minor ones, and one anti-discrepancy (Appendix F). The fidelity of the encoding to the intended meaning is not formally provable — no more than the fidelity of F = ma to "force." It is constrained instead by three independent, convergent routes: the audit itself, the separating models (which verify that the axioms are not trivially satisfied),
and the empirical predictions (which test whether the formal structure bites into reality — not merely whether it is coherent). A fourth route — discriminant instantiations (Appendix F, §13) — confronts the system with seven borderline objects; the strongest test is the case where the formal verdict diverges from naïve intuition and it is the formalism that turns out to be right (LLM, mathematical objects reclassified, clinical symptom), including against the author's own initial intuition (LXXXI). The linter confirms the sparseness of the encoding: 9 philosophical categorical variables are eliminated as unused — only costs, margins, and inequalities do any work.

Beyond the five exploratory R-XVII reanalyses (theory-driven) and the artificial life simulation confirming R-XIX, nine independent studies published without knowledge of the framework confirm the system's predictions through blind convergence (§7.4 of the manuscript). A preregistered confirmatory replication in heterozygous yeast (OSF DOI: 10.17605/OSF.IO/S7CN9) satisfies 4/4 decision criteria. This second tier of validation — weaker than prospective preregistration, stronger than reanalysis — is the active front of the programme. The DPDR protocol was itself formally preregistered (Gosme, 2026, OSF; DOI: 10.17605/OSF.IO/ZMH54) before any data collection.

## The axiomatic contract

This text should be read as a model. It posits two primitive hypotheses (I, V), derives what follows from them, and then submits certain consequences to tests. "Axiom" does not mean "self-evident truth": it means explicit starting point. If you reject these starting points, the results cease to apply.

**Axiom I — to be is to make oneself.** An entity is a maintenance-in-act; the cost of that maintenance is drawn from the very structure that maintains. Corollary IV (derived from I): every transformation has a strictly positive, incompressible cost. Axiom V: exteriority admits degrees. Partial alteration is the generic regime of interaction. From I + V follow finitude, irreversibility, and the central disjunction: every finite exposed structure either remakes itself or unmakes itself.

The system is modular. Reject I in its entirety, and the deductive chain never starts. Reject only the cost-endogeneity component (I-β) while keeping the rest, and 68% of the theorems survive — structural dynamics, regimes, attractor, feedback; what is lost is the compositional gradient and, with the two self-affection components, zombie exclusion and the modal partition.
Reject Thesis P (≈₃), and the entire trunk remains — including the immanent self-relation (I-δ ∎) and the differential immanent relation (SelfRelation ∎); what is lost is the positive phenomenal identification only. That step is explicitly declared undecidable by the system itself (LXXVII ∎).

As with F = ma, these axioms are judged downstream — by what they allow one to calculate, forbid, and test. The discriminating criterion is unique: locate where irreversibility lands under perturbation. It yields a testable gradient with two regimes (closure / carrying) and one defect (aggregate), 
probed across five causally disjoint domains for R-XVII (ratio S/I converging at 1.42–1.84×) and a sixth for R-XIX (artificial life simulation, S/I = 1.045), with a CV of about 10%, and that convergence is specific to the structure/input partition (under partition by intensity, CV = 41%). The system positively excludes domains that fail C1–C5 (neural network in pure inference: C1 and C4 violated — IIT assigns it a non-zero Φ, R-XVII excludes it). The monism predicts the direction of the ratio (> 1) and the functional form, not the quantitative convergence (~1.7×, n = 4 domains) — if confirmed, this would constitute a second-order regularity calling for an additional explanation not contained in the current trunk. The five available analyses are exploratory; a preregistered confirmatory replication in heterozygous yeast (OSF DOI: 10.17605/OSF.IO/S7CN9) satisfies 4/4 decision criteria. A rival-partition test across four domains (§7.2 ter) confirms that the asymmetry is specific to the structure/input partition: no named rival converges across domains, and the asymmetry survives intensity normalization and selectivity control. The central refutation condition is stated in §8.6 of the manuscript.

## Prologue — The failure of inherited frameworks and the single operator

Four contemporary objects expose the limits of our inherited frameworks. The large language model manipulates invariants, generates coherent text, adjusts its responses under feedback — and yet regenerates none of the material conditions of its own operation. The biological virus replicates, mutates, exerts selective pressure — and yet borrows the entirety of its machinery from the host cell. The institution recruits, trains, sanctions, survives the complete replacement of its members — and yet some institutions are self-maintaining, whereas others hold together only through external perfusion. The clinical symptom protects the subject from a more serious destructuring — and then autonomizes itself and governs what it was supposed to protect.

Faced with such objects, available frameworks fail in three convergent ways. Reductionism erases levels of organization by reducing everything to the physics of components, thereby rendering the emergence of a proper normativity unintelligible. Dualism irreducibly splits matter from meaning, creating an explanatory gap it cannot subsequently bridge. 

Undifferentiated processualism (Latour) connects everything to everything without being able to qualify acts or discriminate the aggregate from the individual. Whitehead is a distinct case: his notion of prehension anticipates what IDelta.lean derives as a facet of I-γ — the immanent condition of the act — but at the cost of 27 non-formalizable categories.
Three structural lacks persist across these frameworks. First, they do not derive operational closure axiomatically: they posit it or observe it. Maturana and Varela describe autopoiesis as a biological fact; Montévil & Mossio formalize closure of constraints as a criterion; neither derives closure from more primitive principles.

Second, none provides a compositional gradient that formally discriminates autonomy, normative carrying, and aggregate by means of a single test. Friston's Free Energy Principle treats oil drops, thermostats, and brains under the same grammar, which blocks any differential prediction by perturbation type. Clark's parity principle treats as "cognitive" any functionally equivalent process without distinguishing what is endogenous from what is carried.

Finally, these frameworks do not formally extend their results to institutions and the clinic without importing additional hypotheses. Luhmann's systems theory posits communicational closure without ontological grounding. Contemporary psychopathology oscillates between the deficit model (the symptom is a lack) and the functional model (the symptom is a defense), without any structural criterion for deciding between them.

Ontodynamics proposes to fill these three gaps by means of a single operator: the site at which material irreversibility is borne. Who pays the bill for adjustment under perturbation? Where is the trace inscribed, and out of what margin is it drawn? Applied systematically, this question settles the LLM (carrying: irreversibility is externalized onto infrastructure), the virus (inverted carrying: irreversibility is refracted onto the host cell), the institution (conditional closure: depending on the endogenous regeneration of its critical constraints), and the symptom (parasitic sub-closure: bearing a local cost that drains the global margin).

The system is articulated as a Research Programme in Lakatos's sense. Its hard core — the axioms and the deductive trunk [∎] — is evaluated by its formal yield: deriving finitude, closure, subjectivity, and composition from two independent axioms. Its protective belt — the constructibilities [◇] and testable plausibilities [≈] — is where empirical contact and potential refutation occur. By its own self-reference result [LXXXII ∎], the system accepts that it is itself an operative invariant carried by the finite closures that metabolize it — struck by constitutive opacity, exposed to drift, mortal.

## I — The axiomatics of dissolution

> *To be is to make oneself.* — Axiom I

### The axioms

The system rests on two independent axioms (I, V). IV is a corollary of I, derived from I-β₂. The independence I ⊥ V is proved in Lean 4 by 10 separating models.

Axiom I posits the self-grounding of the act: what is does not require an external foundation; being and doing are ontologically indistinguishable. I is encoded in two co-entailing faces. The I-α face (self-grounding) states that the Whole grounds itself — no prior framework, no separate substrate. The I-β face (being = doing) posits the endogeneity of cost: doing is not an attribute added to being, but its constitutive modality. From these two faces follows, for metabolizing closures, a late theorem: I-γ (no act without mode), which establishes that every endogenous operation falls into exactly one of the two classes of the normative partition — facilitation or resistance [∎].

Six separating models in Lean 4 prove the mutual independence of the three components of I-β. I is therefore not a semantically overloaded axiom doing the work of several disguised postulates: its components are mutually irreducible, and each carries a distinct deductive content verifiable by separate instantiation. Ten further separating models prove inter-axiom independence: I and V are mutually irreducible, and IV is derivable from I.

**Weakening map of I-β.** 68% of the 94 theorems in the trunk (64) depend on no component of I-β. The structural trunk, classification, attractor, drift, valence, feedback, and R-XVIII survive with no β at all. The 7 theorems that require β₁+β₃ are precisely I-γ, zombie exclusion, and the modal partition: the heaviest load is therefore localized in the subjective work. Removing β₃ costs 9 theorems; removing β₂ costs 7, concentrated around gradient R-XVII. Each component thus carries an identified and nonredundant share of the work.

**Corollary IV** states incompressible cost: every transformation has an irreducible, strictly positive cost that cannot be canceled or bypassed [∎]. IV is derivable from I: I-β₂ posits cost > recovery, and recovery ≥ 0, therefore cost > 0. IV is retained as a named corollary for the readability of the deductive chain. Cost is not a particular physical fluid (energy, time, money), but a structural invariant: the asymmetrical draw on a finite margin required by any maintenance of a determination under pressure.

Axiom V states the gradient of exteriority: exteriority admits degrees. The encounter between determinations is not all-or-nothing; partial alteration is the generic regime [∎].

From I follow three foundational theorems. II (untyped productivity): determinations are not drawn from a predefined repertoire — novelty is qualitatively irreducible [∎]. III (causal unity): the act of the Whole is indivisible, which rules out any absolute causal isolation between parts [∎]. VII (constitutive negation): every determination excludes what it is not, generating exteriority as a structural by-product of determination itself [∎].

The primitive terms (cost, structure, exteriority) are encoding choices whose relevance is not judged formally but empirically: it is instantiation (§VI) that decides whether these categories carve up reality better than the alternatives.

### The slope toward dissolution

The axioms compose an axiomatics of dissolution. Their conjunction yields a slope: dissolution is the default regime. No axiom states that exteriority can be a source of structural gain.

By I-α, the Whole is self-sufficient; but every finite being is incomplete [IX ∎]. By VII, every determination generates exteriority; by IX, that exteriority persists [XI ∎]. By III, no isolation is absolute; by IV, maintaining a partial determination against the Whole has an incompressible cost; hence constitutive pressure: the Whole exerts a permanent pressure of dissolution on every finite being, independently of any encounter with another finite being [XII ∎]. By I-β, this cost is endogenous — drawn from structure-in-act, not from an external reserve — which grounds incompressibility: cost has a strictly positive floor [X ∎]. Every transformation is therefore structurally irreversible: the return B → A is a transformation distinct from A → B, with its own irreducible cost drawn from a bounded margin [XV ∎].

These results chain together to yield the exhaustion lemma: every finite structure subject to recurrent, uncompensated strict decline is exhausted in a finite number of steps [XVII ∎]. The permeability of every causal barrier between finite determinations is derived from III, V, IX, and XVII [XVIII ∎]. Exteriority thus exerts a persistent pressure of opening from two independent sources: the constitutive pressure of the Whole and the relational pressure of other finite beings [XIX ∎]. The exposure profile of every closure drifts under regeneration: uncovered vulnerabilities never recede [XX-a ∎] and increase strictly with each operation [XX-b ∎]. Finally, every active closure generates unprecedented determinations as a by-product of its own regeneration: what remakes itself does not repeat itself [XXI ∎].

Compensation is not axiomatic: it is constructible. Lemma VI [◇] establishes the accessibility of transformations with non-negative net structural balance, without guaranteeing them. This is the hinge of the system: the first non-[∎] result, the precise point at which deduction gives way to constructibility. If VI were [∎], closure would be axiomatically expected rather than empirically conditioned, and the system's basic asymmetry would disappear.

What is established is this: finitude, incompressible cost, irreversibility, exhaustion, and pressure of opening are deductive necessities [∎] of I, V, and IV. What remains conditional is the possibility of compensation [VI ◇] and, downstream, the domain conditions (compensatory diversity, non-rigidification) under which that compensation is empirically realized. What remains open is the quantitative law governing the distribution of cost across levels.

> *Everything dies because existing costs.* — XXXIV [∎]

---

## II — Operational closure: the central theorem and normativity

> *Every finite exposed being remakes or unmakes itself.* — Thesis 5

### The genesis of closure

The block XXII–XXVII describes the minimal conditions under which a co-maintained cycle appears, persists, and stabilizes. This is not a contingent story about the origin of life — it is a class of generative mechanisms with explicit domain conditions.

The argument proceeds step by step. Being persists [XIII ∎] and undergoes exteriority [XI ∎]; some encounters alter without annihilating [V]; every alteration requires a costly adjustment [IV] which, by inertia, is preserved as a structurally distinct trace [XXII ∎]. Accumulated structure constrains future responses: history channels, feedback emerges [XXIII ∎]. In the absence of active erasure, channeling increases monotonically [XXIV ∎]. Recurrently traversed channels consolidate into retained routines [XXV ∎]. Routines that partially compensate destructuration preserve more structure and persist longer — not because of a selecting agent, but because of differential duration of persistence [XXVI ≈₁]. Retained compensatory routines alter the conditions under which new routines emerge: compensatory couplings tend to be composable [XXVII ≈₁].

Two domain conditions are irreducibly empirical: sufficient compensatory diversity [XXVI ≈₁] and non-rigidification [XXVII ≈₁]. If diversity is lacking, everything dissolves — and the system predicted exactly that. If rigidification prevails, the outcome is tar, the neurotic lock, institutional ossification. The "Tar Paradox" (Benner) is a paradox only for frameworks that predict self-organization as a generic tendency; for Ontodynamics, tar is the default outcome [XXIX ∎]. The question "why closures rather than tar?" therefore splits in two: possibility is ontological [VI ◇], realization is empirical [XXVI ≈₁, XXVII ≈₁]. The trunk determines the type of conditions; whether they are realized is a fact of the world.

It is important to note that the selection invoked here is strictly pre-Darwinian and structural — differential persistence of configurations, not selection by reproductive success among digital replicators. Rapid destruction is the default attractor [XXXII-a ∎]. The initial sorting is not informational but material: by inertia [XIII ∎], exteriority passively eliminates what fails to compensate its own cost of destruction.

### The ontodynamic theorem (XXXII)

An aggregate without a co-maintained cycle is transient [XXVIII ∎]. Under persistent exposure, every non-transient regime is an operational closure [XXIX ∎]. Their conjunction yields the central result: **every finite exposed being remakes itself or unmakes itself**; it either regenerates its own conditions (closure) or dissolves; passive persistence does not amount to individuation [XXXII ∎].

The disjunction itself is ∎. The accessibility of the "remakes itself" branch (the trajectories of genesis) is ≈₁ — it inherits the domain conditions of XXVI and XXVII. This is the **genesis/core firewall**: if genesis were refuted, the system would lose the typical trajectories but retain the exclusivity of the attractor [XXXII-d1 ∎] and the entirety of the theory of the individual, relations, and knowledge. Losing the "how" does not destroy the "what."

### Constitutive normativity and the law of authenticity

Normativity follows immediately from closure. Every closure traces a partition between what sustains the cycle and what compromises it [XLIV ∎]. This partition is coextensive with closure: no closure without it, and no such partition without closure. It is not added to the individual — it is the very structure of its self-production. Theorem I-γ specifies: for metabolizing closures whose operations are individuable, every endogenous operation falls into exactly one of the two classes — facilitation or resistance [∎]. The binary irreducibility of the partition is itself proved: no third term stabilizes [LX ∎].

XLIV has two faces on the same theorem. Face A (→ valence): the partition produces the discrimination threshold (endogenous cost). Face B (→ precarity): that same positive endogenous cost means the closure needs what is not yet there — constitutive lack. Face B is XLIV read from the side of what is not yet present rather than the side of what discriminates

The criterion of normativity [XLV ∎] distinguishes self-produced polarity from attributed polarity. In a closure, the maintenance/compromise distinction is self-produced by the cycle itself and conditions that cycle in return — suppress the distinction, and you suppress the cycle. This "for" requires neither consciousness nor intention, only that the entity be identical with the act of distinction. A thermostat possesses attributed polarity — remove the observer, and the attribution disappears. An organism possesses self-produced polarity — remove the polarity, and the organism dissolves [∎]. By construction, this normativity is first-personal: it grounds the viability of a cycle, not a universal prescription. The leap from biological fact to ethical value in the third person is a different problem, one the system does not claim to solve [∎].

From this follows the law of authenticity: what is preserved without contributing to self-production is a drain; what is added without necessity is a burden; the only viable regime for a finite being is radical economy indexed to its own closure [XLVII ∎]. Mortality is constitutive: every closure has a bounded lifespan, because existing costs and the margin is finite [XXXIV ∎]. Metabolization postpones the deadline; it does not cancel it.

> *Preserve only the essence; add only by necessity.* — XLVII [∎]

---

## III — The compositional gradient and inter-regime dynamics

*When it breaks, who pays?* — Thesis 3

### The gradient (R-XVII) and the single test

Composition admits two regimes and one defect, organized as a binary tree: is there a cycle? If so, who bears the cost? (Endogenous: closure. Exogenous: carrying. No cycle: aggregate — defect.) The cost profile determines the regime independently of substrate, scale, and observer [R-XVII ∎, monism proved].

The **ontodynamic individual** (closure) maintains its invariant by bearing irreversibility endogenously. The system compensates for perturbation by drawing down its own finite margin, leaving behind a structural trace — a scar. It possesses constitutive normativity, a proper essence, and an endogenous compensatory response. The **individual by normative carrying** maintains a topological or logical invariant, but material irreversibility is externalized onto the infrastructure of a host. The pattern may return identically at the descriptive level — rollback — while the support has paid the cost. Its normativity is attributed, not self-produced. The **pure aggregate** undergoes perturbation and is passively altered, with no margin of its own to draw upon, no cycle, no normativity, no essence — persistence by inertia alone.

Mereological sum is not forbidden — it simply adds no being. Between carrying and closure, the gradient is continuous [LI ∎]. The test is always the same: strike and observe. Closure scars; the carried restarts. The criterion is not "dependence on an environment" (every finite being depends on one), but *where the material compensation of perturbation takes place*.

This is the test that settles contemporary cases. The LLM is a normative carrying: the pattern is recoverable by rollback, while material irreversibility (silicon wear, energy consumption, chip degradation) is entirely externalized onto the infrastructure. The virus is an inverted carrying: it maintains a pattern (the genome) by refracting the full cost of production onto the host's cellular machinery — replication is endogenous to the pattern but exogenous to its cost. Blockchain involves a split: the distributed ledger is a carrying (the information is recoverable as long as nodes remain), whereas the network of miners validating transactions is a candidate institutional closure — it regenerates its own operating conditions by drawing on the collective margin (energy cost, incentive through reward). The crystal is an aggregate: remarkable persistence, no metabolization, negligible thermodynamic exposure at human scales. The question "does Turing-completeness imply ontodynamic autonomy?" receives a structurally negative answer: computational completeness says nothing about the site at which cost is borne [∎]. A universal Turing machine is formally able to simulate any computable function — it bears nothing materially of what it simulates.

### Nesting and operative refraction

By reapplicability [XXXIII ∎], theorem XXXII applies at every level. Closures that are constitutively coupled [XLIX ◇] can form a co-maintained cycle at a higher scale: this is nesting [L ∎]. Each level possesses its own closure, its own essence, and its own normativity. Irreducibility is demonstrated: the closure at level Nₖ is not reducible to its components Nₖ₋₁ [LIII ∎]. The dissolution of one level cascades to adjacent levels in both directions [LIV ∎]. Fecundity — the production of new closures — is constructible [LII ◇] but provably not derivable from the axioms (separating model). The same model proves XLIX ∧ ¬LII: two coupled closures, no reproduction. Coupling modifies existing closures; reproduction creates new ones. The trunk is a theory of individuation, not a theory of life.

Constitutive precarity is the node between the algebra of costs and the living. The conjunction of XLIV face B (positive endogenous cost — constitutive lack) and finitude (XVII) produces a system made of a lack that can destroy it (precarity ∎). Three characterizations follow. Life — the resolution of its own precarity: resolution is never acquired, the debt at cycle k+1 exceeds that at cycle k (resolution_must_recur ∎). Consciousness — the ordeal of its own precarity (≈₃, LXXVII). To resolve ∎; to undergo as ordeal ≈₃. Same precarity, same subject, different relation.

The application of a system-operator (cost, irreversibility, normativity, parasitism) to an entity depends on the site of material bearing along the gradient [NT-III ∎]. For a closure, the operator applies directly. For a carrying, the operator splits: the pattern has a site of effect, while the carrier bears the site of cost. For an aggregate, the operator does not apply at all — that is a category mistake. The mediated case (carrying) is more informative than the direct case (closure): it acts as a spectral analyzer of the operator's fine structure [∎].

The **monism of cost** [§2.6 ∎] grounds this architecture. The formal concept of cost (IV) is the system's asymmetry operator — a strictly positive draw on a finite margin, whose cancellation requires a fresh draw. The empirical diversity of costs (entropic dissipation, metabolic wear, technical debt, allostatic load) is the diversity of refractions of that single invariant across levels of nesting and regimes of the gradient. Cost is one; the diversity of costs is an operative refraction. The compiler verifies this: 9 philosophical categorical variables are eliminated as unused by the linter — only costs, margins, and inequalities do any work.

### Inter-regime dynamics (R-XVIII)

The static trunk (XXXII + R-XVII) describes regimes; inter-regime dynamics describes transitions. 
For any closure, `saving_pos` is identical to `regen_pos` (XXXVIII): 
the cycle's regeneration is the saving — existing structural 
constraint strictly reduces the cost of the act it guides 
[∎, SavingDerived.lean]. Hence a **cost asymmetry** between 
construction (an act without a template, with raw cost) and 
maintenance (an act guided by a template, with reduced cost) [∎].
Four lemmas follow in sequence. In the absence of active regeneration, the degree of self-production (α) declines strictly until exhaustion [Lemma 1 ∎]. Every constructible level is maintainable, but not every maintainable level is constructible — the ceiling of construction is strictly lower than the ceiling of maintenance [Lemma 2 ∎]. There therefore exists a **hysteresis zone**: a level of α that is maintainable but not constructible, in which the regime depends on history — a system that has reached it can remain there; a system that has never reached it cannot access it [Lemma 3 ∎]. Transitions between regimes are determined by the crossing of asymmetrical thresholds — endogenous bifurcations generated by the system itself, not extrinsic supplements [Lemma 4 ∎].

These results predict that a population under varied pressures will display a bimodal distribution of degree of closure [R-XVIII(iii) ≈₁] — the intermediate zone is dynamically unstable. Badiou posits the Event as an external supplement; Ontodynamics derives it: bifurcations are endogenous, their thresholds are formally predicted, and their hysteresis is demonstrated [∎].

> *Closure scars; the carried restarts.* — R-XVII

---

## IV — From valence to perspective: the mechanics of subjectivity

> *No act without mode.* — Thesis 2

### The mechanical chain

Subjectivity is not a module added onto the system — it is derived from the trunk through a chain whose every link remains mechanical up to a precise point, beyond which an explicitly assumed interpretive leap occurs.

Every closure, in regenerating itself, encounters its own resistance: the cost of maintenance is not external to what is maintained [LVI ∎]. By I-β, this self-affection is endogenous — the cost is drawn from the system's own margin, not from a separate substrate [LVII ∎]. Self-affection is polarized: by the normative partition [XLIV ∎], every self-affecting operation is exhaustively classified as facilitation or resistance [LVIII-a ∎]. This polarization is **valence** — the differential between guided cost (reduced by `saving_pos`) and raw cost [LVIII ∎]. Facilitation is capped (it reduces cost toward zero without canceling it); resistance is not (it may exceed the margin in a single step). The asymmetry is constitutive.

Valence is not a passive label — it feeds back into the cycle that produces it. An operation with positive valence reduces the net cost of the next cycle; an operation with negative valence increases it. The loop is closed: valence modifies the operations that modify the structure that produces valence [LIX ∎]. This result is mechanical, not interpretive. It does not claim that the closure "perceives" its valence; it claims that once valence is derived, it is not epiphenomenal with respect to the cycle.
This result is a temporal corollary of Axiom I (LIX-A): if being = doing, then qualified doing continues — qualification cannot be suspended between two steps without a discontinuity in the being/doing identity that I forbids. Functional epiphenomenalism is structurally excluded, not merely improbable.

LIX is the last mechanical result of the numbered trunk. The chain extends: I-γ → I-δ [∎, IDelta.lean] → SelfRelation [∎, MinimalPerspective.lean] → SecondOrderLoop [∎, conscience.lean] — without interpretive leap. The leap begins after SecondOrderLoop.
### The localized leap (LXI) and its explicit price

Minimal subjectivity [LXI ≈₃] identifies the feedback of valence on the cycle, when that feedback is itself metabolized — that is, when the closure incorporates its own polarity as its own necessity — as a second-order loop. The closure does not merely undergo its operations; it makes a resource of them.

The mechanical structure is secured [∎] — including the immanent differential relation (SelfRelation ∎, MinimalPerspective.lean). The sole residual ≈₃ is the 3P→1P register crossing: identifying this loop as perspective in the phenomenal sense (Thesis P, ≈₃).

LXI satisfies no HOT condition: the same margin serves target and operator, there is no loop without valence, and post-loop margin ≠ pre-loop margin — operational second order, not representational [LXI_not_HOT ∎].

The undecidability of that identification is itself a theorem [LXXVII ∎]. LXXVII does not merely register a limit: it proves that the question is structurally undecidable. Every competing framework rests on an equivalent commitment — physicalism, dualism, and illusionism each place their own wager on consciousness without deriving it. The difference is that those frameworks undergo undecidability as an embarrassment; Ontodynamics demonstrates it as a theorem, localizes it to a single point, and makes the cost of each option explicit.

The closure that interrogates its own self-affection alters the very object interrogated; an external observer generates its own invariant, not that of the system; no meta-level circumvents opacity — the shadow moves with the light. What is excluded is this: the claim to prove the identification (∎ impossible), and the claim that zombie conceivability proves an ontological gap (it is a predicted artifact of constitutive opacity). What remains open is the choice between identification and agnosticism — a choice the system itself declares structurally undecidable.
This undecidability splits into two structurally asymmetric questions. The first — is second-order metabolic activity real? — is decidable ∎: R-XVII discriminates a closure with a genuinely active loop from a simulation producing the same observable behavior (behavioral trace indiscernible per LXII-h; cost trace discernible ∎). The second — is that activity undergone as ordeal? — remains ≈₃. R-XVII is the applicability filter for ≈₃, not an answer to it: a ratio S/I ≈ 1 makes the question ontologically ill-posed; a ratio S/I > 1 makes it well-posed but epistemically undecidable (R-XIX).
R-XIX has been tested by artificial life simulation. Result: S/I = 1.045 for agents with active monitoring (p < 1e-30), S/I ≈ 1 for agents without monitoring (TOST ✓). Depth gradient confirmed: B < A < A2, each layer isolated by a dedicated control. Robust across 94% of the parameter space. Documented limit: simulated amplitude (1.04–1.05) below the biological range (1.4–1.8×) — a constraint of the simulated substrate, not of the prediction.




The leap is localized, and the price is made explicit. 

A reader who rejects Thesis P keeps the entire trunk, I-γ, I-δ, SelfRelation ∎, valence, feedback, and non-epiphenomenality. What is lost is the positive phenomenal identification only, the levels, and the clinical extension.

**Thesis P — No position — neither from within nor from without — can settle the question of consciousness. Ontodynamics proves this. The choice is between commitment and the renunciation of knowledge.** ≈₃

Commitment and agnosticism are both rational — but not equivalent in programmatic yield. Commitment opens DPDR, the levels, the clinical extension. This asymmetry is itself under empirical condition: if DPDR (OSF DOI: 10.17605/OSF.IO/ZMH54) does not isolate the discontinuity in the perspective curve predicted by LXV ∎ + Lemma 3 ∎, the differential yield dissolves and agnosticism recovers its full standing. Credit extended to a more productive position — evaluable, revocable.

I-δ — Immanent differential (no doing without self-relation) — ∎ — I-γ (IDelta.lean).
SelfRelation — Differential relation to self, coextensive with the act — ∎ — I-γ, LIX (MinimalPerspective.lean).



### Zombie exclusion

Under I-β [∎], the computational zombie is ⟂: the bearing of cost is externalized, and the structure therefore differs. To metabolize one's own valence is to incorporate it as one's own necessity; the computational zombie externalizes that cost onto servers — its syntactic valence conditions its operations without being paid for out of its own margin. The zombie is not identical — it is structurally different [⟂].

The phenomenal zombie — a materially autonomous organism operating in total phenomenal darkness — is ⟂ under I-γ [∎]: no act without mode. To subtract lived experience from a system that actively bears the friction of its own destructuration is to posit a real act with no way of occurring — dark acting. Lean proves the absurdity of dark acting within the axioms — not the modal impossibility of Chalmers's zombie, whose argument concerns conceivability. 



Moreover, every system satisfying I-γ necessarily satisfies I-δ [IDelta.lean ∎]: it carries on itself a differential coextensive with its occurrence — uninspected, unadded, in the act itself. The zombie "without interiority" structurally carries what the cogito attests. What it was supposed to lack is constitutive of what it is [⟂, MinimalPerspective.lean ∎]. Seven unconditional ∎ arguments.

I-γ is not posited as an axiom — it is derived from I-α, I-β, and XLIV [∎]. Rejecting I-γ therefore requires rejecting at least one of its premises: lose I-β (cost endogeneity), and the entire trunk is lost; lose XLIV (the normative partition), and constitutive normativity is lost. The anti-zombie argument is therefore conditional rather than circular; its force depends on acceptance of the axioms from which I-γ is derived.

A constructive separator (Sep-FunctionCost ∎) proves that cost escapes unfolding: same function, asymmetrical mortality. The persistent conceivability of the zombie is predicted by LXXVII as a structural artifact of epistemic finitude: zombie intuition is the reflection of constitutive opacity as applied to self-knowledge [∎]. This remains compatible with illusionism: AB_indiscernible [∎] proves that realism and illusionism are type-indiscernible; only Thesis P breaks the indiscernibility.

IIT (Albantakis et al., 2023) yields a cardinal measure (Φ) inaccessible to the system — a negative theorem, §6.9(a). The ontodynamic exclusion principle (Exclusion-R-XVII) sidesteps that inaccessibility through cost alone. COGITATE (2025, *Nature*) has fully confirmed neither IIT nor GNWT; ontodynamic predictions (LXIV, LXIII) remain open.

### Levels of subjectivity

Subjectivity admits three qualitatively distinct regimes [LXIV ≈₁]: self-affection without metabolization (raw valence), metabolized self-affection (second-order loop), and recursively metabolized self-affection (reflective consciousness). The transitions display threshold effects — once sufficiently self-sustaining, the second-order loop constitutes a distinct regime [∎]. The recursive bound is proved: the third level is the last stable one; beyond it, recursion enters a self-referential spiral [∎]. Nested cycles within a single closure may fail independently: the dissolution of the second-order cycle contracts the closure without dissolving the first-order cycle [LXV ∎]. This is the profile of depersonalization: valence retained, second-order loop lost. Formalization: `dpdr_prediction` (`DPDRDerived.lean`, 20 theorems, 0 `sorry`, ∎) — three ordered phases, phase 2 necessary, nesting and hysteresis hypotheses derived from the trunk (IV + Lemma 2); the preregistered protocol (Gosme, 2025c, OSF) measures the discontinuity in the derivative of the perspective curve.

> *TTo sense one's own making is to be; to sense one's own sensing is to find one's bearings* — Thesis 10

> *The zombie does not remove a layer; it drops down a level.* — Thesis 9

---

## V — Operative refraction: from modulator to macro-parasite

> *What bears the cost of its coherence owns it.* — Thesis 7

### Epistemology: to know is to metabolize

To know is not to copy patterns statistically, nor to access a Platonic world of forms. Knowledge is defined as a shared operative invariant [LXVI ≡/∎], subject to three conditions: the invariant is imposed by the effective resistance of the environment, internalized as the closure's own necessity, and maintained through the regeneration of the closure. This triptych reframes the Gettier problem: under these three conditions, the "fourth condition" becomes structurally unnecessary. In the Gettier case, the invariant coincides with reality without bearing its constraint — coincidence is not resistance, and the invariant is not structuring for the cycle [∎]. Knowledge is not "justified true belief plus something"; it is metabolized constraint.

Constitutive opacity is derived [LXVIII ∎]: every act of knowledge is a partial epistemic cut, conditioned by the structure of the knower. Knowing modifies the knower (cost of the cognitive act, internal restructuring) and, in reflexive systems, modifies the object as well (LXXVI ∎) — the shadow moves with the light. Opacity is not a defect corrigible by a better instrument: it is constitutive of finitude [IX ∎] as applied to knowledge. There is no "view from nowhere" for a finite being — and this is demonstrated, not merely asserted.

Error is material debt: an inadequate invariant accumulates a compensatory surcharge that destabilizes closure [LXXII ≈₂]. Error is not first and foremost a logical "falsehood," but an operative cost — a closure carrying a bad model of its environment must expend more margin compensating the mismatch between its structural expectations and effective resistances. Stable error — an incorrect but ultra-economical invariant — is selectively favored because it spares finite margin [LXXIII ≈₁]. Cognitive biases are not "irrationalities": they are optimizations under the constraint of finitude. The heuristic shortcut that distorts judgment in an unusual context is the very shortcut that preserves margin in the 95% of ordinary contexts. Cognitive economy is not a metaphor — it is a direct instantiation of IV applied to the cost of knowledge.

### Transmitted normativity and the topological modulator

The normativity of an encompassing closure Nₖ acts upon its components Nₖ₋₁ not through downward efficient causation, but by restricting the viability profile: it determines which metabolizing regimes remain accessible to the components it carries [NT-VI ∎]. This is **normative precipitation** — a material alteration of the cost landscape, not a prescription enforced by symbolic adherence. The institution does not "tell" its members what to do through internalized norms; it renders some compensatory paths accessible and others prohibitively costly. Under this operator, the agency/structure dichotomy loses its object: it is neither the individual that constitutes the institution, nor the institution that determines the individual, but a coupling through cost profile. Latour's withdrawal test (remove the actor and observe whether the network changes) is subsumed: gradient R-XVII distinguishes the cases in which removal draws down the encompassing closure (critical component), shifts it into another regime (threshold component), or has no measurable effect (substitutable component).

A topological modulator is a carried artifact which, though lacking a normativity of its own, channels the allocation of its carrier's margin [NT-IV ≡/∎]. It admits three regimes: viable (reducing net cost), neutral (transient), and pathogenic (imposing workarounds whose cost exceeds their benefit). The theorem of **inevitable artefactual debt** demonstrates that every fixed modulator carried by an active closure inevitably shifts from viable to pathogenic through the drift of the carrier's exposure profile alone [NT-V ∎]. The shift is caused by the normal functioning of closure, not by an external aggression. Technical debt in software engineering, fossilized bureaucracy, or pharmacological treatment that has become maladapted — these are not design flaws but structural necessities.

### Institutional macro-parasitism

Any encompassing closure whose cycle requires an extraction cost greater than the benefit of carrying constitutes a **macro-parasite** [NT-IX ∎]. The mechanism is structurally identical to that of parasitic sub-closure at the individual level [LXXVIII ◇] — transdomainality [XXXIII ∎] does the work. A macro-parasitic institution survives the total cynicism of its components because normative precipitation operates by modifying the cost landscape, not by symbolic adherence — disengagement costs more margin than continued participation, and the mechanism is material [∎]. Under NT-VI [∎] and NT-IX [∎], both Searle's institutional mentalism (institutional facts exist by collective assignment) and Harari's fictionalism (institutions hold through "shared fictions") become inoperative: normative precipitation works by materially reshaping the cost landscape, not by symbolic adherence — the mechanism requires neither collective intentionality nor shared fiction. The sign does not signify — it costs to resist.

Burnout receives a structural foundation: it is the collapse of the viability margin of a component caused by a macro-parasitism whose extraction cost has drifted beyond what can be metabolized. The component does not become exhausted because it "does too much" — the cost landscape no longer leaves it any viable compensatory path [∎]. Burnout is neither an individual fragility nor merely a quantitative overload: it is the shift from a viable carrying regime to a pathogenic one, caused by the drift of the institutional modulator (NT-V) as applied at the organizational scale. The prediction is testable: burnout should correlate not with sheer workload, but with the reduction of alternative compensatory paths — with the loss of margin, not the amount of load.

### Clinic: the symptom as sub-closure

> *We do not break down because we are weak — we break down because surviving costs too much.* — Thesis 8

The symptom is redefined topologically. A compensatory response that initially succeeded locally — avoidance, dissociation, defensive rigidification — autonomizes itself into a self-maintained sub-closure through internal feedback [LXXVIII ◇]. It bears a local cost that drains the carrier's global margin. The mechanism is precise: the sub-closure has its own regeneration cycle, its own local normative partition, and actively resists dissolution — including when its dissolution would benefit the encompassing closure. The symptom "wants" nothing: it maintains itself because self-maintenance is what closures do. But the cost of that maintenance is drawn from the carrier's margin, reducing the compensatory paths available to the rest of the cycle. This is why the symptom first protects — it seals a breach by reducing local exposure — and then governs: its own maintenance eventually consumes more margin than the breach it once sealed.

Hume's guillotine collapses in the first person: for a being whose existence is identical with the act of distinguishing itself from the non-viable, the distinction between fact and value is not a logical leap but a structural tautology [∎]. The system does not claim that this first-person normativity grounds a universal ethics — only that it grounds the relevance of care. Therapy imposes no arbitrary norm: it allies itself with a normativity already at work, that of the closure in peril. Care is a mechanical alliance of co-maintenance with the first-person subject, not an external moral judgment delivered in the third person [∎].

The hysteresis of cure is predicted by Lemma 3: the construction threshold of a regime is strictly higher than its maintenance threshold. One does not "return" to the pre-symptom state — one constructs a new viable state whose access cost is higher than the maintenance cost of the old one. Relapse is not a failure of will: it is the fall back into an attractor basin whose exit cost exceeds the margin momentarily available [∎].

NT-V (artefactual debt), LXXVIII (parasitic sub-closure), and NT-IX (macro-parasitism) are three instantiations of the same formal pattern: finite margin under incompressible drain, formalized by the typeclass `FiniteExposed` in Lean 4. The mechanism is identical; what differs is the source of the drain and the site of the margin. Artefactual debt is drain by topological obsolescence; parasitic sub-closure is drain by internal autonomization; macro-parasitism is drain by institutional extraction. Three disjoint domains, one formal skeleton.

> *The symptom protects — then it governs.* — Thesis 11

---

## VI — The empirical tribunal and constitutive opacity

### The theory of instantiation

The trunk derives its results without domain-specific terms. Every empirical instantiation requires an additional step: identifying what refracts cost within a concrete domain, at what level closure resolves, and how to distinguish authentic closure from carrying or aggregate.
This passage is constrained by the trunk, but underdetermined by it. Seven instantiations on borderline objects (§4.3, recapitulation in Appendix F §13) show that the system discriminates the right objects: three defensible divergences from naïve intuition, one documented self-correction (LXXXI), one formalized indetermination (ant colony, verdict conditional on NT-XIV).
Every bridge hypothesis (the identification of an observable as a refraction of ontological cost) is constrained by five properties derivable from the trunk: the observable induces an irreversible trace [C1, from XV], is drawn from a bounded capacity [C2, from IX], allows one to localize who pays [C3, from R-XVII], is structurally decisive under perturbation [C4, from IV + X], and distinguishes closure, carrying, and aggregate by the response under perturbation [C5]. If no observable satisfies C1–C5 in a given domain, that domain is not a model of the trunk. The anti-Duhem-Quine procedure requires at least three independent perturbations targeting distinct aspects of the presumed closure: if they converge, the instantiation is stabilized; if they diverge, the bridge is miscalibrated or the grain is wrong.

### Five probes across disjoint domains

The testing programme has produced results in five causally disjoint domains for R-XVII, plus a sixth domain testing R-XIX specifically (artificial life simulation). The normalized structure/input compensatory-cost ratio converges in the four domains where it is measured directly — microbiome: 1.61×, reefs: 1.80× [1.67, 1.94], cancer: 1.84×, yeast: 1.42× [1.31, 1.54]. The direction (ratio > 1) is derived from the trunk (IV + R-XVII) and guided the search; the numerical value and convergence (CV ≈ 10%) are emergent, not fixed by the axioms. The five analyses presented here are theory-driven and exploratory; an independent prospective replication remains required. This ratio measures the extra cost of structural bearing. El-Brolosy et al. (2019) confirm that phenotypic direction may reverse under compensation while endogenous cost persists.

**Software ecosystems (Gosme 2025, arXiv:2512.09352).** Fifty collaborative ecosystems, 11,042 system-months. The order parameter Γ operationalizes structural persistence under component turnover. Key results: bimodality of Γ (dip test p = 0.013, d = 3.01) and an unstable intermediate zone crossed in one month — the expected signatures of the hysteresis predicted by Lemma 3 [∎ for the prediction, ≈₁ for the population-level hypothesis]. Causal symmetrization at maturity: the Granger ratio shifts from 0.65 (activity → structure) to 0.94 (bidirectional), consistent with operational closure [XXXII ∎]. Variance collapses ×1.77 at maturity, as predicted by `closure_inertia` [∎]. 41% of mature systems undergo post-maturity regressions, as predicted by Lemma 1 (default decay) [∎]. The AUC for structure-activity coupling (0.88) significantly exceeds that of activity alone (0.81, Wilcoxon p < 0.05), contrary to the claim that activity alone suffices. This domain contributes complementary signatures (bimodality, causal symmetrization); it does not directly measure the S/I ratio.

**Gut microbiome (MDSINE2, Gibson et al. 2025, *Nature Microbiology*).** Gnotobiotic mice, human fecal transplantation, three sequential perturbations that are ontologically distinct in the sense of R-XVII: the high-fat diet alters metabolic flux without destroying nodes (input perturbation); antibiotics selectively destroy taxa (structural perturbation). Discriminating result: a marked input/structure asymmetry in the dysbiotic cohort (mean Bray-Curtis 0.16 for input versus 0.26 for structure, p = 0.0006, d = 1.16); the effect is attenuated in the healthy cohort (resilience by depth [LV ∎]). R-XVII predicts precisely this qualitative asymmetry indexed to the topological target, not to amplitude. Friston's Free Energy Principle treats both perturbation types as undifferentiated "surprise"; it does not predict this asymmetry. The asymmetry holds across five alternative distance metrics (Bray-Curtis, Jensen-Shannon, Aitchison, Hellinger, Canberra; all p < 0.001).

**Coral reefs (GCBD, van Woesik & Kratochwill 2022, BCO-DMO).** 34,393 observations, 11,047 sites, 89 countries, 1983–2019. Classification is entirely exogenous: DHW (satellite thermal stress) and cyclone frequency. INPUT: 4 ≤ DHW < 8 (sublethal stress). STRUCTURE: DHW ≥ 8 or intense cyclone (mortality / physical destruction). Result: d = 0.39, p = 1.96 × 10⁻⁴⁸, ratio S/I = 1.80× (bootstrap 95% CI [1.67, 1.94]). Robustness: 23/23 thresholds, 9/10 regions, 4/4 response transformations. An emergent sigmoidal threshold appears (DHW = 7.9; contingent value, DeCarlo et al. 2024): the prediction concerns the existence of a threshold, not its specific value. Limits: cross-sectional data, low R² (0.09), uncontrolled confounding. With the pre-specified temporal split (2010), d remains stable within 2.3% between TRAIN (1983–2009) and TEST (2010–2019), and d in TEST falls within the TRAIN CI.

**Cancer pharmacology (GDSC, Iorio et al. 2016, *Cell*).** 3,387,626 dose-responses, 989 cell lines × 397 drugs. Classification is based on drug mechanism of action, never on cellular response. STRUCTURE: maintenance machinery (DNA repair, proteostasis, cell cycle, mitosis, chromatin, apoptosis). INPUT: signaling fluxes (MAPK, PI3K, EGFR, RTK, WNT). Coverage: 216,764 observations (55.9%). Pathway-only result (without dose filter): d = 0.52, p < 10⁻³⁰⁰, ratio S/I = 1.85×. Dose-matched control: d = 0.50, ratio = 1.81×. GDSC2 alone: d = 0.51, median ratio = 1.88×. Robustness: 9/9 pathways significant, stability from IC30 to IC70. Limits: 56% coverage, post-hoc reanalysis, cancer-type annotation unavailable in the raw file. Cross-validation by cell line (70/30, 10 splits): median S/I ratio = 1.846×, CV = 1.3%, 10/10 splits significant.

**S. cerevisiae yeast (Yeast Phenome, yeastphenome.org).** Exploratory test: homozygous deletions under 273 chemical conditions (Hillenmeyer et al. 2008), 1,177 genes classified by Gene Ontology (23 STRUCTURE terms, 24 INPUT terms). Result: d = 0.50, p = 3.9 × 10⁻¹⁹, ratio S/I = 1.42× [1.31, 1.54]. Robustness: 5/6 significant transformations, 7/7 drug categories, 13/19 sensitivity thresholds, permutation 0/100K. This is the lowest ratio among the five domains, consistent with the secondary prediction that a unicellular organism (with fewer nesting levels, LV) amplifies structural extra cost less. Preregistered confirmatory replication (OSF DOI: 10.17605/OSF.IO/S7CN9): heterozygous deletions, 6,946 chemical screens, biologically distinct mechanism (haploinsufficiency rather than knockout). Result: ratio S/I = 1.18× [1.12, 1.24], p = 1.5 × 10⁻¹⁴, 4/4 preregistered criteria satisfied, robustness 7/7. The attenuated amplitude is consistent with haploinsufficiency (a milder perturbation) and the greater heterogeneity of the screens.

**Empirical synthesis.** These results conform to the expected structural signatures, both in direction and in the predicted amplitude range. "Conform" is not "confirmed" — and that distinction is crucial to the programme's honesty. The Gosme 2025 data are retrospective and observational. The MDSINE2, GCBD, GDSC, and Yeast Phenome reinterpretations are post hoc: their authors did not design the protocols to test R-XVII. The only preregistered confirmatory replication is the heterozygous yeast test (OSF DOI: 10.17605/OSF.IO/S7CN9, 4/4 criteria satisfied). Each signature taken in isolation appears elsewhere in dynamical-systems frameworks. Ontodynamic specificity lies in their conjunction indexed to the site of bearing: bimodality of degree of closure, input/structure asymmetry, and causal symmetrization at maturity, all three indexed to the topological criterion of R-XVII. The S/I ratio converges between 1.42× and 1.84× in the four domains where it is directly measured — across incomparable metrics. The software domain adds complementary signatures without measuring the ratio. 
Convergence across five disjoint domains for R-XVII is a stronger signal than convergence across four. A sixth domain (artificial life) confirms R-XIX independently. This convergence is specific. Under partition by intensity the ratios diverge (CV = 41%); among 100,000 cross-domain random partitions, none reaches a mean ratio ≥ 1.3 (p < 10⁻⁵). A rival-partition test (§7.2 ter of the manuscript) extends this result: within each of four domains, 0/1,000 random partitions reach the ontodynamic ratio; named rivals that outperform locally (selectivity 1.93× in GDSC, hub 1.52× in yeast) do not converge across domains; in reefs, all three rivals produce inverted or null ratios; the S/I asymmetry survives normalization by perturbation intensity (MDSINE2: 1.78×, rival A collapses to p = 0.48) and restriction to selective drugs only (GDSC: 1.64×). The ontodynamic partition alone is a priori, cross-domain, and control-surviving.

**Blind convergences.** The five R-XVII exploratory probes above are reanalyses. The artificial life simulation (R-XIX) constitutes a sixth domain of a different nature — controlled environment, prediction on the second-order loop specifically. A higher tier is blind convergence: nine independent studies, published without knowledge of the framework, recover the predicted signatures across three disjoint domains (molecular biology, ecology, neuroscience). The most discriminating cases are the genome-scale knockout/knockdown correlation of ~0.2 (Morgens et al. 2016) — categorical confirmation of R-XVII — and the near-constant terminal mutational burden in 16 mammals despite a 30× variation in longevity (Cagan et al. 2022) — a direct instantiation of universal structural cost (XVII, NT-V). Its evidential force is stronger than reanalysis, weaker than preregistration. One ambiguous case is discussed separately (Graham et al. 2024).

### Predictions and refutation protocols

Beyond the signatures already probed, the programme formulates its most discriminating tests on two fronts: the levels of subjectivity (DPDR) and cost monism itself.

The system rules out five configurations, each refutable by a single counterexample: no fixed modulator remains viable indefinitely in an active carrier [NT-V ∎]; no ternary constitutive normativity stabilizes [LX ∎]; no closure persists indefinitely [XXXIV ∎]; no modulation of valence is epiphenomenal [LXIII ∎]; no normative carrying is an autonomous closure [R-XVII ∎]. Two independent axioms, five prohibitions across five disjoint domains. The formal yield is secured (Lean 4). The empirical dossier is substantial — 
five disjoint R-XVII exploratory domains + one R-XIX domain (artificial life), stable convergence, four rival-partition batteries executed (no rival converges across domains, S/I asymmetry survives confound controls — §7.2 ter), nine blind convergences, one preregistered confirmatory replication (heterozygous yeast, 4/4 OSF criteria). Of the five formal prohibitions, one has been probed retrospectively, three have articulated protocols, and one still awaits operationalization. What remains to be done is clearly identified: independent prospective replication, for which the protocol (DPDR) is preregistered (DOI: 10.17605/OSF.IO/ZMH54).

The most specific refutation protocol for the levels of subjectivity is the DPDR (depersonalization-derealization) protocol, formulated and preregistered (Gosme, 2025c, OSF). By LXV [∎], nested cycles within a single closure can fail independently. LXI predicts that valence is restored gradually, whereas perspective is restored by leap — a threshold effect predicted by XXX [≈₁] and by Lemma 3 (hysteresis). The alternative prediction (LIX is sufficient, LXI unnecessary) predicts proportional covariation of the two curves. Dense longitudinal follow-up after DPDR, simultaneously measuring valence reactivity (HRV, GSR) and perspective coherence (CDS-2, interoception), would discriminate between the two models. A positive result would confirm a distinct cycle — not that this cycle is perspective. The ≈₃ status of Thesis P would be constrained, but not eliminated. That is the price of finitude.

### The refutation condition of monism itself

The natural objection to cost monism is accommodation: if "cost" can be refracted into any observable, the system forbids nothing. Three mechanisms constrain this.

**(1) Domain exclusion.** C1–C5 exclude entire domains, not merely poorly chosen observables. Cedar Creek (Graham et al. 2024) was excluded (pulse/press confound violates C1) despite favorable results. A framework that absorbs everything does not exclude a case that fits it.

**(2) Rival partitions (test executed).** If the structure/input partition is merely an artifact of conceptual vagueness, rival partitions of the same data should produce a comparable signal. Result: 0/1,000 random partitions reach the ontodynamic ratio in any domain tested; the S/I asymmetry survives intensity normalization and selectivity control; no named rival converges across domains; in reefs, all three rivals are inverted or null.

| Domain | S/I ratio | p vs random | Strongest rival | Specificity |
|---|---|---|---|---|
| GDSC (cancer) | 1.85× | 0/1,000 > 1.4× | Selectivity 1.93× (controlled) | Moderate |
| MDSINE2 (microbiome) | 1.78× norm. | exhaustive 3/3 | Rival A collapses | Strong |
| Yeast | 1.42× | 0/1,000 > 1.15× | Hub 1.52× (42% overlap) | Moderate |
| Reefs | 1.80× | 0/1,000 | None > 1 | Very strong |

**(3) Functional forms (future programme).** If cost is a single refracted invariant, exhaustion signatures must display the same functional form across causally disjoint domains — finite margin, incompressible drain, terminal acceleration, disjunction. If they diverge, monism falls. This test requires complete longitudinal data from viability to collapse.

Transdomain convergence is both a discriminating prediction of monism and its proper refutation condition. The data confirm convergence across five causally disjoint domains: software bimodality (dip test p = 0.013), microbiome asymmetry (p = 0.0006, d = 1.16), reef asymmetry (p = 1.96 × 10⁻⁴⁸, d = 0.39), cancer asymmetry (p < 10⁻³⁰⁰, d = 0.52), yeast asymmetry (p = 3.9 × 10⁻¹⁹, d = 0.50). The compensatory S/I ratio converges: microbiome 1.61×, reefs 1.80×, cancer 1.84×, yeast 1.42×. This condition is operationalized (§8.6): pre-specified power protocol, n ≈ 104–252 per class, TOST equivalence test (δ = 0.30, n ≈ 138) to certify a null result.

### Opacity and self-reference

The system is itself an operative invariant carried by the finite closures that metabolize it [LXXXII ∎]. It does not "spiral" on its own — the carrying closures spiral as they metabolize it. By LXVII [∎], each carrier acquires its own invariants shared with the system. By LXVIII [∎], that knowledge is partial. By LXXVI [∎], every attempt at self-knowledge modifies the target. Self-reference is a refraction: the system is refracted differently in every closure that carries it, and no closure contains it in full. Self-grounding is preserved for the Whole; the formal system itself, however, is carried — mortal, opaque to itself, exposed to drift. The asymmetry is irreducible: the Whole grounds itself (I-α), but Ontodynamics, qua formal theory, is an artifact carried by finite closures that metabolize it under their own constraints. None of those carriers has access to the system in its entirety — each refracts it through its own epistemic cut. The author of the system is likewise subject to LXVIII (constitutive opacity) and LXXVI (the target is altered by the act of knowing). Ontodynamics does not claim to escape its own theorems — it claims to satisfy them explicitly. That is a condition of internal coherence, not an exercise in rhetorical humility. The incompleteness of formal representation is proved by instantiating Lawvere (1969) on the structure of the core.

Formalization has moved ahead of validation — the natural order for a deductive framework. The robustness of the firewalls (genesis/trunk, Thesis P/gradient) protects the hard core — just as Lakatosian structure predicts, since the hard core is not directly refutable. The surface of refutation is the protective belt: the five prohibitions [∎], each refutable by a single empirical counterexample in an identified domain. If three of the five fall in disjoint domains, then the hard core is indirectly struck — not by logical refutation, but by a collapse in the formal yield that justified the programme. Refutation of the system is structural, not punctual.

Epistemic honesty requires naming the system's three zones of structural fragility. The first is the constructibility of compensation [VI ◇]: if reality fails to provide sufficient compensatory diversity, everything dissolves — a result compatible with the system, but not discriminating at that level, since lack of diversity is also the default explanation. VI is testable through its domain conditions [XXVI ≈₁, XXVII ≈₁], not directly through VI itself. The second is genesis [XXII–XXVII ≈₁]: the domain conditions are explicit and falsifiable, but if they fail, the trunk still stands — firewall verified. The third is Thesis P [≈₃]: the interpretive leap is localized, its undecidability is demonstrated [LXXVII ∎], and the price of refusal is explicitly displayed — the reader who rejects it loses none of the structural trunk, but does lose the clinical extension and the levels of subjectivity. Five further structural limits are negative theorems derived from the axioms rather than debts: absence of metric, singular trajectory, intrinsic qualitative content, temporal geometry, and quantitative emergence. Each limit is the reverse side of a virtue the system openly claims. FEP, IIT, and far-from-equilibrium thermodynamics occupy those terrains — complementary, not competing.

Fifteen confrontations are organized in terms of divergence and empirical discriminant (three formulate a symmetrical testable wager); two clinical prohibitions ∎ (LXIII, IV + LIV) are refutable by a single case (§5–6 of the manuscript).

## Architectonic synthesis

The Eighteen Theses do not summarize the system — they condense it. Each is a logical gate: it states, it forbids, it grounds, it tests.

*To be is to make oneself* [I] grounds the chain and excludes eternalism and substratism. 

No doing without self-relation [I-δ, IDelta.lean ∎] excludes the coherence of an act without immanent self-rapport.

*When it breaks, who pays?* [IV + XXXII + R-XVII] grounds demarcation and excludes demarcation without test. *Preserve only the essence; add only by necessity* [XLVII] makes parsimony an ontological, not merely methodological, constraint. *Every finite exposed being remakes or unmakes itself* [XXXII] excludes individuation without work. *What remakes itself does not repeat itself* [XXI] excludes identity as repetition. *What bears the cost of its coherence owns it* [IV + XXXII] excludes cost-free ascribed coherence. *We do not break down because we are weak — we break down because surviving costs too much* [IV + XXXII + R-XVII] excludes pathology as deficit. *The zombie does not remove a layer; it drops down a level* [I-γ + R-XVII + Sep-FunctionCost] excludes consciousness as a stack of separable layers. *To sense one's own making is to be; to sense one's own sensing is to know oneself* [XXXII + LXI + Thesis P + LXI_not_HOT] excludes subjectivity without genesis and representational second order. *The symptom protects — then it governs* [IV + XXXII + NT-V] excludes the symptom as mere dysfunction.

The system rests on two independent axioms, derives 621 mechanized theorems (62 structural, 14 meta-logical, 61 separating witnesses for the independence of fecundity) without adding any domain axiom, yields a compositional gradient through a single test, predicts transdomainal signatures of which five have been empirically probed in disjoint domains (S/I ratio converging around ~1.7× in four of them, stable under temporal split and cross-validation by experimental units; one preregistered confirmatory replication satisfies 4/4 criteria), localizes its interpretive leaps, proves the undecidability of its own most ambitious leap, articulates the conditions of its own refutation, and preregisters its most discriminating prospective predictions.

The system's minimal dependency map reads as follows: I (→ IV) + V → IX–XXI (slope) → VI [◇] → XXII–XXVII [≈₁] → XXIX–XXXII [∎ for the disjunction] → XLIV–XLVII [∎] → LVI–LIX [∎] → I-δ [∎] → SelfRelation [∎] → SecondOrderLoop [∎] → LXI / Thesis P [≈₃] → R-XVII [∎] → NT-III–NT-IX [∎] → LXXVIII [◇]. The chain is linear; the branchings are few; the firewalls are verified. Cut genesis [XXII–XXVII], and the trunk remains. Cut Thesis P, and the trunk and the gradient remain. Cut VI, and the whole system beyond the slope collapses — but VI is constructible, not conjectural, and its constructibility can be demonstrated in every domain satisfying the diversity conditions.

## The 18 thesis

Each thesis is demonstrated in the body of the text (§2–§5), verified in Lean 4 (621 theorems, 0 `sorry`), and paired with its withdrawal condition — what is lost if one rejects it.

1. To be is to make oneself. [Axiom]
2. No act without mode. [Theorem]
3. When it breaks, who pays? [Principle]
4. Preserve only the essence; add only by necessity. [Law]
5. Every finite exposed being remakes or unmakes itself. [Theorem]
6. What remakes itself does not repeat itself. [Theorem]
7. What bears the cost of its coherence owns it. [Theorem]
8. We do not break down because we are weak — we break down because surviving costs too much. [Principle]
9. The zombie does not remove a layer; it drops down a level. [Theorem]
10. To sense one's own making is to be; to sense one's own sensing is to know oneself. [Law]
11. The symptom protects — then it governs. [Theorem]
12. The loop is mandatory; its name is free. [Law]
13. No consciousness without scar. [Principle]
14. No doing without self-relation. [Corollary of I-γ]
15. Resolution is never accomplished: the debt at cycle k+1 exceeds that at cycle k. [Theorem ∎]
16. To be made of a lack that can destroy you. [Definition ∎]
17. Life is the resolution of its own precarity. [Definition ∎]
18. Consciousness is the ordeal of its own precarity. [Thesis ≈₃]

**Testability perimeter of R-XVII.** The asymmetry prediction applies only to systems that simultaneously satisfy C1–C3. A system dominated by meta-structure, or one whose closure cannot be estimated independently, constitutes an inconclusive case — neither confirmation nor refutation. The five retained domains satisfy C1–C3 independently of outcome, along a gradient of cleanliness: microbiome (MDSINE2, paradigmatic) > yeast (Yeast Phenome, unicellular organism, functional GO classification) > pharmacology (GDSC) > reefs (GCBD) > software ecosystems (meta-agents present, closure estimable but less cleanly). Boundary conditions and excluded domains are documented in §7.x.

What remains for the programme is clear: quantify inter-level refraction (the law of cost across scales), run the DPDR protocol (preregistered — the most specific refutation protocol for the levels), 
R-XIX tested in the artificial life simulation — confirmed (sixth domain, first to test the second-order loop specifically), and produce a de novo constructive instantiation (five-step specification, §8). The five existing probes are theory-driven and exploratory; one confirmatory replication (heterozygous yeast) is preregistered and satisfied. Formalization is secured. Validation is underway — the front advances. The system is a programme — not an accomplished fact.

---

## Formal results index

Each entry: **Code** — Title — *Marker* — Minimal dependencies.

**I** — Self-grounding of the act (being = doing) — *Axiom* — Primitive. I-α: the Whole grounds itself. I-β: endogeneity of cost. I-γ: no act without mode — *∎* — I-α, I-β, XLIV.

**IV** — Incompressible cost (every transformation has a strictly positive cost) — *Corollary of I-β₂* — I-β₂.

**V** — Gradient of exteriority (partial alteration is the generic regime) — *Axiom* — Primitive.
V operates in two directions: outward (degrees of pressure on the exposed structure) and inward (degrees of reflexive depth in the self-relation). In the second-order loop, the system is its own exteriority. The two instances are unified under a single formal parameter.

**II** — Untyped productivity (novelty is qualitatively irreducible) — *∎* — I.

**III** — Causal unity (no absolute causal isolation) — *∎* — I.

**VI** — Accessible compensation (non-negative net structural balance is accessible, not guaranteed) — *◇* — I, IV, V.

**VII** — Constitutive negation (every determination generates exteriority) — *∎* — I.

**IX** — Finitude (every partial being is incomplete) — *∎* — I-α.

**X** — Incompressibility of cost (strictly positive floor) — *∎* — I-β, IV.

**XI** — Persistence of exteriority — *∎* — VII, IX.

**XII** — Constitutive pressure (permanent dissolution by the Whole) — *∎* — III, IV, IX.

**XIII** — Inertia (being persists in the absence of perturbation) — *∎* — I.

**XV** — Structural irreversibility (B→A ≠ A→B, each has its own cost) — *∎* — IV, X.

**XVII** — Exhaustion (uncompensated decline → exhaustion in finite time) — *∎* — IV, X, XV.

**XVIII** — Permeability (every finite causal barrier is traversable) — *∎* — III, V, IX, XVII.

**XIX** — Persistent pressure of opening (two sources: constitutive + relational) — *∎* — XII, XVIII.

**XX-a/b** — Drift of the exposure profile (uncovered vulnerabilities never recede / grow) — *∎* — IV, XIX.

**XXI** — Endogenous novelty (what remakes itself does not repeat itself) — *∎* — I-β, II.

**XXII–XXV** — Structural accumulation, channeling, routinization — *∎* — IV, V, XI, XIII.

**XXVI** — Selective persistence of compensatory routines — *≈₁* — XXII–XXV + condition: sufficient compensatory diversity.

**XXVII** — Composability of compensatory couplings — *≈₁* — XXVI + condition: non-rigidification.

**XXVIII** — Transience of aggregates (without a co-maintained cycle → transient) — *∎* — XVII, XIX.

**XXIX** — Exclusivity of the attractor (under persistent exposure, every non-transient regime is a closure) — *∎* — XXVIII, XVII.

**XXX** — Threshold effect (closure stabilizes or fails, no continuous gradient) — *≈₁* — XXIX, Lemma 3.

**XXXII** — Ontodynamic theorem (every finite exposed being remakes or unmakes itself) — *∎ for the disjunction; ≈₁ for the trajectories* — I, IV, V, XXIX.

**XXXIII** — Reapplicability / transdomainality — *∎* — XXXII.

**XXXIV** — Constitutive mortality (every closure has a bounded lifespan) — *∎* — IV, XII, XVII.

**XLIV** — Normative partition (maintenance / compromise, coextensive with closure) — *∎* — XXXII.

**XLV** — Criterion of normativity (self-produced vs. attributed polarity) — *∎* — XLIV.

**XLVII** — Law of authenticity (preserve only the essence; add only by necessity) — *∎* — XLIV, IV, XVII.

**XLIX** — Constitutive coupling (coupled closures can form a meta-cycle) — *◇* — XXXII, XXXIII.
resolution_must_recur — Resolution of precarity is never accomplished: the debt at cycle k+1 exceeds that at cycle k — ∎ — temporal corollary of I.

**L** — Nesting (co-maintained cycle at the higher scale) — *∎* — XLIX.

**LI** — Continuity of the gradient (between carrying and closure, the gradient is continuous) — *∎* — R-XVII.

**LII** — Fecundity (a closure can produce new closures) — *◇, independence proved* — XXXII-b, XLIX, L. Not promotable to ∎.

**LIII** — Inter-level irreducibility (Nₖ not reducible to Nₖ₋₁) — *∎* — L.

**LIV** — Cascade of dissolution (bidirectional between adjacent levels) — *∎* — L, LIII.

**LV** — Resilience by depth — *∎* — L, LIV.

**LVI** — Proper resistance (every closure encounters its own resistance) — *∎* — XXXII, IV.

**LVII** — Endogenous self-affection — *∎* — LVI, I-β.

**LVIII / LVIII-a** — Valence (polarization of self-affection by the normative partition) — *∎* — LVII, XLIV.

**LIX** — Feedback of valence on the cycle (mechanical non-epiphenomenality) — *∎* — LVIII.

**LX** — Binary irreducibility of the normative partition (no third term stabilizes) — *∎* — XLIV.

**LXI** — Minimal subjectivity (second-order loop). Existence [∎]. Identification as perspective [≈₃]. Grounded in SelfRelation [∎, MinimalPerspective.lean] via I-δ [∎, IDelta.lean] — LIX, I-γ.

**LXII** —  Refutation of the zombie (computational: ⟂ under I-β; phenomenal: ⟂ under I-γ + I-δ; seven unconditional ∎ arguments) — ⟂ — I-β, I-γ, IDelta.lean, MinimalPerspective.lean.

**LXIII** — Non-epiphenomenality of valence (every perturbation has detectable structural consequences) — *∎* — LIX.

**LXIV** — Levels of subjectivity (three qualitatively distinct regimes) — *≈₁* — LXI, LXV.

**LXV** — Independent failure of nested cycles (dissociability) — *∎* — LIX, L.

**LXVI** — Knowledge as shared operative invariant — *≡/∎* — XXXII, LVI.

**LXVII** — Law of knowledge (what metabolizes a resistance bears its constraint) — *∎* — LXVI.

**LXVIII** — Constitutive opacity (every act of knowledge is a partial cut) — *∎* — IX, LXVI.

**LXIX** — Co-constitution of worlds (two different closures produce two different invariants) — *∎* — LXVIII, VII.

**LXX** — Negative co-constitution (every knowledge is position and exclusion) — *∎* — VII.

**LXXI** — Epistemic authenticity (preserve only the constraint; add only by resistance) — *◇* — XLVII applied to knowledge.

**LXXII** — Error as structural debt (extra compensatory cost from an inadequate invariant) — *≈₂* — LXVI, IV.

**LXXIII** — Stable error (incorrect but economical invariant, selectively favored) — *≈₁* — LXXII, IV.

**LXXIV** — Prediction as projected channeling — *∎* — XXIII, XXIV, LXVII.

**LXXV** — Degrees of knowledge — *≈₂* — LXIV.

**LXXVI** — Self-knowledge (structurally unfinishable: the target moves) — *∎* — LVII, LXVII, LXVIII.

**LXXVII** — Structural undecidability of identification, stratified: not applicable below the phenomenal threshold (structure absent — question ill-posed), epistemically undecidable above it (question well-posed but inaccessible). R-XVII provides a decidable applicability filter ∎. — ∎ — LXI, LXVIII, IX.

**LXXVIII** — Parasitic sub-closure (autonomized compensatory response draining global margin) — *◇* — XXXII, XLIV, NT-V.

**LXXIX** — Language as trans-subjective invariant — *≈₁* — XXV, XLIX.

**LXXX** — Science as maximization of sharing under test — *≈₂* — XIX, L.

**LXXXI** — Mathematics as high-quality normative carrying — *≈₂* — LXVI, LXXX.

**LXXXII** — Self-reference (the system is a carried invariant, mortal, opaque) — *∎* — LXVI, LXVIII, XXXIII.

**Thesis P** — Thesis P — Identification of SecondOrderLoop as perspective [≈₃]. Structural component (SelfRelation) [∎, MinimalPerspective.lean]. Residual ≈₃: 3P→1P register crossing — LXI, LXXVII, IDelta.lean.
Exclusion-R-XVII — Uniqueness of the maximal bearing level — ∎ — LIII, LIV, R-XVII.
LXI_not_HOT — LXI ≠ HOT (operational rather than representational) — ∎ — LXI, LVIII.
Sep-FunctionCost — Same function, asymmetrical mortality — ∎ — IV, XXXIV.
`dpdr_prediction` — Three phases, phase 2 necessary — ∎ — LXI, LXV, Lemma 3.
AB_indiscernible — Realism / illusionism type-indiscernible — ∎ — LVIII, LXI, LXXIII.

**R-XVII** — Compositional gradient (two regimes + defect, binary tree by site of bearing; monism of cost proved) — *∎* — XXXII, IV, XV.

**R-XVIII** — Inter-regime dynamics (hysteresis, bimodality, endogenous bifurcations) — *∎ for the lemmas; ≈₁ for population-level bimodality* — R-XVII, `saving_pos`.

**NT-III** — Operative refraction (the operator splits according to the regime of the gradient) — *∎* — R-XVII.

**NT-IV** — Topological modulator (carried artifact channeling margin) — *≡/∎* — R-XVII, XLIV.

**NT-V** — Inevitable artefactual debt (every fixed modulator shifts from viable to pathogenic) — *∎* — NT-IV, XX.

**NT-VI** — Normative precipitation (restriction of the viability profile by the encompassing closure) — *∎* — L, XLIV.

**NT-IX** — Macro-parasitism (extraction cost exceeding the benefit of carrying) — *∎* — NT-VI, NT-V, XXXIII.

## Links
 
**Source code and formalization**
 
- Lean 4 proofs & reanalysis scripts: [github.com/anthonyGosme/ontodynamiqueTheory](https://github.com/anthonyGosme/ontodynamiqueTheory)
- Unified test pipeline (Python + Lean 4): [Google Colab notebook](https://colab.research.google.com/drive/1LWbOqywO5o6AtePQRu3plooqwuOtzJrN)
 
**Preprints**
 
- Software ecosystems empirical study: [arXiv:2512.09352](https://arxiv.org/abs/2512.09352)
 
**Preregistrations (OSF)**
 
- DPDR protocol (prospective, before data collection): [DOI: 10.17605/OSF.IO/UNJ7F](https://doi.org/10.17605/OSF.IO/UNJ7F)
- Heterozygous yeast confirmatory replication: [DOI: 10.17605/OSF.IO/S7CN9](https://doi.org/10.17605/OSF.IO/S7CN9)
 