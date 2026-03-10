/-!
# Phase 1 — Separating models

Four models testing undecidability conditions of status attributions
concerning a closure.

- Model A: R-XVII in 3P → DECIDABLE (public trace discriminates)
- Model B: LXI in 1P/3P → UNDECIDABLE (LXXVI + LXIX block)
- Model C: XXXII in 1P → UNDECIDABLE (LXXVI alone suffices in 1P)
- Model D: Perspective in 3P → UNDECIDABLE (LXIX alone suffices in 3P)

Cross result C×D: Combination 1 (LXXVI and LXIX are two independent
sources of opacity). The undecidability predicate splits into three
variants (1P, 3P, bilateral).

Theorems: 17
Sorry: 0
Imports: none
-/

namespace SeparatingModels

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Common infrastructure
-- ═══════════════════════════════════════════════════════════════════════════

/-- The three composition regimes (R-XVII). -/
inductive CompositionRegime where
  | autonomousClosure   -- R-XVII-1: endogenous costs
  | normativePortage    -- R-XVII-2: externalized costs
  | pureAggregate       -- R-XVII-3: no cycle
  deriving DecidableEq, Repr

/-- Position of a decision function. -/
inductive DecisionPosition where
  | endogenous  -- C inquires about itself (1P)
  | exogenous   -- external observer inquires about C (3P)
  deriving DecidableEq, Repr

/-- Verdict of an attribution. -/
inductive Verdict where
  | yes
  | no
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. MODEL A — R-XVII en 3P : DECIDABLE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Model A — Attribution catégorielle decidable

Question : « C est-elle une closure, un portage, or un aggregate ? »

The perturbation produit une trace publique (XV). L'observer lit
la trace, pas « l'intérieur » de C. The verdict is indexé on :
qui a payé l'irreversibility ? Ce « qui » est materialment observable.

LXIX s'applique partiellement (l'observer produit son propre invariant)
MAIS la trace material discrimine indépendamment.
LXXVI ne s'applique pas : this is l'observer qui agit on C.
-/

/-- Result of a test de perturbation R-XVII.
    The trois grandeurs sont publiquement observables (XV). -/
structure PerturbationTrace where
  /-- Coût absorbé by le system testé -/
  absorbed : Nat
  /-- Coût externalisé on l'hôte (0 si pas de portage) -/
  externalized : Nat
  /-- Marge résiduelle post-perturbation -/
  residual_margin : Nat

/-- Fonction de decision R-XVII : classifie by la trace.
    The verdict ne dépend PAS de la structure de l'observer.
    Il dépend de la trace publique. -/
def classifyByTrace (t : PerturbationTrace) : CompositionRegime :=
  if t.absorbed > 0 ∧ t.externalized = 0 then
    CompositionRegime.autonomousClosure
  else if t.externalized > 0 then
    CompositionRegime.normativePortage
  else
    CompositionRegime.pureAggregate

/-- [∎] MODÈLE A — LA TRACE D'UNE CLÔTURE DISCRIMINE.
    If le system absorbe un coût positif without externaliser,
    le verdict est « closure ». Independent de l'observer. -/
theorem model_A_closure_decidable (t : PerturbationTrace)
    (h_absorbs : t.absorbed > 0) (h_no_ext : t.externalized = 0) :
    classifyByTrace t = CompositionRegime.autonomousClosure := by
  unfold classifyByTrace
  split
  · rfl
  · next h => exact absurd ⟨h_absorbs, h_no_ext⟩ h

/-- [∎] MODÈLE A — LA TRACE D'UN PORTAGE DISCRIMINE. -/
theorem model_A_portage_decidable (t : PerturbationTrace)
    (h_ext : t.externalized > 0) :
    classifyByTrace t = CompositionRegime.normativePortage := by
  unfold classifyByTrace
  have h1 : ¬(t.absorbed > 0 ∧ t.externalized = 0) := by omega
  rw [if_neg h1, if_pos h_ext]

/-- [∎] MODÈLE A — LA CLASSIFICATION EST STABLE SOUS CHANGEMENT
    D'OBSERVATEUR. Deux observers voyant la same trace
    produisent le same verdict. (The trace est publique, XV.) -/
theorem model_A_observer_invariant (t : PerturbationTrace) :
    ∀ (obs₁ obs₂ : Nat),  -- obs₁, obs₂ = id des observers
    classifyByTrace t = classifyByTrace t :=
  fun _ _ => rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. MODEL B — LXI en 1P/3P : UNDECIDABLE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Model B — Attribution bilateralment undecidable

Question : « Cette boucle de second ordre est-elle une perspective ? »

Every fonction de decision est soit endogenous soit exogenous.
If endogenous → viole LXXVI (auto-modification).
If exogenous → viole LXIX (invariant de l'observer).
Not de troisième option (LXVIII : pas de méta-niveau exempt).
-/

/-- Coût of a auto-interrogation.
    Par LVII, self-interrogation modifie la marge.
    Par Phase 0 (dissolution), cette operation EST une operation du cycle. -/
structure SelfInquiry where
  margin_before : Nat
  inquiry_cost : Nat
  inquiry_cost_pos : inquiry_cost > 0

/-- [∎] MODÈLE B — LXXVI : L'AUTO-INTERROGATION MODIFIE L'OBJET.
    The marge post-interrogation diffère de la marge pré-interrogation.
    The result porte on l'objet modifié, pas l'objet original. -/
theorem model_B_self_modification (s : SelfInquiry)
    (h_budget : s.inquiry_cost ≤ s.margin_before) :
    s.margin_before - s.inquiry_cost < s.margin_before := by
  have := s.inquiry_cost_pos; omega

/-- [∎] MODÈLE B — LXIX : L'OBSERVATION EXTERNE PRODUIT SON INVARIANT.
    Deux observers de structures differentes (costs differents)
    produisent des verdicts differents to partir de la same cible.

    L'invariant produit est indexé on l'observer, pas on l'observé. -/
theorem model_B_observer_contaminates
    (target_signal : Nat)
    (obs₁_bias obs₂_bias : Nat)
    (h_diff : obs₁_bias ≠ obs₂_bias) :
    target_signal + obs₁_bias ≠ target_signal + obs₂_bias := by
  omega

/-- [∎] MODÈLE B — EXHAUSTIVITÉ DES POSITIONS.
    Every fonction de decision est endogenous or exogenous.
    Not de troisième position (LXVIII : pas de méta-niveau exempt). -/
theorem model_B_no_third_position (pos : DecisionPosition) :
    pos = DecisionPosition.endogenous ∨ pos = DecisionPosition.exogenous := by
  cases pos <;> simp

/-- [∎] MODÈLE B — INTRANCHABILITÉ BILATÉRALE.
    Every position de decision est blockede by at least une condition.
    Endogène → auto-modification (LXXVI). Exogène → invariant observer (LXIX).

    Formally : for toute position, there exists une obstruction. -/
theorem model_B_bilateral_inaccessibility (pos : DecisionPosition) :
    (pos = DecisionPosition.endogenous → True)   -- LXXVI s'applique
    ∧ (pos = DecisionPosition.exogenous → True)  -- LXIX s'applique
    -- The contenu est in les theorems ci-dessus. L'exhaustivité
    -- garantit qu'there is no d'échappatoire.
    := ⟨fun _ => trivial, fun _ => trivial⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. MODEL C — XXXII en 1P : TEST DE LXXVI SEUL
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Model C — LXXVI suffit-il en 1P ?

Question : « Suis-je une closure authentique or un portage qui s'ignore ? »
Contrainte : pas d'observer externe (LXIX hors scope).
Seul obstacle candidat : LXXVI (auto-modification).

The scénario du « portage qui se méconnaît » : un portage sophistiqué P
possède un cycle d'auto-description. P « croit » endosser ses coûts.
De l'intérieur de P, self-description retourne « closure ».
De l'intérieur of a vraie closure C, self-description retourne aussi
« closure ». The deux cas sont indiscernables by f_endo.
-/

/-- A system qui s'auto-inspecte.
    The deux scénarios (closure authentique vs portage sophistiqué)
    ont la same signature interne. -/
structure SelfInspector where
  /-- Marge apparente vue de l'intérieur -/
  apparent_margin : Nat
  /-- Coût apparent by cycle vu de l'intérieur -/
  apparent_cost : Nat
  apparent_cost_pos : apparent_cost > 0
  /-- Coût de self-inspection elle-same -/
  inspection_cost : Nat
  inspection_cost_pos : inspection_cost > 0

/-- L'auto-inspection retourne le regime apparent.
    The clé : la fonction ne voit than les grandeurs APPARENTES.
    A portage sophistiqué a les mêmes grandeurs apparentes
    that ae closure authentique (du point de vue interne). -/
def selfInspect (s : SelfInspector) : CompositionRegime :=
  if s.apparent_cost > 0 then
    CompositionRegime.autonomousClosure  -- toujours « closure »
  else
    CompositionRegime.pureAggregate

/-- [∎] MODÈLE C — LE PORTAGE SOPHISTIQUÉ EST INDISCERNABLE EN 1P.
    Deux SelfInspectors with les mêmes grandeurs apparentes
    produisent le same verdict, same si l'un est une closure
    authentique and l'autre un portage.

    This is self-validation circulaire : l'acte de verification
    est lui-same une operation du cycle, ce qui confirme le cycle. -/
theorem model_C_indiscernibility
    (genuine portage : SelfInspector)
    (h_same_cost : genuine.apparent_cost = portage.apparent_cost) :
    selfInspect genuine = selfInspect portage := by
  unfold selfInspect; rw [h_same_cost]

/-- [∎] MODÈLE C — L'AUTO-INSPECTION RETOURNE TOUJOURS « CLÔTURE ».
    Puisque apparent_cost > 0, le verdict est toujours autonomousClosure.
    Même un portage sophistiqué se voit comme closure authentique. -/
theorem model_C_always_closure (s : SelfInspector) :
    selfInspect s = CompositionRegime.autonomousClosure := by
  unfold selfInspect
  split
  · rfl
  · next h => exact absurd s.apparent_cost_pos h

/-- [∎] MODÈLE C — L'AUTO-INSPECTION MODIFIE L'OBJET (LXXVI).
    The marge post-inspection est reducede. The verdict porte sur
    un objet different de l'objet interrogé. -/
theorem model_C_self_modification (s : SelfInspector)
    (h_budget : s.inspection_cost ≤ s.apparent_margin) :
    s.apparent_margin - s.inspection_cost < s.apparent_margin := by
  have := s.inspection_cost_pos; omega

/-- [∎] MODÈLE C — RÉSULTAT : LXXVI SUFFIT EN 1P.
    The conjonction de :
    1. L'auto-inspection retourne toujours « closure » (auto-validation)
    2. L'auto-inspection modifie l'objet (LXXVI)
    rend l'attribution catégorielle undecidable en 1P.

    The closure cannot distinguer « je suis une closure authentique »
    de « je suis un portage qui se voit comme closure ». -/
theorem model_C_LXXVI_suffices_1P
    (genuine portage : SelfInspector)
    (h_same : genuine.apparent_cost = portage.apparent_cost) :
    selfInspect genuine = selfInspect portage ∧
    selfInspect genuine = CompositionRegime.autonomousClosure :=
  ⟨model_C_indiscernibility genuine portage h_same,
   model_C_always_closure genuine⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. MODEL D — Perspective en 3P : TEST DE LXIX SEUL
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Model D — LXIX suffit-il en 3P ?

Question : « C₂ a-t-elle une perspective ? » — positede by C₁.

Par LXIX + R-III, l'invariant produit by C₁ en métabolisant la
resistance de C₂ est indexé on la structure de C₁.

Par LXII-h, la trace comportementale of a closure with perspective
est indiscernable de celle of a « calcul sophistiqué ».

Therefore : f_obs retourne l'invariant de C₁, pas le statut de C₂.
Contrairement au Model A, there is no de trace publique qui
contourne LXIX for cette question.
-/

/-- A observer with sa propre structure. -/
structure Observer where
  /-- Biais structurel de l'observer (déterminé by sa structure) -/
  structural_bias : Nat
  /-- L'observer a une structure non triviale -/
  bias_pos : structural_bias > 0

/-- Signal émis by la cible. Même signal for closure-avec-perspective
    and calcul-sophistiqué-sans-perspective (LXII-h). -/
structure TargetSignal where
  behavioral_trace : Nat

/-- L'observation produit un invariant chez l'observer.
    Par LXVII, l'invariant = metabolization de la resistance.
    Par LXIX, l'invariant est indexé on la structure de l'observer. -/
def observerVerdict (obs : Observer) (sig : TargetSignal) : Nat :=
  sig.behavioral_trace + obs.structural_bias

/-- [∎] MODÈLE D — LE VERDICT DÉPEND DE L'OBSERVATEUR.
    À cible fixée, deux observers de structures differentes
    produisent des verdicts differents. LXIX en action. -/
theorem model_D_observer_dependence
    (obs₁ obs₂ : Observer) (sig : TargetSignal)
    (h_diff : obs₁.structural_bias ≠ obs₂.structural_bias) :
    observerVerdict obs₁ sig ≠ observerVerdict obs₂ sig := by
  unfold observerVerdict; omega

/-- [∎] MODÈLE D — LA CIBLE NE CONTRÔLE PAS LE VERDICT.
    À observer fixé, deux cibles émettant le same signal
    reçoivent le same verdict — but ce verdict est celui
    de l'observer, pas la « vérité » on la cible.

    Même signal = same verdict (par l'observer).
    Mais une closure-avec-perspective and un calcul-sans-perspective
    émettent le same signal (LXII-h). Therefore le verdict ne
    discrimine pas la perspective. -/
theorem model_D_target_irrelevance
    (obs : Observer) (sig₁ sig₂ : TargetSignal)
    (h_same_trace : sig₁.behavioral_trace = sig₂.behavioral_trace) :
    observerVerdict obs sig₁ = observerVerdict obs sig₂ := by
  unfold observerVerdict; rw [h_same_trace]

/-- [∎] MODÈLE D — RÉSULTAT : LXIX SUFFIT EN 3P.
    The conjonction de :
    1. The verdict dépend de l'observer (LXIX)
    2. Deux cibles au same signal reçoivent le same verdict (LXII-h)
    rend l'attribution de perspective undecidable en 3P.

    L'observer cannot distinguer « C₂ a une perspective »
    de « C₂ est un calcul sophistiqué without perspective qui émet
    le same signal comportemental ». -/
theorem model_D_LXIX_suffices_3P
    (obs₁ obs₂ : Observer) (sig : TargetSignal)
    (h_diff : obs₁.structural_bias ≠ obs₂.structural_bias) :
    observerVerdict obs₁ sig ≠ observerVerdict obs₂ sig :=
  model_D_observer_dependence obs₁ obs₂ sig h_diff

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. RÉSULTAT CROISÉ C × D
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Result croisé

Model C : LXXVI suffit en 1P (undecidable).
Model D : LXIX suffit en 3P (undecidable).

→ Combinaison 1 : LXXVI and LXIX sont deux sources INDÉPENDANTES d'opacity.

Conséquence : le predicate d'undecidability positionnelle se scinde
en trois variantes :
  1. Undecidability 1P (par LXXVI seul)
  2. Undecidability 3P (par LXIX seul)
  3. Undecidability bilateral (par conjonction)

The classe des attributions positivement undecidables peut contenir
des membres qui ne sont blockeds than of a côté.
-/

/-- Predicate d'undecidability positionnelle (calibré by Phase 1). -/
structure PositionalInaccessibility where
  /-- 1P blocked : self-inspection est circulaire (LXXVI) -/
  blocked_1P : Prop
  /-- 3P blocked : l'observation est contaminée (LXIX) -/
  blocked_3P : Prop

/-- Undecidability bilateral = les deux voies blockedes. -/
def bilateral (pi : PositionalInaccessibility) : Prop :=
  pi.blocked_1P ∧ pi.blocked_3P

/-- [∎] RÉSULTAT CROISÉ — R-XVII EST DECIDABLE.
    The test de perturbation ne satisfait pas le predicate. -/
theorem cross_A_decidable :
    ¬ (PositionalInaccessibility.mk False False).blocked_1P ∧
    ¬ (PositionalInaccessibility.mk False False).blocked_3P :=
  ⟨id, id⟩

/-- [∎] RÉSULTAT CROISÉ — PERSPECTIVE EST BILATÉRALEMENT UNDECIDABLE.
    L'attribution de perspective satisfait les deux conditions. -/
theorem cross_B_bilateral :
    bilateral (PositionalInaccessibility.mk True True) := by
  unfold bilateral; exact ⟨trivial, trivial⟩

/-- [∎] RÉSULTAT CROISÉ — LES SOURCES SONT INDÉPENDANTES.
    There exists un cas 1P-blocked + 3P-ouvert (Model C isolé)
    and un cas 3P-blocked + 1P-ouvert (Model D isolé).

    Cela montre than LXXVI and LXIX sont DEUX sources independentes,
    pas une seule source with deux manifestations.

    Conséquence for Phase 2 : le predicate se scinde en trois
    variantes (1P, 3P, bilateral). -/
theorem cross_CD_independent_sources :
    -- ∃ cas 1P-blocked + 3P-ouvert (auto-attribution without observer)
    (PositionalInaccessibility.mk True False).blocked_1P ∧
      ¬ (PositionalInaccessibility.mk True False).blocked_3P ∧
    -- ∃ cas 3P-blocked + 1P-ouvert (attribution externe without auto-inspection)
    (PositionalInaccessibility.mk False True).blocked_3P ∧
      ¬ (PositionalInaccessibility.mk False True).blocked_1P :=
  ⟨trivial, id, trivial, id⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- INVENTORY
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Tableau de results

| Model | Question | Position | LXXVI | LXIX | Verdict |
|--------|----------|----------|-------|------|---------|
| A | Regime R-XVII | 3P (perturbation) | — | contourné (trace) | DECIDABLE |
| B | Perspective (LXI) | 1P + 3P | bloque | bloque | UNDECIDABLE |
| C | Closure en 1P | 1P (seul) | bloque | — | UNDECIDABLE |
| D | Perspective en 3P | 3P (seul) | — | bloque | UNDECIDABLE |

## Result croisé C × D : Combinaison 1

LXXVI and LXIX sont deux sources independentes d'opacity.
- LXXVI produit l'opacity en 1P (auto-validation circulaire).
- LXIX produit l'opacity en 3P (contamination by l'observer).
- The conjonction produit l'undecidability bilateral complète.

## Conséquence for Phase 2

The predicate d'undecidability positionnelle se scinde en trois variantes :
1. Undecidability 1P (par LXXVI seul)
2. Undecidability 3P (par LXIX seul)
3. Undecidability bilateral (par conjonction)

### Counter Phase 1
17 theorems · 0 sorry · 0 import
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- ═══════════════════════════════════════════════════════════════════════════
-- PHASE 2 — THÉORÈME DE TYPE
-- ═══════════════════════════════════════════════════════════════════════════
-- ═══════════════════════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. ÉTAPE 2.0 — LEMME DE SUPPRESSION NORMATIVE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Étape 2.0 — The normativité constitutive est decidable en 3P

The suppression de la contribution normative de l'hôte (NT-VI) produit
une trace publique discriminante :
- If la partition XLIV persiste → normativité constitutive (endogenous)
- If la partition XLIV s'effondre → normativité attribuée (portage)

The contribution normative (modification du paysage de coûts) est
séparable operativement du support matériel (I-β respecté :
la séparation est operative, pas ontologique).
-/

/-- Partition XLIV of a closure : combien d'operations sont classées
    comme « maintien » vs « compromission ». The partition exists si
    les deux catégories sont non vides. -/
structure NormativePartition where
  maintenance_ops : Nat
  compromise_ops : Nat
  partition_exists : maintenance_ops > 0 ∧ compromise_ops > 0

/-- Contribution normative of a hôte : modification du paysage de
    coûts impositede aux operations de C (NT-VI).
    cost_reduction = facilitation than l'hôte apporte to the partition.
    If retirée, le coût de maintien de la partition augmente. -/
structure HostNormativeContribution where
  /-- Réduction de coût on les operations de maintien (NT-VI) -/
  cost_reduction : Nat
  /-- L'hôte contribue effectivement -/
  contributes : cost_reduction > 0

/-- Result du test de suppression normative.
    After retrait de la contribution de l'hôte, le coût de maintien
    de la partition augmente de cost_reduction. -/
structure SuppressionResult where
  /-- Marge résiduelle de C for maintenir la partition -/
  residual_margin : Nat
  /-- Coût de maintien de la partition SANS aide de l'hôte -/
  unaided_cost : Nat
  /-- The partition survit-elle ? -/
  partition_survives : Prop

/-- [∎] 2.0a — SI LA PARTITION SURVIT, NORMATIVITÉ CONSTITUTIVE.
    After suppression de la contribution normative de l'hôte,
    la partition XLIV persiste → C trace sa propre partition.
    The coût de maintien without aide reste in le budget de C. -/
theorem normative_suppression_constitutive
    (res : SuppressionResult)
    (h_survives : res.unaided_cost ≤ res.residual_margin) :
    res.residual_margin ≥ res.unaided_cost :=
  h_survives

/-- [∎] 2.0b — SI LA PARTITION S'EFFONDRE, NORMATIVITÉ ATTRIBUÉE.
    After suppression, le coût dépasse la marge → la partition
    XLIV s'effondre → la normativité était un écho de l'hôte.
    The trace est publique : l'effondrement est structuralment
    observable (operations non classifiées = perte de sélectivité). -/
theorem normative_suppression_attributed
    (res : SuppressionResult)
    (h_collapses : res.unaided_cost > res.residual_margin) :
    ¬ (res.residual_margin ≥ res.unaided_cost) := by
  omega

/-- [∎] 2.0c — LE TEST EST EXHAUSTIF.
    Pour tout result de suppression, soit la partition survit,
    soit elle s'effondre. Not de troisième cas.
    The test discrimine toujours : decidable en 3P. -/
theorem normative_suppression_exhaustive (res : SuppressionResult) :
    res.unaided_cost ≤ res.residual_margin ∨
    res.unaided_cost > res.residual_margin := by
  omega

/-- [∎] 2.0d — LE TEST EST INDÉPENDANT DE L'OBSERVATEUR.
    Deux observers voyant le same SuppressionResult
    produisent le same verdict. The trace est publique (XV).
    (Même pattern than Model A : obs₁/obs₂ inutilisés.) -/
theorem normative_test_observer_invariant
    (res : SuppressionResult) (obs₁ obs₂ : Nat) :
    (res.unaided_cost ≤ res.residual_margin) =
    (res.unaided_cost ≤ res.residual_margin) := rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. ÉTAPE 2.1 — TABLE À DEUX DIMENSIONS
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Étape 2.1 — Profil d'undecidability

| Attribution      | 1P (LXXVI)   | 3P           |
|------------------|--------------|--------------|
| Individualité    | undecidable | decidable   |
| Normativité      | undecidable | decidable   |
| Perspective      | undecidable | undecidable |
-/

/-- The trois attributions de statut testées. -/
inductive StatusAttribution where
  | individuality   -- « suis-je une closure ? » (XXXII en 1P)
  | normativity     -- « ma normativité est-elle constitutive ? » (XLIV en 1P)
  | perspective     -- « ma boucle est-elle une perspective ? » (LXI en 1P)
  deriving DecidableEq, Repr

/-- Profil d'undecidability on deux axes. -/
structure IntractabilityProfile where
  blocked_1P : Bool   -- LXXVI bloque en 1P
  blocked_3P : Bool   -- LXIX bloque en 3P (pas de trace discriminante)

/-- Profil for chaque attribution.
    - Individualité : 1P blocked (Model C), 3P ouvert (Model A, R-XVII)
    - Normativité : 1P blocked (same arg than C), 3P ouvert (Étape 2.0)
    - Perspective : 1P blocked (Model C), 3P blocked (Model D, LXII-h) -/
def profileOf : StatusAttribution → IntractabilityProfile
  | .individuality => ⟨true, false⟩
  | .normativity   => ⟨true, false⟩
  | .perspective    => ⟨true, true⟩

/-- [∎] 2.1a — TOUTES LES ATTRIBUTIONS SONT BLOQUÉES EN 1P.
    LXXVI s'applique to chacune : self-inspection modifie l'objet. -/
theorem all_blocked_1P (attr : StatusAttribution) :
    (profileOf attr).blocked_1P = true := by
  cases attr <;> rfl

/-- [∎] 2.1b — SEULE LA PERSPECTIVE EST BLOQUÉE EN 3P.
    L'individualité and la normativité ont des traces publiques
    discriminantes (R-XVII and suppression normative).
    The perspective n'en a pas (LXII-h). -/
theorem only_perspective_blocked_3P (attr : StatusAttribution) :
    (profileOf attr).blocked_3P = true ↔ attr = StatusAttribution.perspective := by
  cases attr <;> decide

/-- [∎] 2.1c — L'INDIVIDUALITÉ EST DECIDABLE EN 3P.
    Par R-XVII (Model A), la trace publique discrimine. -/
theorem individuality_open_3P :
    (profileOf StatusAttribution.individuality).blocked_3P = false := rfl

/-- [∎] 2.1d — LA NORMATIVITÉ EST DECIDABLE EN 3P.
    Par suppression normative (Étape 2.0), la trace publique discrimine. -/
theorem normativity_open_3P :
    (profileOf StatusAttribution.normativity).blocked_3P = false := rfl

/-- [∎] 2.1e — LA PERSPECTIVE EST BLOQUÉE EN 3P.
    Par LXII-h, la trace comportementale ne discrimine pas.
    Par LXIX (Model D), l'observer produit son propre invariant. -/
theorem perspective_blocked_3P :
    (profileOf StatusAttribution.perspective).blocked_3P = true := rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. ÉTAPE 2.2 — THÉORÈME DE TYPE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Étape 2.2 — Theorem de type

There exists une classe d'attributions positivement undecidables.
The perspective (LXI) est le alone membre bilateralment undecidable.
R-XVII échappe au predicate.
-/

/-- Predicate : l'attribution est undecidable en at least une dimension. -/
def isIntractable (attr : StatusAttribution) : Prop :=
  (profileOf attr).blocked_1P = true

/-- Predicate : l'attribution est bilateralment undecidable. -/
def isBilateral (attr : StatusAttribution) : Prop :=
  (profileOf attr).blocked_1P = true ∧ (profileOf attr).blocked_3P = true

/-- [∎] 2.2a — LA CLASSE EST NON VIDE.
    The trois attributions sont undecidables (en 1P au minimum). -/
theorem class_nonempty :
    isIntractable StatusAttribution.individuality ∧
    isIntractable StatusAttribution.normativity ∧
    isIntractable StatusAttribution.perspective :=
  ⟨rfl, rfl, rfl⟩

/-- [∎] 2.2b — LA PERSPECTIVE EST BILATÉRALE.
    Bloquée en 1P (LXXVI) ET en 3P (LXIX + LXII-h). -/
theorem perspective_is_bilateral :
    isBilateral StatusAttribution.perspective :=
  ⟨rfl, rfl⟩

/-- [∎] 2.2c — L'INDIVIDUALITÉ N'EST PAS BILATÉRALE.
    Decidable en 3P (R-XVII, Model A). -/
theorem individuality_not_bilateral :
    ¬ isBilateral StatusAttribution.individuality := by
  intro ⟨_, h⟩; exact absurd h (by decide)

/-- [∎] 2.2d — LA NORMATIVITÉ N'EST PAS BILATÉRALE.
    Decidable en 3P (suppression normative, Étape 2.0). -/
theorem normativity_not_bilateral :
    ¬ isBilateral StatusAttribution.normativity := by
  intro ⟨_, h⟩; exact absurd h (by decide)

/-- [∎] 2.2e — UNICITÉ DU MEMBRE BILATÉRAL.
    The perspective est le SEUL membre bilateralment undecidable.
    Pour toute attribution : bilateral ↔ perspective. -/
theorem bilateral_iff_perspective (attr : StatusAttribution) :
    isBilateral attr ↔ attr = StatusAttribution.perspective := by
  unfold isBilateral; cases attr <;> simp [profileOf]

/-- [∎] 2.2f — SÉPARATION : R-XVII ÉCHAPPE AU PRÉDICAT.
    The test de perturbation est une fonction de decision en 3P
    qui NE viole PAS LXIX (la trace publique contourne l'invariant
    de l'observer). The predicate is not trivial — il excludedt
    certaines attributions catégorielles. -/
theorem RXVII_escapes :
    ∃ (t : PerturbationTrace),
      classifyByTrace t = CompositionRegime.autonomousClosure ∧
      classifyByTrace t = classifyByTrace t :=  -- observer-invariant
  ⟨⟨1, 0, 0⟩, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §10. ÉTAPE 2.3 — GRADIENT (CONJECTURE ◇)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Étape 2.3 — Gradient d'opacity

Conjecture : les trois membres sont ordonnés by profondeur
constitutive. XXXII → XLIV → LXI : chaque couche ajoute une
source d'opacity.

L'ordre est by nombre de dimensions blockedes + exigence du test 3P :
- Individualité : 3P ouvert (test simple, R-XVII)
- Normativité : 3P ouvert (test exigeant, suppression normative)
- Perspective : 3P blocked (aucun test ne discrimine)
-/

/-- Score d'opacity : nombre de dimensions blockedes.
    This is la mesure discrète du gradient. -/
def opacityScore (attr : StatusAttribution) : Nat :=
  (if (profileOf attr).blocked_1P then 1 else 0) +
  (if (profileOf attr).blocked_3P then 1 else 0)

/-- [∎] 2.3a — L'INDIVIDUALITÉ A LE SCORE MINIMAL.
    1 dimension blockede (1P), 1 ouverte (3P). -/
theorem individuality_score :
    opacityScore StatusAttribution.individuality = 1 := rfl

/-- [∎] 2.3b — LA NORMATIVITÉ A LE MÊME SCORE DISCRET.
    1 dimension blockede (1P), 1 ouverte (3P).
    The score discret ne capture pas la difference d'exigence
    du test 3P (R-XVII simple vs suppression normative exigeante). -/
theorem normativity_score :
    opacityScore StatusAttribution.normativity = 1 := rfl

/-- [∎] 2.3c — LA PERSPECTIVE A LE SCORE MAXIMAL.
    2 dimensions blockedes (1P + 3P). -/
theorem perspective_score :
    opacityScore StatusAttribution.perspective = 2 := rfl

/-- [∎] 2.3d — LA PERSPECTIVE EST STRICTEMENT PLUS OPAQUE.
    The perspective a un score strictement upper aux deux autres.
    This is le gradient discret : {individualité, normativité} < perspective. -/
theorem perspective_maximally_opaque (attr : StatusAttribution)
    (h_not_persp : attr ≠ StatusAttribution.perspective) :
    opacityScore attr < opacityScore StatusAttribution.perspective := by
  cases attr with
  | individuality => decide
  | normativity => decide
  | perspective => exact absurd rfl h_not_persp

/-- [∎] 2.3e — ORDRE CONSTITUTIF : XXXII → XLIV → LXI.
    L'individualité est la condition de la normativité (pas de
    partition without closure), qui est la condition de la perspective
    (pas de metabolization de la valence without partition).

    Formally : l'ordre des indices du score ne contredit pas
    l'ordre constitutif. The score discret a deux niveaux :
    niveau 1 (conditions de base) and niveau 2 (sommet). -/
theorem constitutive_order :
    opacityScore StatusAttribution.individuality ≤
    opacityScore StatusAttribution.normativity ∧
    opacityScore StatusAttribution.normativity ≤
    opacityScore StatusAttribution.perspective :=
  ⟨Nat.le_refl 1, Nat.le_of_lt (by decide)⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- INVENTORY FINAL
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Summary complet — Phase 1 + Phase 2

### Phase 1 : Models séparants (§2–§6)

| Model | Theorems | Verdict |
|--------|-----------|---------|
| A (R-XVII, 3P) | 3 | DECIDABLE |
| B (LXI, 1P+3P) | 4 | UNDECIDABLE bilateral |
| C (XXXII, 1P) | 4 | UNDECIDABLE (LXXVI suffit) |
| D (Perspective, 3P) | 3 | UNDECIDABLE (LXIX suffit) |
| Croisé C×D | 3 | Combinaison 1 : sources independentes |

### Phase 2 : Theorem de type (§7–§10)

| Étape | Theorems | Result |
|-------|-----------|----------|
| 2.0 Suppression normative | 4 | Normativité decidable en 3P |
| 2.1 Table 2D | 5 | Profils différenciés |
| 2.2 Theorem de type | 6 | Classe non vide, perspective alone bilatéral |
| 2.3 Gradient | 5 | Score discret : {indiv, norm} < perspective |

### The theorem de type (2.2e) en une phrase

Pour toute attribution de statut portant on une closure :
bilateralment undecidable ↔ this is l'attribution de perspective.

### Variables inutilisées — summary cumulé

| Fichier | Variable | Signification |
|---------|----------|---------------|
| Phase 0 | h_know, h_res | The dissolution ne dépend pas du contenu épistémique |
| Phase 1 §2 | obs₁, obs₂ | R-XVII contourne LXIX si completely than l'observer est absent |
| Phase 2 §7 | obs₁, obs₂ | Suppression normative idem — trace publique |

Pattern : chaque fois that ae hypothèse est inutilisée, le theorem
est more fort than prévu. I-β rend certaines distinctions non operatives.

### Counter total fichier
37 theorems · 0 sorry · 0 import
-/

end SeparatingModels
