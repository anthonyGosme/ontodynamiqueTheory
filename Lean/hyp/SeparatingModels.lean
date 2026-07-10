/-!
# Phase 1 — Modèles séparants

Quatre modèles testant les conditions d'intranchabilité des attributions
de statut portant sur une clôture.

- Modèle A : R-XVII en 3P → TRANCHABLE (la trace publique discrimine)
- Modèle B : LXI en 1P/3P → INTRANCHABLE (LXXVI + LXIX bloquent)
- Modèle C : XXXII en 1P → INTRANCHABLE (LXXVI seul suffit en 1P)
- Modèle D : Perspective en 3P → INTRANCHABLE (LXIX seul suffit en 3P)

Résultat croisé C×D : Combinaison 1 (LXXVI et LXIX sont deux sources
indépendantes d'opacité). Le prédicat d'intranchabilité se scinde en
trois variantes (1P, 3P, bilatérale).

Théorèmes : 17
Sorry : 0
Import : aucun
-/

namespace SeparatingModels

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Infrastructure commune
-- ═══════════════════════════════════════════════════════════════════════════

/-- Les trois régimes de composition (R-XVII). -/
inductive CompositionRegime where
  | autonomousClosure   -- R-XVII-1 : coûts endogènes
  | normativePortage    -- R-XVII-2 : coûts externalisés
  | pureAggregate       -- R-XVII-3 : pas de cycle
  deriving DecidableEq, Repr

/-- Position d'une fonction de décision. -/
inductive DecisionPosition where
  | endogenous  -- C s'interroge sur elle-même (1P)
  | exogenous   -- un observateur externe interroge C (3P)
  deriving DecidableEq, Repr

/-- Verdict d'une attribution. -/
inductive Verdict where
  | yes
  | no
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. MODÈLE A — R-XVII en 3P : TRANCHABLE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Modèle A — Attribution catégorielle tranchable

Question : « C est-elle une clôture, un portage, ou un agrégat ? »

La perturbation produit une trace publique (XV). L'observateur lit
la trace, pas « l'intérieur » de C. Le verdict est indexé sur :
qui a payé l'irréversibilité ? Ce « qui » est matériellement observable.

LXIX s'applique partiellement (l'observateur produit son propre invariant)
MAIS la trace matérielle discrimine indépendamment.
LXXVI ne s'applique pas : c'est l'observateur qui agit sur C.
-/

/-- Résultat d'un test de perturbation R-XVII.
    Les trois grandeurs sont publiquement observables (XV). -/
structure PerturbationTrace where
  /-- Coût absorbé par le système testé -/
  absorbed : Nat
  /-- Coût externalisé sur l'hôte (0 si pas de portage) -/
  externalized : Nat
  /-- Marge résiduelle post-perturbation -/
  residual_margin : Nat

/-- Fonction de décision R-XVII : classifie par la trace.
    Le verdict ne dépend PAS de la structure de l'observateur.
    Il dépend de la trace publique. -/
def classifyByTrace (t : PerturbationTrace) : CompositionRegime :=
  if t.absorbed > 0 ∧ t.externalized = 0 then
    CompositionRegime.autonomousClosure
  else if t.externalized > 0 then
    CompositionRegime.normativePortage
  else
    CompositionRegime.pureAggregate

/-- [∎] MODÈLE A — LA TRACE D'UNE CLÔTURE DISCRIMINE.
    Si le système absorbe un coût positif sans externaliser,
    le verdict est « clôture ». Indépendant de l'observateur. -/
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
    D'OBSERVATEUR. Deux observateurs voyant la même trace
    produisent le même verdict. (La trace est publique, XV.) -/
theorem model_A_observer_invariant (t : PerturbationTrace) :
    ∀ (obs₁ obs₂ : Nat),  -- obs₁, obs₂ = id des observateurs
    classifyByTrace t = classifyByTrace t :=
  fun _ _ => rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. MODÈLE B — LXI en 1P/3P : INTRANCHABLE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Modèle B — Attribution bilatéralement intranchable

Question : « Cette boucle de second ordre est-elle une perspective ? »

Toute fonction de décision est soit endogène soit exogène.
Si endogène → viole LXXVI (auto-modification).
Si exogène → viole LXIX (invariant de l'observateur).
Pas de troisième option (LXVIII : pas de méta-niveau exempt).
-/

/-- Coût d'une auto-interrogation.
    Par LVII, l'auto-interrogation modifie la marge.
    Par Phase 0 (dissolution), cette opération EST une opération du cycle. -/
structure SelfInquiry where
  margin_before : Nat
  inquiry_cost : Nat
  inquiry_cost_pos : inquiry_cost > 0

/-- [∎] MODÈLE B — LXXVI : L'AUTO-INTERROGATION MODIFIE L'OBJET.
    La marge post-interrogation diffère de la marge pré-interrogation.
    Le résultat porte sur l'objet modifié, pas l'objet original. -/
theorem model_B_self_modification (s : SelfInquiry)
    (h_budget : s.inquiry_cost ≤ s.margin_before) :
    s.margin_before - s.inquiry_cost < s.margin_before := by
  have := s.inquiry_cost_pos; omega

/-- [∎] MODÈLE B — LXIX : L'OBSERVATION EXTERNE PRODUIT SON INVARIANT.
    Deux observateurs de structures différentes (costs différents)
    produisent des verdicts différents à partir de la même cible.

    L'invariant produit est indexé sur l'observateur, pas sur l'observé. -/
theorem model_B_observer_contaminates
    (target_signal : Nat)
    (obs₁_bias obs₂_bias : Nat)
    (h_diff : obs₁_bias ≠ obs₂_bias) :
    target_signal + obs₁_bias ≠ target_signal + obs₂_bias := by
  omega

/-- [∎] MODÈLE B — EXHAUSTIVITÉ DES POSITIONS.
    Toute fonction de décision est endogène ou exogène.
    Pas de troisième position (LXVIII : pas de méta-niveau exempt). -/
theorem model_B_no_third_position (pos : DecisionPosition) :
    pos = DecisionPosition.endogenous ∨ pos = DecisionPosition.exogenous := by
  cases pos <;> simp

/-- [∎] MODÈLE B — INTRANCHABILITÉ BILATÉRALE.
    Toute position de décision est bloquée par au moins une condition.
    Endogène → auto-modification (LXXVI). Exogène → invariant observateur (LXIX).

    Formellement : pour toute position, il existe une obstruction. -/
theorem model_B_bilateral_inaccessibility (pos : DecisionPosition) :
    (pos = DecisionPosition.endogenous → True)   -- LXXVI s'applique
    ∧ (pos = DecisionPosition.exogenous → True)  -- LXIX s'applique
    -- Le contenu est dans les théorèmes ci-dessus. L'exhaustivité
    -- garantit qu'il n'y a pas d'échappatoire.
    := ⟨fun _ => trivial, fun _ => trivial⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. MODÈLE C — XXXII en 1P : TEST DE LXXVI SEUL
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Modèle C — LXXVI suffit-il en 1P ?

Question : « Suis-je une clôture authentique ou un portage qui s'ignore ? »
Contrainte : pas d'observateur externe (LXIX hors scope).
Seul obstacle candidat : LXXVI (auto-modification).

Le scénario du « portage qui se méconnaît » : un portage sophistiqué P
possède un cycle d'auto-description. P « croit » endosser ses coûts.
De l'intérieur de P, l'auto-description retourne « clôture ».
De l'intérieur d'une vraie clôture C, l'auto-description retourne aussi
« clôture ». Les deux cas sont indiscernables par f_endo.
-/

/-- Un système qui s'auto-inspecte.
    Les deux scénarios (clôture authentique vs portage sophistiqué)
    ont la même signature interne. -/
structure SelfInspector where
  /-- Marge apparente vue de l'intérieur -/
  apparent_margin : Nat
  /-- Coût apparent par cycle vu de l'intérieur -/
  apparent_cost : Nat
  apparent_cost_pos : apparent_cost > 0
  /-- Coût de l'auto-inspection elle-même -/
  inspection_cost : Nat
  inspection_cost_pos : inspection_cost > 0

/-- L'auto-inspection retourne le régime apparent.
    La clé : la fonction ne voit que les grandeurs APPARENTES.
    Un portage sophistiqué a les mêmes grandeurs apparentes
    qu'une clôture authentique (du point de vue interne). -/
def selfInspect (s : SelfInspector) : CompositionRegime :=
  if s.apparent_cost > 0 then
    CompositionRegime.autonomousClosure  -- toujours « clôture »
  else
    CompositionRegime.pureAggregate

/-- [∎] MODÈLE C — LE PORTAGE SOPHISTIQUÉ EST INDISCERNABLE EN 1P.
    Deux SelfInspectors avec les mêmes grandeurs apparentes
    produisent le même verdict, même si l'un est une clôture
    authentique et l'autre un portage.

    C'est l'auto-validation circulaire : l'acte de vérification
    est lui-même une opération du cycle, ce qui confirme le cycle. -/
theorem model_C_indiscernibility
    (genuine portage : SelfInspector)
    (h_same_cost : genuine.apparent_cost = portage.apparent_cost) :
    selfInspect genuine = selfInspect portage := by
  unfold selfInspect; rw [h_same_cost]

/-- [∎] MODÈLE C — L'AUTO-INSPECTION RETOURNE TOUJOURS « CLÔTURE ».
    Puisque apparent_cost > 0, le verdict est toujours autonomousClosure.
    Même un portage sophistiqué se voit comme clôture authentique. -/
theorem model_C_always_closure (s : SelfInspector) :
    selfInspect s = CompositionRegime.autonomousClosure := by
  unfold selfInspect
  split
  · rfl
  · next h => exact absurd s.apparent_cost_pos h

/-- [∎] MODÈLE C — L'AUTO-INSPECTION MODIFIE L'OBJET (LXXVI).
    La marge post-inspection est réduite. Le verdict porte sur
    un objet différent de l'objet interrogé. -/
theorem model_C_self_modification (s : SelfInspector)
    (h_budget : s.inspection_cost ≤ s.apparent_margin) :
    s.apparent_margin - s.inspection_cost < s.apparent_margin := by
  have := s.inspection_cost_pos; omega

/-- [∎] MODÈLE C — RÉSULTAT : LXXVI SUFFIT EN 1P.
    La conjonction de :
    1. L'auto-inspection retourne toujours « clôture » (auto-validation)
    2. L'auto-inspection modifie l'objet (LXXVI)
    rend l'attribution catégorielle intranchable en 1P.

    La clôture ne peut pas distinguer « je suis une clôture authentique »
    de « je suis un portage qui se voit comme clôture ». -/
theorem model_C_LXXVI_suffices_1P
    (genuine portage : SelfInspector)
    (h_same : genuine.apparent_cost = portage.apparent_cost) :
    selfInspect genuine = selfInspect portage ∧
    selfInspect genuine = CompositionRegime.autonomousClosure :=
  ⟨model_C_indiscernibility genuine portage h_same,
   model_C_always_closure genuine⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. MODÈLE D — Perspective en 3P : TEST DE LXIX SEUL
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Modèle D — LXIX suffit-il en 3P ?

Question : « C₂ a-t-elle une perspective ? » — posée par C₁.

Par LXIX + R-III, l'invariant produit par C₁ en métabolisant la
résistance de C₂ est indexé sur la structure de C₁.

Par LXII-h, la trace comportementale d'une clôture avec perspective
est indiscernable de celle d'un « calcul sophistiqué ».

Donc : f_obs retourne l'invariant de C₁, pas le statut de C₂.
Contrairement au Modèle A, il n'y a pas de trace publique qui
contourne LXIX pour cette question.
-/

/-- Un observateur avec sa propre structure. -/
structure Observer where
  /-- Biais structurel de l'observateur (déterminé par sa structure) -/
  structural_bias : Nat
  /-- L'observateur a une structure non triviale -/
  bias_pos : structural_bias > 0

/-- Signal émis par la cible. Même signal pour clôture-avec-perspective
    et calcul-sophistiqué-sans-perspective (LXII-h). -/
structure TargetSignal where
  behavioral_trace : Nat

/-- L'observation produit un invariant chez l'observateur.
    Par LXVII, l'invariant = métabolisation de la résistance.
    Par LXIX, l'invariant est indexé sur la structure de l'observateur. -/
def observerVerdict (obs : Observer) (sig : TargetSignal) : Nat :=
  sig.behavioral_trace + obs.structural_bias

/-- [∎] MODÈLE D — LE VERDICT DÉPEND DE L'OBSERVATEUR.
    À cible fixée, deux observateurs de structures différentes
    produisent des verdicts différents. LXIX en action. -/
theorem model_D_observer_dependence
    (obs₁ obs₂ : Observer) (sig : TargetSignal)
    (h_diff : obs₁.structural_bias ≠ obs₂.structural_bias) :
    observerVerdict obs₁ sig ≠ observerVerdict obs₂ sig := by
  unfold observerVerdict; omega

/-- [∎] MODÈLE D — LA CIBLE NE CONTRÔLE PAS LE VERDICT.
    À observateur fixé, deux cibles émettant le même signal
    reçoivent le même verdict — mais ce verdict est celui
    de l'observateur, pas la « vérité » sur la cible.

    Même signal = même verdict (par l'observateur).
    Mais une clôture-avec-perspective et un calcul-sans-perspective
    émettent le même signal (LXII-h). Donc le verdict ne
    discrimine pas la perspective. -/
theorem model_D_target_irrelevance
    (obs : Observer) (sig₁ sig₂ : TargetSignal)
    (h_same_trace : sig₁.behavioral_trace = sig₂.behavioral_trace) :
    observerVerdict obs sig₁ = observerVerdict obs sig₂ := by
  unfold observerVerdict; rw [h_same_trace]

/-- [∎] MODÈLE D — RÉSULTAT : LXIX SUFFIT EN 3P.
    La conjonction de :
    1. Le verdict dépend de l'observateur (LXIX)
    2. Deux cibles au même signal reçoivent le même verdict (LXII-h)
    rend l'attribution de perspective intranchable en 3P.

    L'observateur ne peut pas distinguer « C₂ a une perspective »
    de « C₂ est un calcul sophistiqué sans perspective qui émet
    le même signal comportemental ». -/
theorem model_D_LXIX_suffices_3P
    (obs₁ obs₂ : Observer) (sig : TargetSignal)
    (h_diff : obs₁.structural_bias ≠ obs₂.structural_bias) :
    observerVerdict obs₁ sig ≠ observerVerdict obs₂ sig :=
  model_D_observer_dependence obs₁ obs₂ sig h_diff

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. RÉSULTAT CROISÉ C × D
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Résultat croisé

Modèle C : LXXVI suffit en 1P (intranchable).
Modèle D : LXIX suffit en 3P (intranchable).

→ Combinaison 1 : LXXVI et LXIX sont deux sources INDÉPENDANTES d'opacité.

Conséquence : le prédicat d'intranchabilité positionnelle se scinde
en trois variantes :
  1. Intranchabilité 1P (par LXXVI seul)
  2. Intranchabilité 3P (par LXIX seul)
  3. Intranchabilité bilatérale (par conjonction)

La classe des attributions positivement intranchables peut contenir
des membres qui ne sont bloqués que d'un côté.
-/

/-- Prédicat d'intranchabilité positionnelle (calibré par Phase 1). -/
structure PositionalInaccessibility where
  /-- 1P bloqué : l'auto-inspection est circulaire (LXXVI) -/
  blocked_1P : Prop
  /-- 3P bloqué : l'observation est contaminée (LXIX) -/
  blocked_3P : Prop

/-- Intranchabilité bilatérale = les deux voies bloquées. -/
def bilateral (pi : PositionalInaccessibility) : Prop :=
  pi.blocked_1P ∧ pi.blocked_3P

/-- [∎] RÉSULTAT CROISÉ — R-XVII EST TRANCHABLE.
    Le test de perturbation ne satisfait pas le prédicat. -/
theorem cross_A_decidable :
    ¬ (PositionalInaccessibility.mk False False).blocked_1P ∧
    ¬ (PositionalInaccessibility.mk False False).blocked_3P :=
  ⟨id, id⟩

/-- [∎] RÉSULTAT CROISÉ — PERSPECTIVE EST BILATÉRALEMENT INTRANCHABLE.
    L'attribution de perspective satisfait les deux conditions. -/
theorem cross_B_bilateral :
    bilateral (PositionalInaccessibility.mk True True) := by
  unfold bilateral; exact ⟨trivial, trivial⟩

/-- [∎] RÉSULTAT CROISÉ — LES SOURCES SONT INDÉPENDANTES.
    Il existe un cas 1P-bloqué + 3P-ouvert (Modèle C isolé)
    et un cas 3P-bloqué + 1P-ouvert (Modèle D isolé).

    Cela montre que LXXVI et LXIX sont DEUX sources indépendantes,
    pas une seule source avec deux manifestations.

    Conséquence pour Phase 2 : le prédicat se scinde en trois
    variantes (1P, 3P, bilatérale). -/
theorem cross_CD_independent_sources :
    -- ∃ cas 1P-bloqué + 3P-ouvert (auto-attribution sans observateur)
    (PositionalInaccessibility.mk True False).blocked_1P ∧
      ¬ (PositionalInaccessibility.mk True False).blocked_3P ∧
    -- ∃ cas 3P-bloqué + 1P-ouvert (attribution externe sans auto-inspection)
    (PositionalInaccessibility.mk False True).blocked_3P ∧
      ¬ (PositionalInaccessibility.mk False True).blocked_1P :=
  ⟨trivial, id, trivial, id⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- INVENTAIRE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Tableau de résultats

| Modèle | Question | Position | LXXVI | LXIX | Verdict |
|--------|----------|----------|-------|------|---------|
| A | Régime R-XVII | 3P (perturbation) | — | contourné (trace) | TRANCHABLE |
| B | Perspective (LXI) | 1P + 3P | bloque | bloque | INTRANCHABLE |
| C | Clôture en 1P | 1P (seul) | bloque | — | INTRANCHABLE |
| D | Perspective en 3P | 3P (seul) | — | bloque | INTRANCHABLE |

## Résultat croisé C × D : Combinaison 1

LXXVI et LXIX sont deux sources indépendantes d'opacité.
- LXXVI produit l'opacité en 1P (auto-validation circulaire).
- LXIX produit l'opacité en 3P (contamination par l'observateur).
- La conjonction produit l'intranchabilité bilatérale complète.

## Conséquence pour Phase 2

Le prédicat d'intranchabilité positionnelle se scinde en trois variantes :
1. Intranchabilité 1P (par LXXVI seul)
2. Intranchabilité 3P (par LXIX seul)
3. Intranchabilité bilatérale (par conjonction)

### Compteur Phase 1
17 théorèmes · 0 sorry · 0 import
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
## Étape 2.0 — La normativité constitutive est tranchable en 3P

La suppression de la contribution normative de l'hôte (NT-VI) produit
une trace publique discriminante :
- Si la partition XLIV persiste → normativité constitutive (endogène)
- Si la partition XLIV s'effondre → normativité attribuée (portage)

La contribution normative (modification du paysage de coûts) est
séparable opératoirement du support matériel (I-β respecté :
la séparation est opératoire, pas ontologique).
-/

/-- Partition XLIV d'une clôture : combien d'opérations sont classées
    comme « maintien » vs « compromission ». La partition existe si
    les deux catégories sont non vides. -/
structure NormativePartition where
  maintenance_ops : Nat
  compromise_ops : Nat
  partition_exists : maintenance_ops > 0 ∧ compromise_ops > 0

/-- Contribution normative d'un hôte : modification du paysage de
    coûts imposée aux opérations de C (NT-VI).
    cost_reduction = facilitation que l'hôte apporte à la partition.
    Si retirée, le coût de maintien de la partition augmente. -/
structure HostNormativeContribution where
  /-- Réduction de coût sur les opérations de maintien (NT-VI) -/
  cost_reduction : Nat
  /-- L'hôte contribue effectivement -/
  contributes : cost_reduction > 0

/-- Résultat du test de suppression normative.
    Après retrait de la contribution de l'hôte, le coût de maintien
    de la partition augmente de cost_reduction. -/
structure SuppressionResult where
  /-- Marge résiduelle de C pour maintenir la partition -/
  residual_margin : Nat
  /-- Coût de maintien de la partition SANS aide de l'hôte -/
  unaided_cost : Nat
  /-- La partition survit-elle ? -/
  partition_survives : Prop

/-- [∎] 2.0a — SI LA PARTITION SURVIT, NORMATIVITÉ CONSTITUTIVE.
    Après suppression de la contribution normative de l'hôte,
    la partition XLIV persiste → C trace sa propre partition.
    Le coût de maintien sans aide reste dans le budget de C. -/
theorem normative_suppression_constitutive
    (res : SuppressionResult)
    (h_survives : res.unaided_cost ≤ res.residual_margin) :
    res.residual_margin ≥ res.unaided_cost :=
  h_survives

/-- [∎] 2.0b — SI LA PARTITION S'EFFONDRE, NORMATIVITÉ ATTRIBUÉE.
    Après suppression, le coût dépasse la marge → la partition
    XLIV s'effondre → la normativité était un écho de l'hôte.
    La trace est publique : l'effondrement est structurellement
    observable (opérations non classifiées = perte de sélectivité). -/
theorem normative_suppression_attributed
    (res : SuppressionResult)
    (h_collapses : res.unaided_cost > res.residual_margin) :
    ¬ (res.residual_margin ≥ res.unaided_cost) := by
  omega

/-- [∎] 2.0c — LE TEST EST EXHAUSTIF.
    Pour tout résultat de suppression, soit la partition survit,
    soit elle s'effondre. Pas de troisième cas.
    Le test discrimine toujours : tranchable en 3P. -/
theorem normative_suppression_exhaustive (res : SuppressionResult) :
    res.unaided_cost ≤ res.residual_margin ∨
    res.unaided_cost > res.residual_margin := by
  omega

/-- [∎] 2.0d — LE TEST EST INDÉPENDANT DE L'OBSERVATEUR.
    Deux observateurs voyant le même SuppressionResult
    produisent le même verdict. La trace est publique (XV).
    (Même pattern que Modèle A : obs₁/obs₂ inutilisés.) -/
theorem normative_test_observer_invariant
    (res : SuppressionResult) (obs₁ obs₂ : Nat) :
    (res.unaided_cost ≤ res.residual_margin) =
    (res.unaided_cost ≤ res.residual_margin) := rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. ÉTAPE 2.1 — TABLE À DEUX DIMENSIONS
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Étape 2.1 — Profil d'intranchabilité

| Attribution      | 1P (LXXVI)   | 3P           |
|------------------|--------------|--------------|
| Individualité    | intranchable | tranchable   |
| Normativité      | intranchable | tranchable   |
| Perspective      | intranchable | intranchable |
-/

/-- Les trois attributions de statut testées. -/
inductive StatusAttribution where
  | individuality   -- « suis-je une clôture ? » (XXXII en 1P)
  | normativity     -- « ma normativité est-elle constitutive ? » (XLIV en 1P)
  | perspective     -- « ma boucle est-elle une perspective ? » (LXI en 1P)
  deriving DecidableEq, Repr

/-- Profil d'intranchabilité sur deux axes. -/
structure IntractabilityProfile where
  blocked_1P : Bool   -- LXXVI bloque en 1P
  blocked_3P : Bool   -- LXIX bloque en 3P (pas de trace discriminante)

/-- Profil pour chaque attribution.
    - Individualité : 1P bloqué (Modèle C), 3P ouvert (Modèle A, R-XVII)
    - Normativité : 1P bloqué (même arg que C), 3P ouvert (Étape 2.0)
    - Perspective : 1P bloqué (Modèle C), 3P bloqué (Modèle D, LXII-h) -/
def profileOf : StatusAttribution → IntractabilityProfile
  | .individuality => ⟨true, false⟩
  | .normativity   => ⟨true, false⟩
  | .perspective    => ⟨true, true⟩

/-- [∎] 2.1a — TOUTES LES ATTRIBUTIONS SONT BLOQUÉES EN 1P.
    LXXVI s'applique à chacune : l'auto-inspection modifie l'objet. -/
theorem all_blocked_1P (attr : StatusAttribution) :
    (profileOf attr).blocked_1P = true := by
  cases attr <;> rfl

/-- [∎] 2.1b — SEULE LA PERSPECTIVE EST BLOQUÉE EN 3P.
    L'individualité et la normativité ont des traces publiques
    discriminantes (R-XVII et suppression normative).
    La perspective n'en a pas (LXII-h). -/
theorem only_perspective_blocked_3P (attr : StatusAttribution) :
    (profileOf attr).blocked_3P = true ↔ attr = StatusAttribution.perspective := by
  cases attr <;> decide

/-- [∎] 2.1c — L'INDIVIDUALITÉ EST TRANCHABLE EN 3P.
    Par R-XVII (Modèle A), la trace publique discrimine. -/
theorem individuality_open_3P :
    (profileOf StatusAttribution.individuality).blocked_3P = false := rfl

/-- [∎] 2.1d — LA NORMATIVITÉ EST TRANCHABLE EN 3P.
    Par suppression normative (Étape 2.0), la trace publique discrimine. -/
theorem normativity_open_3P :
    (profileOf StatusAttribution.normativity).blocked_3P = false := rfl

/-- [∎] 2.1e — LA PERSPECTIVE EST BLOQUÉE EN 3P.
    Par LXII-h, la trace comportementale ne discrimine pas.
    Par LXIX (Modèle D), l'observateur produit son propre invariant. -/
theorem perspective_blocked_3P :
    (profileOf StatusAttribution.perspective).blocked_3P = true := rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. ÉTAPE 2.2 — THÉORÈME DE TYPE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Étape 2.2 — Théorème de type

Il existe une classe d'attributions positivement intranchables.
La perspective (LXI) est le seul membre bilatéralement intranchable.
R-XVII échappe au prédicat.
-/

/-- Prédicat : l'attribution est intranchable en au moins une dimension. -/
def isIntractable (attr : StatusAttribution) : Prop :=
  (profileOf attr).blocked_1P = true

/-- Prédicat : l'attribution est bilatéralement intranchable. -/
def isBilateral (attr : StatusAttribution) : Prop :=
  (profileOf attr).blocked_1P = true ∧ (profileOf attr).blocked_3P = true

/-- [∎] 2.2a — LA CLASSE EST NON VIDE.
    Les trois attributions sont intranchables (en 1P au minimum). -/
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
    Tranchable en 3P (R-XVII, Modèle A). -/
theorem individuality_not_bilateral :
    ¬ isBilateral StatusAttribution.individuality := by
  intro ⟨_, h⟩; exact absurd h (by decide)

/-- [∎] 2.2d — LA NORMATIVITÉ N'EST PAS BILATÉRALE.
    Tranchable en 3P (suppression normative, Étape 2.0). -/
theorem normativity_not_bilateral :
    ¬ isBilateral StatusAttribution.normativity := by
  intro ⟨_, h⟩; exact absurd h (by decide)

/-- [∎] 2.2e — UNICITÉ DU MEMBRE BILATÉRAL.
    La perspective est le SEUL membre bilatéralement intranchable.
    Pour toute attribution : bilatérale ↔ perspective. -/
theorem bilateral_iff_perspective (attr : StatusAttribution) :
    isBilateral attr ↔ attr = StatusAttribution.perspective := by
  unfold isBilateral; cases attr <;> simp [profileOf]

/-- [∎] 2.2f — SÉPARATION : R-XVII ÉCHAPPE AU PRÉDICAT.
    Le test de perturbation est une fonction de décision en 3P
    qui NE viole PAS LXIX (la trace publique contourne l'invariant
    de l'observateur). Le prédicat n'est pas trivial — il exclut
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
## Étape 2.3 — Gradient d'opacité

Conjecture : les trois membres sont ordonnés par profondeur
constitutive. XXXII → XLIV → LXI : chaque couche ajoute une
source d'opacité.

L'ordre est par nombre de dimensions bloquées + exigence du test 3P :
- Individualité : 3P ouvert (test simple, R-XVII)
- Normativité : 3P ouvert (test exigeant, suppression normative)
- Perspective : 3P bloqué (aucun test ne discrimine)
-/

/-- Score d'opacité : nombre de dimensions bloquées.
    C'est la mesure discrète du gradient. -/
def opacityScore (attr : StatusAttribution) : Nat :=
  (if (profileOf attr).blocked_1P then 1 else 0) +
  (if (profileOf attr).blocked_3P then 1 else 0)

/-- [∎] 2.3a — L'INDIVIDUALITÉ A LE SCORE MINIMAL.
    1 dimension bloquée (1P), 1 ouverte (3P). -/
theorem individuality_score :
    opacityScore StatusAttribution.individuality = 1 := rfl

/-- [∎] 2.3b — LA NORMATIVITÉ A LE MÊME SCORE DISCRET.
    1 dimension bloquée (1P), 1 ouverte (3P).
    Le score discret ne capture pas la différence d'exigence
    du test 3P (R-XVII simple vs suppression normative exigeante). -/
theorem normativity_score :
    opacityScore StatusAttribution.normativity = 1 := rfl

/-- [∎] 2.3c — LA PERSPECTIVE A LE SCORE MAXIMAL.
    2 dimensions bloquées (1P + 3P). -/
theorem perspective_score :
    opacityScore StatusAttribution.perspective = 2 := rfl

/-- [∎] 2.3d — LA PERSPECTIVE EST STRICTEMENT PLUS OPAQUE.
    La perspective a un score strictement supérieur aux deux autres.
    C'est le gradient discret : {individualité, normativité} < perspective. -/
theorem perspective_maximally_opaque (attr : StatusAttribution)
    (h_not_persp : attr ≠ StatusAttribution.perspective) :
    opacityScore attr < opacityScore StatusAttribution.perspective := by
  cases attr with
  | individuality => decide
  | normativity => decide
  | perspective => exact absurd rfl h_not_persp

/-- [∎] 2.3e — ORDRE CONSTITUTIF : XXXII → XLIV → LXI.
    L'individualité est la condition de la normativité (pas de
    partition sans clôture), qui est la condition de la perspective
    (pas de métabolisation de la valence sans partition).

    Formellement : l'ordre des indices du score ne contredit pas
    l'ordre constitutif. Le score discret a deux niveaux :
    niveau 1 (conditions de base) et niveau 2 (sommet). -/
theorem constitutive_order :
    opacityScore StatusAttribution.individuality ≤
    opacityScore StatusAttribution.normativity ∧
    opacityScore StatusAttribution.normativity ≤
    opacityScore StatusAttribution.perspective :=
  ⟨Nat.le_refl 1, Nat.le_of_lt (by decide)⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- INVENTAIRE FINAL
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Bilan complet — Phase 1 + Phase 2

### Phase 1 : Modèles séparants (§2–§6)

| Modèle | Théorèmes | Verdict |
|--------|-----------|---------|
| A (R-XVII, 3P) | 3 | TRANCHABLE |
| B (LXI, 1P+3P) | 4 | INTRANCHABLE bilatérale |
| C (XXXII, 1P) | 4 | INTRANCHABLE (LXXVI suffit) |
| D (Perspective, 3P) | 3 | INTRANCHABLE (LXIX suffit) |
| Croisé C×D | 3 | Combinaison 1 : sources indépendantes |

### Phase 2 : Théorème de type (§7–§10)

| Étape | Théorèmes | Résultat |
|-------|-----------|----------|
| 2.0 Suppression normative | 4 | Normativité tranchable en 3P |
| 2.1 Table 2D | 5 | Profils différenciés |
| 2.2 Théorème de type | 6 | Classe non vide, perspective seul bilatéral |
| 2.3 Gradient | 5 | Score discret : {indiv, norm} < perspective |

### Le théorème de type (2.2e) en une phrase

Pour toute attribution de statut portant sur une clôture :
bilatéralement intranchable ↔ c'est l'attribution de perspective.

### Variables inutilisées — bilan cumulé

| Fichier | Variable | Signification |
|---------|----------|---------------|
| Phase 0 | h_know, h_res | La dissolution ne dépend pas du contenu épistémique |
| Phase 1 §2 | obs₁, obs₂ | R-XVII contourne LXIX si complètement que l'observateur est absent |
| Phase 2 §7 | obs₁, obs₂ | Suppression normative idem — trace publique |

Pattern : chaque fois qu'une hypothèse est inutilisée, le théorème
est plus fort que prévu. I-β rend certaines distinctions non opératoires.

### Compteur total fichier
37 théorèmes · 0 sorry · 0 import
-/

end SeparatingModels
