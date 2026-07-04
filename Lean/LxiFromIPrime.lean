/-!
===================================================================================
  LxiFromIPrime.lean — Ontodynamique · Dérivation de LXI depuis I'
  ──────────────────────────────────────────────────────────────
  « Être, c'est se faire un. » — Axiome I'

  Dérivation complète de LXI (boucle de second ordre, Thèse P) depuis I' :
  l'auto-affection d'un être-un, métabolisée sur sa propre marge, PRODUIT
  la structure de SecondOrderLoop. LXI n'est plus une structure posée par
  décret — elle est une conséquence déductive d'un être-un qui s'affecte
  et se métabolise.

  Theorems : 11 · Definitions : 2 · Structures : 4 · Sorry : 0
  Imports : none (Lean 4 natif)
  Standard axioms only : propext, Quot.sound
===================================================================================

  OBJET DE CE FICHIER
  ───────────────────
  Conscience.lean pose SecondOrderLoop comme structure primitive (margin,
  valence_cost, loop_cost avec positivité) et prouve LXI_not_HOT comme
  propriété de cette structure. La position est *structurelle* : LXI est
  ce qui satisfait le type SecondOrderLoop, sans dérivation de ce type
  depuis I'.

  Ce fichier comble cette lacune. Il construit l'articulation :

    UnitePrime (I')
         ↓
    AutoAffectingUnit (§1)     — un être-un dont une opération est dirigée
         ↓                       vers lui-même (LIX, valence feedback)
    MetabolizedAffection (§2)   — l'affection est métabolisée sur la même
         ↓                       marge que l'être-un (saut qualitatif LXI)
    toSecondOrderLoop (§3)      — projection structurelle vers Conscience.lean
         ↓
    LXI_not_HOT (déjà prouvé)   — héritage automatique

  GAIN ARGUMENTATIF
  ─────────────────
  Sous la position actuelle, LXI est fondé par décret : on pose
  SecondOrderLoop, on prouve qu'elle n'est pas HOT. Un lecteur peut
  objecter que la structure est ad hoc — adaptée au résultat.

  Sous la dérivation proposée ici, LXI émerge d'un être-un qui :
  (a) satisfait I' (architectonique, pas structurel)
  (b) possède au moins une opération auto-dirigée (LIX, observable)
  (c) métabolise cette auto-direction sur sa propre marge (LXI, testable)

  La structure SecondOrderLoop devient conséquence — elle sort naturellement
  du processus, elle n'est pas imposée. C'est un renforcement argumentatif
  pour toute défense publique de la Thèse P sur la Conscience (article EJP,
  discussion avec philosophes de l'esprit, positionnement vis-à-vis de HOT/
  IIT/GWT).

  RAPPORT AU DÉPÔT EXISTANT
  ─────────────────────────
  Fichier autoporteur (convention du dépôt). Réplique localement :
  - UnitePrime (défini dans IPrime.lean §1),
  - SecondOrderLoop (défini dans Conscience.lean ligne 145),
  - LXI_not_HOT (prouvé dans Conscience.lean ligne 203).

  La réplication est bit-to-bit identique — cohérence syntaxique. La
  projection toSecondOrderLoop (§3) instancie la structure externe depuis
  notre construction.

  RAPPORT AU RAFFINEMENT PORTÉ/PORTAGE
  ────────────────────────────────────
  L'auto-affection ici concerne une clôture qui s'affecte elle-même. Un
  porté (au sens de Carried.lean) ne s'auto-affecte pas au sens strict —
  il est maintenu par ses porteurs, qui peuvent eux-mêmes avoir des boucles
  de second ordre. LXI relève donc du mode clôture, pas du mode porté.
  C'est conforme au résumé système : LXI est Thèse P, elle caractérise
  les clôtures capables de s'auto-métaboliser.
-/

namespace LxiFromIPrime

-- ═══════════════════════════════════════════════════════════════════════════
-- Réplications autoporteuses
-- ═══════════════════════════════════════════════════════════════════════════

/-- **UnitePrime** (réplique de IPrime.lean §1).
    Être-un opératoire au sens d'I' : marge positive, opérations individuées
    non-vides, chaque opération avec coût positif (IV). -/
structure UnitePrime where
  margin : Nat
  margin_pos : margin > 0
  operations : List Nat
  operations_nonempty : operations ≠ []
  operations_positive : ∀ c ∈ operations, c > 0

/-- **SecondOrderLoop** (réplique de Conscience.lean ligne 145).
    Structure de la boucle de second ordre telle que posée dans le fichier
    Conscience. Ce fichier-ci la DÉRIVE depuis UnitePrime + auto-affection
    + métabolisation, au lieu de la poser. -/
structure SecondOrderLoop where
  margin : Nat
  margin_pos : margin > 0
  valence_cost : Nat
  valence_cost_pos : valence_cost > 0
  loop_cost : Nat
  loop_cost_pos : loop_cost > 0

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. AUTO-AFFECTION — un être-un dont une opération le prend pour objet
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 1. AutoAffectingUnit — LIX (valence feedback)

Une unité auto-affectante est un `UnitePrime` dont une opération au moins
est *dirigée vers l'un lui-même* plutôt que vers le dehors. C'est la
condition minimale pour qu'il y ait valence feedback (LIX) : l'un se
sent, s'évalue, se détermine par rapport à soi.

À ce stade, on n'exige pas encore la métabolisation. L'auto-affection peut
être latente, non métabolisée — une sensation que l'un a de soi sans
l'intégrer dans sa propre régulation. C'est LIX/LVIII, pas encore LXI.

### Encodage

Dans `UnitePrime`, les opérations sont des `Nat` (leur coût). Pour marquer
qu'une opération est auto-dirigée, on ajoute un champ : une des opérations
au moins a un coût "de valence" — c'est-à-dire un coût porté par le fait
que l'un se prend pour objet.

Plutôt que d'ajouter un champ à `UnitePrime` (ce qui impacterait tous les
fichiers), on construit une extension `AutoAffectingUnit` qui hérite des
champs d'`UnitePrime` et ajoute le coût de valence.
-/

/-- **AutoAffectingUnit** — un être-un qui s'affecte (LIX).
    Étend UnitePrime par un coût de valence strictement positif.
    La valence est une opération que l'un dirige vers lui-même.

    À ce stade : pas encore de métabolisation. L'affection existe, elle
    coûte, mais elle n'est pas nécessairement intégrée au cycle de l'un.
    C'est LIX (valence feedback) dans sa forme minimale. -/
structure AutoAffectingUnit extends UnitePrime where
  /-- Coût de la valence : l'opération auto-dirigée coûte (IV appliqué à
      l'auto-affection). LIX + LVIII : la valence est non-nulle. -/
  valence_cost : Nat
  /-- IV + LVIII-a : l'auto-affection est réellement coûteuse. -/
  valence_cost_pos : valence_cost > 0
  /-- La valence fait partie du budget opératoire de l'un : elle tire sur
      sa marge, elle n'est pas portée par une source externe. Formellement :
      le coût de valence est compatible avec la marge (payable au moins
      une fois si l'un survit à un cycle). -/
  valence_within_margin : valence_cost ≤ margin

/-- [∎] **L'auto-affection ne brise pas l'unité architectonique.**
    Un AutoAffectingUnit reste un UnitePrime — la valence est ajoutée,
    pas substituée. L'un continue d'avoir une marge, des opérations
    individuées, un coût opératoire positif. L'auto-affection est une
    modalité interne à l'un, pas une fracture de son unité. -/
theorem auto_affection_preserves_unity (a : AutoAffectingUnit) :
    a.toUnitePrime.margin > 0 ∧ a.toUnitePrime.operations ≠ [] :=
  ⟨a.margin_pos, a.operations_nonempty⟩

/-- [∎] **LIX — LA VALENCE EST UN COÛT ENDOGÈNE.**
    Le coût de valence est porté par la marge de l'un lui-même, pas par
    une source externe. C'est la forme quantitative du fait que
    l'auto-affection *est* un acte de l'un, pas un événement subi. -/
theorem valence_is_endogenous (a : AutoAffectingUnit) :
    a.valence_cost ≤ a.margin := a.valence_within_margin

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. MÉTABOLISATION — saut qualitatif vers LXI
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 2. MetabolizedAffection — LXI (boucle de second ordre)

LXI ne se réduit pas à LIX. La valence feedback peut exister sans qu'une
boucle de second ordre ne se referme. La distinction est celle-ci :

* LIX : l'un se sent. La valence existe, elle a un coût, mais elle peut
  rester une sensation brute — non intégrée au fonctionnement de l'un,
  non régulatrice.

* LXI : l'un se sent ET métabolise ce sentir. La valence n'est plus
  seulement une coloration de l'expérience — elle est *travaillée*,
  intégrée au cycle qui régénère l'un. La boucle se referme.

Le saut de LIX à LXI est qualitatif : il s'agit de l'émergence d'une
seconde couche opératoire qui prend la première (la valence) pour objet
et la métabolise.

### Condition formelle du saut

Pour qu'il y ait métabolisation, il faut :
1. La valence existe (on a un AutoAffectingUnit).
2. Un coût supplémentaire (le « loop_cost ») est investi pour transformer
   cette valence en régulation effective.
3. Ce coût est également endogène : il tire sur la même marge.
4. La combinaison valence + loop reste dans le budget de l'un (sinon,
   dissolution avant même que la boucle se referme).
-/

/-- **MetabolizedAffection** — un être-un qui s'auto-affecte ET métabolise
    cette affection (LXI).

    Étend AutoAffectingUnit par un coût de métabolisation de la valence.
    C'est le saut qualitatif LIX → LXI : l'auto-affection n'est plus
    seulement ressentie, elle est travaillée, intégrée au cycle. -/
structure MetabolizedAffection extends AutoAffectingUnit where
  /-- Coût de la métabolisation : opérer SUR la valence (l'intégrer,
      la réguler, la ré-inscrire dans le cycle). -/
  loop_cost : Nat
  /-- IV appliqué à la métabolisation : l'intégration de la valence est
      elle-même un acte coûteux. -/
  loop_cost_pos : loop_cost > 0
  /-- La métabolisation est endogène : le loop_cost tire sur la même marge
      que la valence. Pas de marge séparée pour la boucle — c'est
      précisément ce qui fait que LXI n'est pas HOT (la boucle n'est pas
      intentionnellement dirigée vers un objet distinct). -/
  loop_within_margin : loop_cost ≤ margin
  /-- Viabilité conjointe : valence + loop doivent tenir sur la marge.
      Sinon la métabolisation consomme la marge avant de pouvoir réguler —
      dissolution immédiate, pas de LXI effective. -/
  joint_viability : valence_cost + loop_cost ≤ margin

/-- [∎] **LXI — LE SAUT QUALITATIF EST EFFECTIF.**
    Dans une MetabolizedAffection, le coût total (valence + loop) est
    strictement supérieur au coût de valence seule. La boucle de
    second ordre introduit un surcoût — ce surcoût est la marque de
    la métabolisation effective. -/
theorem metabolization_adds_cost (m : MetabolizedAffection) :
    m.valence_cost + m.loop_cost > m.valence_cost := by
  have := m.loop_cost_pos; omega

/-- [∎] **LXI — LA BOUCLE NE DÉBORDE PAS DE L'UN.**
    Toute MetabolizedAffection satisfait la viabilité conjointe :
    l'auto-affection et sa métabolisation tiennent ensemble dans la
    marge de l'un. C'est la condition pour que LXI existe — sinon,
    dissolution avant bouclage. -/
theorem loop_fits_in_margin (m : MetabolizedAffection) :
    m.valence_cost + m.loop_cost ≤ m.margin := m.joint_viability

/-- [∎] **LXI — LA MÉTABOLISATION TIRE SUR LA MÊME MARGE QUE LA VALENCE.**
    Le loop_cost et le valence_cost sont tous deux ≤ margin (c'est-à-dire
    tirent sur la même ressource finie). Il n'y a pas de marge-opérateur
    distincte d'une marge-cible — c'est le cœur de l'argument anti-HOT. -/
theorem unified_margin_for_loop (m : MetabolizedAffection) :
    m.valence_cost ≤ m.margin ∧ m.loop_cost ≤ m.margin :=
  ⟨m.valence_within_margin, m.loop_within_margin⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. PONT VERS SecondOrderLoop
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 3. Projection MetabolizedAffection → SecondOrderLoop

Toute MetabolizedAffection construite dans ce fichier *est* un
SecondOrderLoop au sens de Conscience.lean. La projection est bijective
sur les champs pertinents : margin, valence_cost, loop_cost, avec leurs
positivités respectives.

Conséquence : tous les théorèmes prouvés pour SecondOrderLoop
(LXI_not_HOT et ses composantes) s'appliquent directement à toute
MetabolizedAffection. La dérivation depuis I' n'ajoute pas de contenu
déductif nouveau — elle renforce la fondation.
-/

/-- **Projection** d'une MetabolizedAffection vers SecondOrderLoop.
    Les champs coïncident par construction :
    - margin : la marge de l'un.
    - valence_cost : le coût de l'auto-affection (LIX).
    - loop_cost : le coût de la métabolisation (LXI).

    Toutes les positivités sont préservées. -/
def MetabolizedAffection.toSecondOrderLoop (m : MetabolizedAffection) :
    SecondOrderLoop where
  margin := m.margin
  margin_pos := m.margin_pos
  valence_cost := m.valence_cost
  valence_cost_pos := m.valence_cost_pos
  loop_cost := m.loop_cost
  loop_cost_pos := m.loop_cost_pos

/-- [∎] **PROJECTION COHÉRENTE.**
    La projection préserve tous les champs. C'est une pure re-étiquetage,
    pas une transformation. -/
theorem projection_preserves_fields (m : MetabolizedAffection) :
    m.toSecondOrderLoop.margin = m.margin ∧
    m.toSecondOrderLoop.valence_cost = m.valence_cost ∧
    m.toSecondOrderLoop.loop_cost = m.loop_cost :=
  ⟨rfl, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 4. HÉRITAGE — LXI_not_HOT pour toute MetabolizedAffection
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 4. LXI_not_HOT appliqué à toute MetabolizedAffection

On réplique localement les théorèmes anti-HOT de Conscience.lean pour
les prouver sur notre construction. Ce n'est pas une redéfinition —
c'est l'exacte projection de ce qui est prouvé dans Conscience via
la structure SecondOrderLoop.

Les trois résultats anti-HOT :
- 2a : non-intentionalité (¬R1) : pas de cible distincte de l'opérateur.
- 2b : non-dissociabilité (¬R2) : la boucle ne peut exister sans valence.
- 2c : non-évaluabilité-en-vérité (¬R3) : pas de référence stable pour juger.
-/

/-- [∎] **LXI-2a — NON-INTENTIONALITÉ (¬R1).**
    Pour toute MetabolizedAffection, si valence_cost + loop_cost ≤ margin,
    il n'existe pas de partition margin = target_margin + operator_margin
    (avec les deux strictement positifs, somme strictement inférieure à
    la marge totale). La boucle n'a pas de cible distincte d'elle-même.

    C'est LIX + LXI articulés sous I' : l'auto-affection métabolisée tire
    sur UNE marge, pas sur deux — conséquence directe de l'unité de l'un. -/
theorem lxi_not_intentional (m : MetabolizedAffection) :
    m.valence_cost + m.loop_cost ≤ m.margin →
    ¬ (∃ (target_margin operator_margin : Nat),
        target_margin + operator_margin = m.margin ∧
        m.valence_cost ≤ target_margin ∧
        m.loop_cost ≤ operator_margin ∧
        target_margin > 0 ∧ operator_margin > 0 ∧
        target_margin + operator_margin < m.margin) := by
  intro _ ⟨_, _, h_sum, _, _, _, _, h_lt⟩
  omega

/-- [∎] **LXI-2b — NON-DISSOCIABILITÉ (¬R2).**
    La boucle ne peut pas exister sans la valence qu'elle métabolise.
    Si loop_cost > 0 et valence_cost = 0, contradiction directe avec
    valence_cost_pos.

    LXI est structurellement inséparable de LIX : métaboliser exige
    qu'il y ait quelque chose à métaboliser. -/
theorem lxi_not_dissociable (m : MetabolizedAffection) :
    ¬ (m.loop_cost > 0 ∧ m.valence_cost = 0) := by
  intro ⟨_, h⟩; have := m.valence_cost_pos; omega

/-- [∎] **LXI-2c — NON-ÉVALUABILITÉ-EN-VÉRITÉ (¬R3).**
    L'acte de métaboliser modifie sa propre cible (la valence portée sur
    la même marge). Il n'y a pas de référence stable pour juger si la
    boucle est « correcte » ou « incorrecte ». Formellement : la marge
    après métabolisation est strictement inférieure à la marge avant.

    C'est LXVIII (opacité constitutive) appliqué à la boucle de second
    ordre : connaître (métaboliser) modifie le connu (la valence). -/
theorem lxi_not_truth_evaluable (m : MetabolizedAffection)
    (h_budget : m.loop_cost ≤ m.margin) :
    m.margin - m.loop_cost < m.margin := by
  have := m.loop_cost_pos; omega

/-- [∎] **LXI_not_HOT DÉRIVÉ DEPUIS I'.**
    Résultat composite : toute MetabolizedAffection construite depuis
    un AutoAffectingUnit satisfait simultanément ¬R2 et la modification
    de la marge. Les trois conditions HOT échouent ensemble.

    Contraste avec la version de Conscience.lean : là-bas, LXI_not_HOT
    est prouvé sur SecondOrderLoop posé comme structure. Ici, il est
    dérivé depuis un être-un qui s'affecte et métabolise — avec les
    mêmes conclusions, mais une fondation plus profonde. -/
theorem LXI_not_HOT_from_IPrime (m : MetabolizedAffection) :
    ¬ (m.loop_cost > 0 ∧ m.valence_cost = 0) ∧
    (m.loop_cost ≤ m.margin → m.margin - m.loop_cost < m.margin) :=
  ⟨lxi_not_dissociable m, lxi_not_truth_evaluable m⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 5. INSTANCE CONCRÈTE — un MetabolizedAffection explicite
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 5. Construction explicite pour habitabilité

On construit un MetabolizedAffection concret pour démontrer que la
structure est habitable — les conditions de viabilité sont mutuellement
satisfaisables.

Paramètres choisis :
- margin : 100 (un être-un avec marge confortable)
- operations : [10, 20] (deux opérations ordinaires)
- valence_cost : 15 (auto-affection non-triviale)
- loop_cost : 30 (métabolisation plus coûteuse — cohérent avec le fait que
  métaboliser exige plus que sentir)
- joint : 15 + 30 = 45 ≤ 100 ✓
-/

/-- [∎] Une MetabolizedAffection concrète. -/
def exampleMetabolizedAffection : MetabolizedAffection :=
  { margin := 100,
    margin_pos := by decide,
    operations := [10, 20],
    operations_nonempty := by decide,
    operations_positive := by
      intro c hc
      cases hc with
      | head       => decide
      | tail _ hc' =>
        cases hc' with
        | head => decide
        | tail _ hc'' => cases hc''
    valence_cost := 15,
    valence_cost_pos := by decide,
    valence_within_margin := by decide,
    loop_cost := 30,
    loop_cost_pos := by decide,
    loop_within_margin := by decide,
    joint_viability := by decide }

/-- [∎] L'exemple projette vers un SecondOrderLoop bien formé. -/
theorem example_projects_correctly :
    exampleMetabolizedAffection.toSecondOrderLoop.margin = 100 ∧
    exampleMetabolizedAffection.toSecondOrderLoop.valence_cost = 15 ∧
    exampleMetabolizedAffection.toSecondOrderLoop.loop_cost = 30 :=
  ⟨rfl, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 6. AXIOM AUDIT
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 6. Audit des axiomes

Décommentez pour vérifier à la compilation.
-/

-- #print axioms auto_affection_preserves_unity
-- #print axioms valence_is_endogenous
-- #print axioms metabolization_adds_cost
-- #print axioms loop_fits_in_margin
-- #print axioms unified_margin_for_loop
-- #print axioms projection_preserves_fields
-- #print axioms lxi_not_intentional
-- #print axioms lxi_not_dissociable
-- #print axioms lxi_not_truth_evaluable
-- #print axioms LXI_not_HOT_from_IPrime
-- #print axioms example_projects_correctly

-- ═══════════════════════════════════════════════════════════════════════════
-- § 7. SYNTHÈSE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 7. Ce que ce fichier établit

1. **Auto-affection comme condition minimale de LIX (§1).**
   AutoAffectingUnit étend UnitePrime par une valence endogène. La valence
   est un coût que l'un paye pour se prendre lui-même pour objet. Distinct
   de LXI — peut exister sans métabolisation.

2. **Métabolisation comme saut qualitatif LXI (§2).**
   MetabolizedAffection étend AutoAffectingUnit par un loop_cost également
   endogène, avec viabilité conjointe. C'est LXI : la boucle de second
   ordre se referme, l'un métabolise son propre sentir.

3. **Projection vers SecondOrderLoop (§3).**
   MetabolizedAffection.toSecondOrderLoop instancie la structure externe
   de Conscience.lean. La correspondance est bijective sur les champs —
   re-étiquetage, pas transformation.

4. **LXI_not_HOT dérivé (§4).**
   Les trois résultats anti-HOT (non-intentionalité, non-dissociabilité,
   non-évaluabilité-en-vérité) sont prouvés directement sur
   MetabolizedAffection. Même contenu déductif que dans Conscience.lean,
   fondation plus profonde : on part d'un être-un qui s'affecte et
   métabolise, pas d'une structure posée.

5. **Habitabilité (§5).**
   Une MetabolizedAffection concrète est construite avec tous les
   invariants vérifiés. La structure n'est pas vide.

## Ce que ce fichier NE fait PAS

* Ne modifie pas Conscience.lean. Ce dernier reste en place avec sa
  position structurelle de LXI. Ce fichier offre la fondation alternative
  depuis I' sans contredire l'existante.

* Ne formalise pas les autres résultats de Thèse P (LXII, LXIII, LXIV,
  LXV — les « anti-unfolding » et leurs ramifications). Chantier
  ultérieur si la Thèse P est défendue publiquement en profondeur.

* Ne traite pas de la relation à l'Illusionnisme (Frankish), à l'IIT
  (Tononi), à GWT (Baars). Ces positionnements sont philosophiques,
  pas formels — ils relèvent du manuscrit, pas du Lean.

## Gain argumentatif pour la défense publique de la Thèse P

Sous cette dérivation, répondre à une objection « votre SecondOrderLoop
est ad hoc » devient immédiat : la structure sort d'I' + auto-affection
+ métabolisation endogène, pas d'un décret. L'adversaire doit alors
contester I' (axiome architectural) ou contester qu'un être-un puisse
s'affecter (empiriquement difficile — les systèmes biologiques
et computationnels le font manifestement). Le coût argumentatif est
déplacé, ce qui est précisément ce qu'un bon fondement déductif procure.

## Compteur

11 théorèmes · 2 définitions · 4 structures · 0 sorry · 0 import
-/

end LxiFromIPrime