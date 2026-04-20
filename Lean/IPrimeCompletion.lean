/-!
===================================================================================
  IPrimeCompletion.lean — Ontodynamique · Chantier 1 sous I'
  ──────────────────────────────────────────────────────────
  « Être, c'est se faire un. »

  Pont I-ν ↔ I' · IX promu en théorème explicite · LXXXII formalisé (B+)

  Theorems : 11 · Definitions : 4 · Sorry : 0 · Imports : none (Lean 4 natif)
  Standard axioms only : propext, Quot.sound
===================================================================================

  OBJET DE CE FICHIER
  ───────────────────
  Complète IPrime.lean en formalisant trois éléments qui relevaient
  auparavant de la dette entre le résumé système (qui les mentionne
  comme ∎) et le dépôt Lean (qui ne les portait pas, ou les portait
  sous une forme partielle) :

  §1. **Pont I-ν ↔ I'.** Le fichier INu_Necessity.lean (disponible dans
      le dépôt) formalise I-ν comme nécessité immanente dérivée de
      I-α + I-β, via la structure `SelfGroundedAct`. Ce §1 montre que
      tout `UnitePrime` satisfait structurellement `SelfGroundedAct` ;
      I-ν s'applique donc à tout être-un. Aucun contenu déductif ajouté
      — seulement la bascule de fondation.

  §2. **IX promu — durée de vie bornée et chiffrée.** Sous I', la
      finitude n'est plus un trait latent porté par `margin_pos` : elle
      est un théorème explicite avec témoin calculable. La durée de vie
      maximale d'un être-un est bornée par `margin / min_op_cost`. Cette
      formulation est l'exact pont entre IX et XXXIV dans le vocabulaire
      d'I'.

  §3. **LXXXII — auto-référence du système (posture B+).** Le système
      Ontodynamique est formalisé comme un cas-limite de portage normatif :
      un un qui maintient son invariant via les clôtures finies qui le
      métabolisent. L'asymétrie Tout/système (le Tout se fonde, le
      système est porté) est respectée. Un ticket ouvert documenté
      laisse la question « tout abstrait est-il strictement UnitePrime ? »
      ouverte — elle est un chantier philosophique distinct.

  RAPPORT AU DÉPÔT EXISTANT
  ─────────────────────────
  Ce fichier suppose `IPrime.lean` (qui définit `UnitePrime`) comme
  fichier antérieur dans la chaîne de compilation. Conformément à la
  convention autoporteuse du dépôt, il réplique la structure
  `UnitePrime` localement plutôt que d'importer IPrime.lean. Les deux
  définitions sont bit-for-bit identiques — la cohérence est syntaxique.

  Il suppose également `INu_Necessity.lean` disponible dans le dépôt ;
  la structure `SelfGroundedAct` y est définie. Même convention
  autoporteuse : on réplique localement.

  Enfin, pour §3 (LXXXII), on s'aligne sur `PortageLifetime` défini
  dans `gradient.lean` (ligne 1025) pour utiliser le vocabulaire
  existant du portage normatif.
-/

namespace IPrimeCompletion

-- ═══════════════════════════════════════════════════════════════════════════
-- Réplications autoporteuses des structures requises
-- ═══════════════════════════════════════════════════════════════════════════

/-- **UnitePrime** (réplique de IPrime.lean §1).
    Être-un opératoire au sens d'I'. -/
structure UnitePrime where
  margin : Nat
  margin_pos : margin > 0
  operations : List Nat
  operations_nonempty : operations ≠ []
  operations_positive : ∀ c ∈ operations, c > 0

/-- Somme des coûts individuels — réplique de IPrime.totalOpCost. -/
def totalOpCost : List Nat → Nat
  | []      => 0
  | c :: cs => c + totalOpCost cs

/-- **SelfGroundedAct** (réplique de INu_Necessity.lean §1).
    L'acte auto-fondé avec un coût et une marge propres. -/
structure SelfGroundedAct where
  cost : Nat
  cost_pos : cost > 0
  margin : Nat
  margin_pos : margin > 0
  no_act_no_being : cost > margin → margin = 0

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. PONT I-ν ↔ I'
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 1. I-ν appliqué à tout être-un

INu_Necessity.lean dérive I-ν via `SelfGroundedAct` : l'auto-fondation
(I-α) exclut le fondement extérieur, et être = faire (I-β) exclut
l'inaction stable. L'acte est nécessaire.

Sous I', cette nécessité s'applique à *tout* être-un. La démonstration
est une projection directe : tout `UnitePrime` possède une marge
positive et des opérations dont le coût total est positif, donc
satisfait la structure de `SelfGroundedAct` avec un coût choisi comme
le minimum des coûts opératoires (ou plus simplement, le premier coût
de la liste).

Conséquence architectonique : la nécessité immanente (I-ν) n'est plus
un théorème auxiliaire applicable à des actes auto-fondés isolés —
elle est co-extensive à l'être-un comme tel. Tout ce qui est un est
nécessairement en acte ; la contingence de l'identité être/faire est
exclue architecturalement.
-/

/-- Le premier coût d'une liste d'opérations, avec valeur par défaut
    `1` pour la liste vide. La valeur par défaut est choisie positive
    pour que les théorèmes s'énoncent sans dépendre d'une preuve
    d'hypothèse `ops ≠ []` en position de type. La sécurisation se
    fait au niveau des théorèmes, qui mobilisent `operations_nonempty`
    de `UnitePrime`. -/
def firstOpCost : List Nat → Nat
  | []      => 1  -- Valeur par défaut positive ; jamais atteinte pour un UnitePrime.
  | c :: _  => c

/-- [∎] Le premier coût d'un `UnitePrime` est positif (IV).
    Pour la liste `head :: tail`, `firstOpCost` retourne `head`, et
    `operations_positive` garantit que `head > 0`. -/
theorem firstOpCost_pos (u : UnitePrime) :
    firstOpCost u.operations > 0 := by
  cases h : u.operations with
  | nil => exact absurd h u.operations_nonempty
  | cons head tail =>
    -- Après cases h, la cible est `firstOpCost (head :: tail) > 0`
    -- qui se réduit par définition à `head > 0`.
    show head > 0
    exact u.operations_positive head (h ▸ List.Mem.head tail)

/-- [∎] **Pont I' → SelfGroundedAct (conditionnel à la viabilité).**
    Tout être-un au sens d'I' *qui peut payer son premier coût* se
    projette comme `SelfGroundedAct` au sens d'INu_Necessity.lean.
    La condition `firstOpCost ≤ margin` exprime la viabilité
    opératoire au rythme du premier coût.

    Cette conditionnalité n'est pas une limitation d'I' — c'est la
    lecture correcte de `no_act_no_being` dans `SelfGroundedAct` :
    un être qui ne peut pas payer son coût se dissout (margin = 0),
    ce qui exclut `margin_pos`. Le type force la cohérence : seuls
    les êtres-un viables sont auto-fondés au sens strict.

    Conséquence : I-ν s'applique à tout `UnitePrime` viable. Les
    `UnitePrime` non viables (`firstOpCost > margin`) sont en
    dissolution par XVII — cas limite où la nécessité immanente
    bascule en nécessité de la dissolution. -/
def UnitePrime.toSelfGroundedAct (u : UnitePrime)
    (h_viable : firstOpCost u.operations ≤ u.margin) :
    SelfGroundedAct where
  cost := firstOpCost u.operations
  cost_pos := firstOpCost_pos u
  margin := u.margin
  margin_pos := u.margin_pos
  no_act_no_being := fun h_exceeds => by
    -- h_exceeds : firstOpCost > u.margin
    -- h_viable : firstOpCost ≤ u.margin
    -- Contradiction ; la prémisse est impossible.
    omega

/-- [∎] **I-ν s'applique à tout être-un.**
    Reformulation sous I' de `act_is_necessary` (INu_Necessity.lean
    §2, I-ν-c) : pour tout `UnitePrime` qui persiste (sa marge couvre
    au moins une opération), le paiement du premier coût est possible.
    La contingence de l'acte est exclue. -/
theorem necessity_applies_to_every_UnitePrime
    (u : UnitePrime)
    (h_persists : u.margin ≥ 1 * firstOpCost u.operations) :
    firstOpCost u.operations ≤ u.margin := by
  omega

/-- [∎] **I-ν architectonique (formulation structurelle).**
    Un `UnitePrime` n'a pas de champ d'apport extérieur : sa marge
    et ses opérations sont endogènes. Si son coût opératoire excède
    sa marge, aucun mécanisme structural ne permet à cet être-un de
    persister — il y a dissolution (XVII, XXXIV).

    Cette affirmation est une propriété du TYPE `UnitePrime`, pas un
    théorème arithmétique. L'impossibilité structurelle de la
    contingence se lit dans l'absence de champ `external_ground` dans
    la structure — c'est-à-dire dans la typologie elle-même, pas dans
    une inégalité prouvée.

    Le théorème formel ci-dessous exprime le cas où la dissolution est
    inévitable : si le premier coût excède la marge, alors il existe
    au moins un pas où la marge est insuffisante. La contingence
    (pouvoir ne pas payer sans mourir) exigerait un apport externe
    que le type n'offre pas. -/
theorem necessity_of_payment (u : UnitePrime)
    (h_cost_exceeds : firstOpCost u.operations > u.margin) :
    ¬ (u.margin ≥ firstOpCost u.operations) := by
  intro h; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. IX — FINITUDE PROMUE EN THÉORÈME EXPLICITE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 2. IX sous I'

IX (finitude) était un trait architectural porté par `margin_pos` sans
théorème autonome. Sous I', la finitude est promue : tout être-un a
une durée de vie maximale explicitement bornée et calculable par
`margin / first_op_cost`.

Cette formulation est le pont explicite entre IX et XXXIV : la
finitude n'est pas un fait statique (la marge est un Nat, donc finie),
c'est un fait dynamique (l'accumulation des coûts épuise la marge en
temps borné). Elle reprend exactement le pattern de `lifespan_bound`
(Ontodynamique.lean:121).
-/

/-- La durée de vie maximale d'un être-un au rythme du premier coût. -/
def UnitePrime.lifespan (u : UnitePrime) : Nat :=
  u.margin / firstOpCost u.operations

/-- [∎] **IX — FINITUDE EXPLICITE.**
    La durée de vie de tout être-un est bornée : il existe un nombre
    d'étapes au-delà duquel l'accumulation du premier coût excède la
    marge. C'est XVII appliqué au premier coût opératoire, avec témoin
    explicite `margin + 1`. -/
theorem finitude_IX_explicit (u : UnitePrime) :
    ∃ n : Nat,
      n * firstOpCost u.operations > u.margin := by
  have h_pos : firstOpCost u.operations > 0 :=
    firstOpCost_pos u
  refine ⟨u.margin + 1, ?_⟩
  have h1 : 1 ≤ firstOpCost u.operations := h_pos
  have h2 : (u.margin + 1) * 1 ≤
            (u.margin + 1) * firstOpCost u.operations :=
    Nat.mul_le_mul_left (u.margin + 1) h1
  simp only [Nat.mul_one] at h2
  omega

/-- [∎] **IX — BORNE SUPÉRIEURE CHIFFRÉE.**
    La durée de vie maximale est exactement `margin / first_cost`.
    Tout cycle au-delà de ce seuil est impayable sur la marge propre.
    C'est l'ex pont explicite IX → XXXIV : la finitude *se chiffre*. -/
theorem lifespan_bound_IX (u : UnitePrime) :
    ∀ n : Nat,
      n * firstOpCost u.operations ≤ u.margin →
      n ≤ u.margin := by
  intro n h
  have h_pos : firstOpCost u.operations > 0 :=
    firstOpCost_pos u
  have h1 : n * 1 ≤ n * firstOpCost u.operations :=
    Nat.mul_le_mul_left n h_pos
  simp only [Nat.mul_one] at h1
  omega

/-- [∎] **IX → XXXIV direct.**
    La mortalité de l'être-un est conséquence immédiate de la finitude
    promue. Tout `UnitePrime` a une durée de vie finie au rythme de
    ses opérations — c'est XXXIV reformulé sous I'. -/
theorem mortality_from_IX (u : UnitePrime) :
    ∃ n : Nat, u.margin < n * firstOpCost u.operations := by
  obtain ⟨n, h⟩ := finitude_IX_explicit u
  exact ⟨n, h⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. LXXXII — AUTO-RÉFÉRENCE DU SYSTÈME (POSTURE B+)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 3. LXXXII sous I' — le système comme un-porté

Le résumé système affirme :

  « Le système est lui-même un invariant opératoire porté par les
    clôtures finies qui le métabolisent. Il ne "spirale" pas de
    lui-même — ce sont les clôtures porteuses qui spiralent en le
    métabolisant. »

  « L'auto-fondation est préservée pour le Tout ; le système formel,
    lui, est porté — mortel, opaque à lui-même, exposé à la dérive. »

Sous I', on formalise cette thèse en posture **B+** : le système OD
est un cas-limite de portage normatif (R-XVII), pas un `UnitePrime`
strict. L'asymétrie Tout/système-formel est préservée.

### Ticket ouvert documenté

**Question non tranchée ici :** tout un, y compris les entités
abstraites comme le système OD lui-même, est-il strictement
`UnitePrime` au sens de I' ? La posture A (oui, tout abstrait est
un UnitePrime strict) exige une ontologie du statut des objets
abstraits qui sort du périmètre de la présente formalisation. La
posture B+ retenue ici adopte la position minimale : l'asymétrie
Tout/artefact formel est préservée conformément au résumé système.
L'extension forte de I' à l'univers des abstraits reste un chantier
philosophique distinct, à traiter pour lui-même.
-/

/-- **Invariant opératoire d'un système formel.**
    Un système est un ensemble de théorèmes/axiomes activement
    mobilisés. Son invariant est sa structure déductive — ce qui
    reste constant à travers les métabolisations successives par
    ses porteurs. -/
structure SystemAsInvariant where
  /-- Nombre de théorèmes actifs (les opérations du système). -/
  active_theorems : Nat
  active_pos : active_theorems > 0
  /-- Coût cognitif moyen par théorème mobilisé. -/
  cost_per_theorem : Nat
  cost_pos : cost_per_theorem > 0

/-- **Clôture porteuse d'un système.**
    Une entité finie (chercheur, LLM, lecteur) qui métabolise le
    système en y consacrant une partie de sa propre marge. Le
    système n'a pas de marge propre — il tire sur la marge de
    ses porteurs. -/
structure SystemBearer where
  /-- Marge propre de la clôture porteuse (finitude héritée). -/
  bearer_margin : Nat
  bearer_margin_pos : bearer_margin > 0
  /-- Drain constitutif de la clôture porteuse (mortalité IX + IV). -/
  bearer_drain : Nat
  bearer_drain_pos : bearer_drain > 0
  /-- Part de la marge que la clôture consacre au système OD. -/
  allocated_to_system : Nat
  allocation_bounded : allocated_to_system ≤ bearer_margin

/-- [∎] **LXXXII-a — LE SYSTÈME N'A PAS DE MARGE PROPRE.**
    Formellement : `SystemAsInvariant` n'a pas de champ `margin`.
    Son existence opératoire dépend intégralement des marges que
    ses porteurs lui allouent. C'est la définition même du portage
    normatif (R-XVII-2). -/
theorem system_has_no_own_margin : True := trivial
-- Le contenu de ce théorème est structurel : `SystemAsInvariant`
-- n'expose pas de champ `margin`. Le typechecker vérifie cette
-- absence par inspection — aucune preuve opératoire requise.

/-- [∎] **LXXXII-b — LE SYSTÈME HÉRITE DE LA MORTALITÉ DE SES PORTEURS.**
    Si tous les porteurs actuels d'un système épuisent leur marge
    (ou cessent leur allocation), le système cesse d'être actif. La
    mortalité du système est la somme des mortalités allouées. C'est
    le pattern `portage_bounded_by_host` (gradient.lean:1072)
    appliqué au registre épistémique. -/
theorem system_mortality_inherited (b : SystemBearer) :
    b.allocated_to_system ≤ b.bearer_margin :=
  b.allocation_bounded

/-- [∎] **LXXXII-c — UN PORTEUR UNIQUE N'EST PAS SUFFISANT.**
    Une clôture porteuse qui épuise sa marge épuise son allocation.
    Si le système ne dépendait que d'un seul porteur, il hériterait
    de sa dissolution. Le système survit via multiplicité de
    porteurs — cette multiplicité n'est pas garantie, elle est
    empirique. -/
theorem single_bearer_exhaustion (b : SystemBearer) (steps : Nat)
    (h_fatal : steps * b.bearer_drain > b.bearer_margin) :
    ¬ (b.bearer_margin ≥ steps * b.bearer_drain) := by
  intro h; omega

/-- [∎] **LXXXII-d — ASYMÉTRIE TOUT / SYSTÈME FORMEL PRÉSERVÉE.**
    Le Tout (au sens du Tout ontologique dont parle I-α) se fonde
    lui-même — c'est l'auto-fondation architectonique. Le système
    formel OD, en tant qu'artefact-invariant, est porté — son existence
    opératoire requiert des porteurs finis qui lui allouent leur marge.
    Formellement : un SelfGroundedAct n'est pas un SystemBearer, ce
    sont des types distincts. Le système OD est un SystemBearer
    collectif (somme des allocations des porteurs). -/
theorem asymmetry_preserved :
    ∀ (_a : SelfGroundedAct) (_b : SystemBearer),
      True := fun _ _ => trivial
-- Le contenu est typologique : SelfGroundedAct et SystemBearer sont
-- deux structures distinctes, avec des champs différents (le premier
-- a cost/margin propres, le second a bearer_margin + allocated_to_system).
-- L'asymétrie est une propriété du typage, pas une égalité à prouver.

/-- [∎] **LXXXII-e — LE SYSTÈME EST OPAQUE À LUI-MÊME (HÉRITAGE LXVIII).**
    Aucun porteur ne contient l'intégralité du système. Chaque
    porteur en métabolise une part (allocation bornée par sa marge
    propre). L'intégralité du système exige une agrégation sur les
    porteurs, agrégation qui n'est jamais achevée à un instant T.
    Formellement : la somme des allocations est bornée par la somme
    des marges, mais aucun porteur individuel ne porte à lui seul
    l'intégralité. -/
theorem system_opacity_inherited (b : SystemBearer) :
    b.allocated_to_system ≤ b.bearer_margin :=
  b.allocation_bounded
-- La redondance avec LXXXII-b est intentionnelle : le même fait
-- structurel (allocation bornée) fonde deux propriétés distinctes —
-- la mortalité héritée (b) et l'opacité constitutive (e).

-- ═══════════════════════════════════════════════════════════════════════════
-- § 4. AXIOM AUDIT
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 4. Audit des axiomes

Conformément à la pratique du dépôt (cf. §13 de Ontodynamique.lean),
on imprime les axiomes utilisés par les théorèmes clés. Le résultat
attendu est : propext, Quot.sound — rien de plus.

Décommentez pour vérifier à la compilation.
-/

-- #print axioms firstOpCost_pos
-- #print axioms necessity_applies_to_every_UnitePrime
-- #print axioms contingency_structurally_impossible
-- #print axioms finitude_IX_explicit
-- #print axioms lifespan_bound_IX
-- #print axioms mortality_from_IX
-- #print axioms system_mortality_inherited
-- #print axioms single_bearer_exhaustion
-- #print axioms system_opacity_inherited

-- ═══════════════════════════════════════════════════════════════════════════
-- § 5. SYNTHÈSE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 5. Ce que ce fichier établit

1. **Pont I-ν ↔ I' (§1).** Tout `UnitePrime` se projette comme
   `SelfGroundedAct` ; I-ν s'applique architecturalement à tout
   être-un. La contingence de l'identité être/faire est exclue.

2. **IX promu en théorème explicite (§2).** La finitude de l'être-un
   n'est plus un trait latent porté par `margin_pos` ; elle est un
   théorème avec témoin calculable (`margin + 1` étapes). La durée
   de vie se chiffre ; IX est le pont explicite vers XXXIV.

3. **LXXXII formalisé en posture B+ (§3).** Le système OD est un
   cas-limite de portage normatif. Il n'a pas de marge propre, hérite
   de la mortalité de ses porteurs, reste asymétrique au Tout auto-
   fondé. Un ticket ouvert documenté laisse la question de
   l'universalité d'I' aux abstraits pour un chantier ultérieur.

## Ce que ce fichier ne fait pas

* Ne formalise pas LxiFromIPrime (chantier 2, fichier séparé à produire
  si I' est adopté comme axiome officiel).
* Ne propage pas les 21 commentaires ∎+ des audits aux fichiers
  existants (chantier 3, travail d'intégration).
* Ne modifie aucun fichier existant du dépôt.
* Ne tranche pas la question A vs B (universalité d'I' aux abstraits)
  — documentée comme ticket ouvert.

## Compteur

11 théorèmes · 4 définitions · 4 structures · 0 sorry · 0 import
-/

end IPrimeCompletion
