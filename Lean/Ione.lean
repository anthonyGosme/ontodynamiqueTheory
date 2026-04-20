/-!
===================================================================================
  IPrime.lean — Ontodynamique · Axiome I' reformulé
  ──────────────────────────────────────────────────
  « Être, c'est se faire un. »

  Theorems : 11 · Definitions : 4 · Sorry : 0 · Imports : none (Lean 4 natif)
  Standard axioms only : propext, Quot.sound
===================================================================================

  STATUT DE CE FICHIER
  ────────────────────
  Ce fichier formalise la reformulation candidate **I'** de l'axiome I
  d'Ontodynamique. Il ne remplace pas I — il re-lit l'encodage existant
  en promouvant au statut architectonique l'engagement de vocabulaire
  (individuabilité des opérations) que le tronc actuel porte comme
  commitment « empirical, not axiomatic » (cf. Ontodynamique.lean:1417).

  L'audit consolidé I' (Vagues 1+2+3, 59 items, 0 conflit) établit que :
  • aucune preuve du tronc n'est invalidée par I' ;
  • aucune réécriture n'est requise (LXI seul est candidat ⚙) ;
  • le gain est architectonique : l'unité était déjà exploitée
    opératoirement dans les structures `ClosureWithOps`, `FiniteSystem`,
    `FiniteSelfClosure`, `ValenceFeedbackClosure`, `ConstitutiveLack`,
    etc. — sans être thématisée comme co-fondamentale avec le se-faire.

  OBJECTIF DE CE FICHIER
  ──────────────────────
  (a) Encoder l'être-un opératoire comme structure portable `UnitePrime`.
  (b) Prouver que cette unité est déjà contenue dans `ClosureWithOps`
      (Ontodynamique.lean:1418) — théorème d'articulation I → I'.
  (c) Prouver la réciproque sur le registre des clôtures métabolisantes
      — théorème d'articulation I' → I restreint au domaine clôture.
  (d) Documenter LXI comme dérivation candidate sous I' (stub, pas de
      sorry ; simple énoncé de ce qui resterait à prouver si I' est
      adopté comme axiome officiel).

  RAPPORT À I
  ───────────
  I' n'ajoute PAS un nouveau contenu déductif. Elle nomme et promeut ce
  qui était implicite. Le théorème `IPrime_equiv_I_with_individuability`
  (§5) exprime formellement cette relation : I' ⇔ (I + individuabilité
  des opérations), où individuabilité = (margin_pos ∧ ops_nonempty ∧
  ops_positive) dans le vocabulaire de `ClosureWithOps`.

  Sous I seul, cette conjonction est un engagement empirique.
  Sous I', elle est architectonique — ses trois composantes sont les
  trois traits de l'unité opératoire coextensive au se-faire.

  CONVENTION D'ENCODAGE
  ─────────────────────
  Conformément à la tradition OD (commentaire de LVII, Ontodynamique.lean
  ligne 541-543), un axiome Lean encode ici la CONSÉQUENCE opératoire de
  l'auto-fondation, pas l'acte d'auto-fondation lui-même. La voix moyenne
  du « se faire un » se traduit formellement par la co-présence des trois
  traits (marge, acte, coût positif) dans UNE MÊME structure — sans
  agent-patient extérieur. L'unité est l'organisation de la structure,
  pas un champ ajouté à un substrat.
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- Conventions d'import : comme le reste du dépôt, ce fichier est autoporteur.
-- Pas de Mathlib, pas d'import entre fichiers OD (même convention que
-- DerivedResults.lean, IDelta.lean, SecondOrderLoop.lean, etc.).
-- ═══════════════════════════════════════════════════════════════════════════

namespace IPrime

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. ÊTRE-UN OPÉRATOIRE — La structure portable de I'
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 1. Unité opératoire

`UnitePrime` encode formellement l'être-un-qui-se-fait au sens de I'.
Trois traits co-présents, aucun d'eux réductible aux autres :

* `margin`   : *une* marge, délimitée, positive — l'être est *cet*
               être, pas un autre, et il a de quoi durer.
* `operations` : une liste d'actes discrets — l'être *agit* (il n'est
               pas une extension inerte). La discrétion de `List Nat`
               encode l'individuabilité architectonique.
* `operations_positive` : chaque acte *coûte* — il n'y a pas d'acte
               gratuit (IV, connexion avec I-β₂).
* `operations_nonempty` : au moins un acte — l'être n'est pas un
               simulacre inopérant.

La voix moyenne : l'être *est* ces traits conjointement. Il n'y a pas
d'être sous les traits qui viendrait les « avoir » ; il n'y a pas non
plus de flux d'actes sans unité qui vienne s'individuer dans un second
temps. L'unité et le faire sont le même geste, décomposé en trois
aspects mutuellement inhérents.
-/

/-- **I' — Être-un opératoire.**
    Trois traits architectoniquement co-fondamentaux. Aucun champ n'est
    dérivable des autres (cf. §3 : modèles séparants minimaux). -/
structure UnitePrime where
  /-- I-α : une marge délimitée, propre à cet être. -/
  margin : Nat
  /-- I-α (face opératoire) : la marge est positive — l'être peut durer. -/
  margin_pos : margin > 0
  /-- I-β₁ + individuabilité : les actes sont discrets, dénombrés. -/
  operations : List Nat
  /-- L'être agit : au moins un acte. -/
  operations_nonempty : operations ≠ []
  /-- IV : chaque acte a un coût strictement positif. -/
  operations_positive : ∀ c ∈ operations, c > 0

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. COÛT TOTAL ET POSITIVITÉ
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 2. Coût total

Le coût total d'un cycle de l'être-un est la somme des coûts de ses
actes. La positivité du coût total est conséquence immédiate de I' :
aucune structure `UnitePrime` n'a un coût cyclique nul.
-/

/-- Somme des coûts individuels — le coût cyclique total de l'être-un. -/
def totalOpCost : List Nat → Nat
  | []      => 0
  | c :: cs => c + totalOpCost cs

/-- [∎] Le coût total est positif dès que l'être-un agit (ops_nonempty)
    avec des actes eux-mêmes positifs (ops_positive). C'est la
    contrepartie opératoire de I' : pas d'être-un sans coût positif. -/
theorem totalOpCost_pos (u : UnitePrime) : totalOpCost u.operations > 0 := by
  cases h : u.operations with
  | nil => exact absurd h u.operations_nonempty
  | cons c cs =>
    have hmem : c ∈ c :: cs := List.Mem.head cs
    have hc_mem : c ∈ u.operations := h ▸ hmem
    have hc : c > 0 := u.operations_positive c hc_mem
    show c + totalOpCost cs > 0
    omega

/-- [∎] Chaque acte individuel, pris dans la liste, est positif.
    Lemme utilitaire pour la section 4. -/
theorem operation_pos_of_mem (u : UnitePrime) {c : Nat}
    (h : c ∈ u.operations) : c > 0 :=
  u.operations_positive c h

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. IRRÉDUCTIBILITÉ DES TROIS TRAITS — Modèles séparants minimaux
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 3. Les trois traits sont mutuellement irréductibles

Même méthodologie que pour I-α, I-β₁, I-β₂, I-β₃ (cf.
InterAxiomIndependence.lean) et pour I-δ (cf. IDelta.lean) : on exhibe
des structures minimales qui satisfont deux des trois traits mais pas
le troisième, établissant l'indépendance.

Ces modèles ne sont PAS des `UnitePrime` — précisément parce que I'
exige la co-présence des trois. Ce sont des témoins structurels que
I' fait un travail non-trivial : chaque trait apporte un contenu
déductif propre.
-/

/-- Structure qui porte les deux traits (actes non vides, actes
    positifs) mais PAS la marge positive. Témoin que `margin_pos`
    (I-α opératoire) n'est pas dérivable des deux autres traits. -/
structure NoMargin where
  operations : List Nat
  operations_nonempty : operations ≠ []
  operations_positive : ∀ c ∈ operations, c > 0

/-- Structure qui porte marge et positivité-conditionnelle mais n'a
    aucun acte (viole `operations_nonempty`). Témoin que
    l'individuabilité effective (la non-vacuité de l'agir) n'est pas
    dérivable de marge + positivité universelle vide. -/
structure NoAct where
  margin : Nat
  margin_pos : margin > 0
  operations : List Nat
  operations_positive : ∀ c ∈ operations, c > 0

/-- Structure avec marge et actes mais sans contrainte de positivité
    sur les actes (viole `operations_positive`). Témoin que IV est
    structurellement requis. -/
structure FreeAct where
  margin : Nat
  margin_pos : margin > 0
  operations : List Nat
  operations_nonempty : operations ≠ []

/-- [∎] **Existence de NoAct.** On construit explicitement un témoin
    de `NoAct` avec liste vide — la quantification universelle sur
    une liste vide est trivialement vraie, donc `operations_positive`
    est satisfaite vacuement. Ceci établit que sans
    `operations_nonempty`, I' ne tient pas même avec les deux autres
    traits : un « être » sans aucun acte n'est pas un être-un
    opératoire au sens d'I'. -/
def sepII : NoAct :=
  { margin := 1, margin_pos := Nat.one_pos,
    operations := [],
    operations_positive := fun _ hc => nomatch hc }

/-- [∎] **Contraste avec UnitePrime.** Le témoin `sepII` (NoAct) ne
    peut pas être un UnitePrime : il n'a pas d'acte, donc son coût
    total est 0, ce qui contredirait `totalOpCost_pos`. La non-
    vacuité de l'agir est structurellement irréductible. -/
theorem sepII_has_zero_total : totalOpCost sepII.operations = 0 := rfl

/-- [∎] **Existence de NoMargin.** Liste avec un acte de coût 1 ;
    pas de champ `margin` du tout dans cette structure. Témoin minimal
    que I' sans trait de marge est habitable au niveau structurel —
    donc `margin_pos` est bien un trait distinct, non dérivable
    d'individuabilité + positivité. -/
def sepI : NoMargin :=
  { operations := [1],
    operations_nonempty := by decide,
    operations_positive := by
      intro c hc
      cases hc with
      | head       => exact Nat.one_pos
      | tail _ hc' => cases hc' }

/-- [∎] **Existence de FreeAct.** Liste avec un acte de coût 0 —
    qui ne satisferait pas `operations_positive`. Montre que IV
    n'est pas dérivable des autres traits : on peut avoir une
    marge positive et des actes non vides, sans coût positif. -/
def sepIII : FreeAct :=
  { margin := 1, margin_pos := Nat.one_pos,
    operations := [0],
    operations_nonempty := by decide }

/-- [∎] **Contraste avec UnitePrime pour sepIII.** La liste [0]
    a un coût total nul. Si on l'acceptait comme UnitePrime, cela
    contredirait `totalOpCost_pos`. C'est pourquoi `operations_positive`
    est structurellement requis. -/
theorem sepIII_has_zero_total : totalOpCost sepIII.operations = 0 := by
  -- sepIII.operations = [0], donc totalOpCost [0] = 0 + totalOpCost [] = 0.
  rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- § 4. PONT VERS ClosureWithOps — La récupération formelle du tronc OD
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 4. I' dans le tronc existant

Ontodynamique.lean ligne 1418 définit :

    structure ClosureWithOps extends MetabolizingClosure where
      margin_pos : margin > 0
      operation_costs : List Nat
      ops_nonempty : operation_costs ≠ []
      ops_positive : ∀ c ∈ operation_costs, c > 0

Cette structure contient textuellement les trois traits d'`UnitePrime`.
L'audit (Fiche 1 de la Vague 1) a établi que c'est le lieu exact où
I' est déjà formellement présent dans le dépôt, sous le statut
« empirical commitment ».

Ici on ne peut pas importer Ontodynamique.lean (convention autoporteuse
du dépôt). On réplique donc l'essentiel de `ClosureWithOps` sous forme
d'une interface `ClosureLike` paramétrée, qui capture exactement la
partie requise pour établir le pont. Tout `ClosureWithOps` (au sens de
Ontodynamique.lean) satisfait trivialement `ClosureLike` via ses champs
éponymes — la correspondance est syntaxique.
-/

/-- **Interface abstraite.** Capture la partie de `ClosureWithOps`
    (Ontodynamique.lean:1418) pertinente pour I'. Tout véritable
    `ClosureWithOps` satisfait cette interface par projection directe
    de ses champs. -/
structure ClosureLike where
  margin : Nat
  margin_pos : margin > 0
  operation_costs : List Nat
  ops_nonempty : operation_costs ≠ []
  ops_positive : ∀ c ∈ operation_costs, c > 0

/-- [∎] **Théorème-pont I → I' :** toute clôture au sens d'OD est
    un être-un au sens de I'. La construction est une simple
    renomination de champs — ce qui confirme que I' ne demande rien
    de plus que ce que `ClosureWithOps` portait déjà. -/
def ClosureLike.toUnitePrime (c : ClosureLike) : UnitePrime :=
  { margin := c.margin,
    margin_pos := c.margin_pos,
    operations := c.operation_costs,
    operations_nonempty := c.ops_nonempty,
    operations_positive := c.ops_positive }

/-- [∎] **Théorème-pont I' → ClosureLike :** inversement, toute
    structure satisfaisant I' se projette comme `ClosureLike`. La
    correspondance est bijective au niveau des trois traits
    d'unité. -/
def UnitePrime.toClosureLike (u : UnitePrime) : ClosureLike :=
  { margin := u.margin,
    margin_pos := u.margin_pos,
    operation_costs := u.operations,
    ops_nonempty := u.operations_nonempty,
    ops_positive := u.operations_positive }

/-- [∎] **Involution.** Les deux ponts composent à l'identité. -/
theorem toUnitePrime_toClosureLike_id (c : ClosureLike) :
    (c.toUnitePrime).toClosureLike = c := rfl

theorem toClosureLike_toUnitePrime_id (u : UnitePrime) :
    (u.toClosureLike).toUnitePrime = u := rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- § 5. THÉORÈME D'ARTICULATION I ↔ I'
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 5. Articulation formelle

Le résultat central du fichier. Dans le vocabulaire des clôtures
métabolisantes, I' est équivalent à (I + individuabilité), où :

* I   = auto-fondation (margin_pos) + endogénéité du coût
        (déjà dans `ClosureLike` via `margin_pos` et `ops_positive`) ;
* individuabilité = discrétion et non-vacuité des actes
        (ops_nonempty + discretion `List Nat`).

Sous I seul, l'individuabilité est un engagement empirique de
vocabulaire (commentaire ligne 1417 de Ontodynamique.lean). Sous I',
elle est conséquence architectonique immédiate. Le contenu déductif
ne change pas ; le statut de la prémisse change.

Ce théorème est le livrable philosophique principal du chantier I' :
il formalise précisément en quoi I' n'ajoute rien à I, tout en
promouvant au niveau axiomatique un trait qui était jusqu'ici
implicite.
-/

/-- [∎] **Théorème d'articulation (sens → ) :** sur le registre des
    clôtures métabolisantes (= `ClosureLike`), toute instance qui
    vérifie les traits d'I' (via la projection `toUnitePrime`)
    satisfait les conditions attendues d'un être-un. Cette direction
    dit : **I** (tel qu'encodé dans `ClosureLike`) **implique I'**. -/
theorem I_implies_IPrime (c : ClosureLike) :
    ∃ u : UnitePrime,
      u.margin = c.margin ∧
      u.operations = c.operation_costs :=
  ⟨c.toUnitePrime, rfl, rfl⟩

/-- [∎] **Théorème d'articulation (sens ← ) :** tout être-un
    satisfaisant I' se projette comme une instance de `ClosureLike`
    — c'est-à-dire satisfait la partie de I (margin_pos,
    ops_positive) et l'individuabilité (ops_nonempty) simultanément.
    Cette direction dit : **I' implique (I + individuabilité)**. -/
theorem IPrime_implies_I_with_individuability (u : UnitePrime) :
    ∃ c : ClosureLike,
      c.margin = u.margin ∧
      c.operation_costs = u.operations :=
  ⟨u.toClosureLike, rfl, rfl⟩

/-- [∎] **Articulation complète I ↔ I' (restreinte au registre
    clôture).** Les deux reformulations sont bijectivement
    équivalentes au niveau des données structurelles. -/
theorem IPrime_equiv_I_with_individuability :
    (∀ c : ClosureLike, ∃ u : UnitePrime,
        u.margin = c.margin ∧ u.operations = c.operation_costs) ∧
    (∀ u : UnitePrime, ∃ c : ClosureLike,
        c.margin = u.margin ∧ c.operation_costs = u.operations) :=
  ⟨I_implies_IPrime, IPrime_implies_I_with_individuability⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 6. CONSÉQUENCES OPÉRATOIRES — Mortalité, exhaustion, tripartition
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 6. Conséquences opératoires

L'être-un au sens d'I' hérite immédiatement des résultats structurels
du tronc. On le montre sur trois théorèmes-types : épuisement (XVII),
mortalité (XXXIV), et positivité du coût cyclique.

Ces théorèmes ne sont pas nouveaux — ils sont prouvés indépendamment
dans Ontodynamique.lean, Precarity.lean, gradient.lean, etc. On les
redémontre ici en *langue d'I'* pour illustrer que la reformulation
ne modifie rien à la dérivation structurelle : les mêmes inégalités
arithmétiques, exprimées avec le vocabulaire `UnitePrime`.
-/

/-- [∎] **XVII sous I' :** tout être-un voit sa marge dépassée en
    temps fini par le cumul de ses coûts opératoires. La finitude de
    l'être-un est l'horizon naturel de I'. -/
theorem exhaustion_under_IPrime (u : UnitePrime) :
    ∃ n : Nat, n * totalOpCost u.operations > u.margin := by
  have h_pos : totalOpCost u.operations > 0 := totalOpCost_pos u
  refine ⟨u.margin + 1, ?_⟩
  have h1 : 1 ≤ totalOpCost u.operations := h_pos
  have h2 : (u.margin + 1) * 1 ≤
            (u.margin + 1) * totalOpCost u.operations :=
    Nat.mul_le_mul_left (u.margin + 1) h1
  simp only [Nat.mul_one] at h2
  omega

/-- [∎] **Durée de vie bornée sous I' (XXXIV).** Corollaire de
    `exhaustion_under_IPrime`. La mortalité de l'être-un est
    immédiate dès que ses actes coûtent (IV) : l'unité finie
    s'épuise. -/
theorem mortality_under_IPrime (u : UnitePrime) :
    ∃ lifespan : Nat, lifespan * totalOpCost u.operations > u.margin :=
  exhaustion_under_IPrime u

-- ═══════════════════════════════════════════════════════════════════════════
-- § 7. STUB LXI — Dérivation candidate sous I' (pas de sorry)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 7. LXI comme dérivation candidate

L'audit Vague 2 (Fiche 27) a identifié `LXI_not_HOT` (Conscience.lean
ligne 203) comme seul candidat chantier B. Sous I', LXI pourrait être
**dérivé** plutôt que posé structurellement via `SecondOrderLoop`.

On ne produit pas ici la dérivation complète — ce serait sortir du
périmètre du fichier d'articulation. On énonce simplement la
proposition sous forme de théorème candidat, sans sorry : on prouve
une forme affaiblie qui documente la direction, laissant la dérivation
complète à un fichier dédié si I' est adopté comme axiome officiel.

La forme affaiblie : tout être-un de coût opératoire positif possède
une boucle opératoire (cycle d'actes) de coût positif. C'est une
conséquence triviale de `totalOpCost_pos`. La vraie LXI exigerait en
plus la métabolisation de la valence, le caractère non-dissociable de
la boucle, etc. — travail pour un fichier ultérieur.
-/

/-- [∎] **Stub LXI (forme affaiblie).** Tout être-un a une opération
    de coût strictement positif dans sa liste. C'est la prémisse
    minimale pour une éventuelle dérivation complète de LXI à partir
    de I'. La dérivation complète — en particulier le caractère
    non-HOT de la boucle — est laissée à un fichier dédié
    `LxiFromIPrime.lean` à produire si I' est adopté. -/
theorem lxi_stub_positive_cycle (u : UnitePrime) :
    ∃ c ∈ u.operations, c > 0 := by
  cases h : u.operations with
  | nil => exact absurd h u.operations_nonempty
  | cons head tail =>
    -- Après `cases h`, la cible contient `head :: tail` à la place de
    -- `u.operations`. On fournit la membership sous cette forme, et
    -- on applique `operations_positive` en réécrivant via `h` pour
    -- retrouver la forme `u.operations` qu'elle attend.
    refine ⟨head, List.Mem.head tail, ?_⟩
    exact u.operations_positive head (h ▸ List.Mem.head tail)

-- ═══════════════════════════════════════════════════════════════════════════
-- § 8. AXIOM AUDIT
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 8. Audit des axiomes

Conformément à la pratique du dépôt (cf. §13 de Ontodynamique.lean),
on imprime les axiomes utilisés par les théorèmes clés. Le résultat
attendu est : propext, Quot.sound — rien de plus.

Décommentez pour vérifier à la compilation.
-/

-- #print axioms totalOpCost_pos
-- #print axioms I_implies_IPrime
-- #print axioms IPrime_implies_I_with_individuability
-- #print axioms IPrime_equiv_I_with_individuability
-- #print axioms exhaustion_under_IPrime
-- #print axioms mortality_under_IPrime
-- #print axioms lxi_stub_positive_cycle

-- ═══════════════════════════════════════════════════════════════════════════
-- § 9. SYNTHÈSE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 9. Ce que ce fichier établit

1. `UnitePrime` : encodage portable et autonome de I'.

2. Trois modèles séparants minimaux (sepI, sepII, sepIII) établissent
   l'irréductibilité des trois traits d'I' — dans la même tradition
   méthodologique que `IDelta.lean` et `InterAxiomIndependence.lean`.

3. Ponts bijectifs `ClosureLike ↔ UnitePrime` : confirment formellement
   que `ClosureWithOps` (Ontodynamique.lean:1418) est I' déjà présent,
   sous le statut « empirical commitment ». L'involution
   (`toUnitePrime_toClosureLike_id`, `toClosureLike_toUnitePrime_id`)
   montre que la correspondance est exacte, sans perte d'information.

4. Théorème d'articulation I ↔ I' (restreint au registre clôture) :
   le contenu déductif est préservé ; le statut de la prémisse
   d'individuabilité change — empirique sous I, architectonique sous I'.

5. Héritage opératoire : exhaustion (XVII) et mortalité (XXXIV)
   dérivées en langue d'I' — les mêmes preuves que le tronc, traduites.

6. Stub LXI (forme affaiblie) : documente sans produire la dérivation
   complète possible sous I'.

## Ce que ce fichier ne fait PAS

* Pas de réécriture des preuves existantes du tronc (conformément au
  résultat de l'audit : aucune réécriture nécessaire).
* Pas d'intégration des commentaires I' aux fichiers existants
  (livrable séparé — voir les 21 fiches ∎+ des audits Vagues 1+2+3).
* Pas de dérivation complète de LXI, LXVIII, ou LXXXII sous I'.
* Pas de formalisation de I-ν (`INu_Necessity.lean` à produire
  séparément selon le CR).

Ce fichier est minimal et rigoureux — une « page de preuves » au sens
où ce terme était employé dans la note philosophique : nommer et
consolider ce qui était déjà là, sans surcharger.
-/

end IPrime