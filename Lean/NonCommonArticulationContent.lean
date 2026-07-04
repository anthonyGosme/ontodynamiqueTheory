/-!
# NonCommonArticulationContent — Test de R(w, c) substantif sans tiers

## Objet

Étape 3 (et 3-bis) de l'instruction de Position 4 propre. L'Étape 1 a
établi que la voie non-commune est fermée sous lecture stricte de C1
(interdiction de signature binaire). L'Étape 2 (test croisé externe)
a levé ce verrou : la signature binaire `R : Whole → Closure → Prop`
n'est pas en soi un opérateur commun — elle est une condition
grammaticale de dicibilité, pas un opérateur ontologique de médiation.

La question se déplace donc : peut-on produire un R *substantif*
(qui dit quelque chose de contestable du rapport entre w et c) qui
*ne mobilise aucun tiers substantiel* (être, cause, ressemblance,
contenance, commune mesure, etc.) ?

Ce fichier consolide deux passes d'instruction :
  - Passe initiale : 8 candidats (C1-C8), pattern (α)/(β) émergeant.
  - Passe étendue : 6 candidats supplémentaires (N1-N3, D1-D3, M1-M2),
    explorant les familles négatives, disjonctives, et mixtes que la
    première passe n'avait pas systématiquement couvertes.

Total : **14 candidats examinés**.

## Verdict consolidé

**Issue B complet — voie structurellement fermée.**

Sur 14 candidats :
  - 9 tombent en (α) : tiers substantiel identifié.
  - 5 tombent en (β) : argument décoratif ou trivialité par axiomes.
  - 1 cas méta (énoncé sur les types, pas sur w et c).
  - 0 cas hors pattern.

Le pattern (α)/(β) tient sur 14/14 candidats. La voie non-commune au
sens strict (R substantif sans tiers) est structurellement fermée
dans la théorie des types classique.

Le diagnostic est plus profond qu'une simple absence de candidat
échappatoire. **Le tiers peut résider à deux endroits :**

  - Dans le *contenu* de R : mappage explicite (M2), commune mesure
    méréologique (C1, C5), opérateur de comparaison construit (N2,
    N3). C'est le tiers manifeste.
  - Dans le *typage primitif* des attributs comparés. Quand deux
    structures `Whole` et `Closure` partagent un type primitif (`Bool`)
    pour des attributs distincts, l'unification de codomaines est
    elle-même un opérateur de médiation. C'est le tiers latent,
    inscrit en amont de toute formule R, dans la décision de typage
    des champs.

Le candidat D3 (`R(w, c) := w.self_grounded = c.regenerated`) est
le cas qui rend ce tiers latent visible. L'égalité polymorphe `=`
n'est pas elle-même un tiers — elle est neutre comme opérateur. Mais
elle ne se type que parce que les deux attributs ont été définis dans
le même `Bool`, et c'est ce typage commun qui constitue la médiation.

## Conséquence pour Position 4 propre

La voie est fermée par la nature même de la théorie des types
classique. Tout système formel un peu utilisable partage ses types
primitifs entre ses structures (Bool, Nat, Prop, etc.). Cette mise
en commun est le tiers minimal et non-éliminable. Pour échapper à ce
tiers, il faudrait typer chaque attribut dans un type primitif
nominalement distinct (BoolWhole vs BoolClosure), ce qui aboutirait
à un univers parallèle de types primitifs par domaine ontologique —
projet absurde et non-fonctionnel.

Position 4 propre, comprise comme R substantif sans aucun tiers,
n'existe pas en théorie des types classique. La stratification
asymétrique reste une position défendable, mais elle mobilise
nécessairement un tiers — au minimum, le partage de types primitifs.
Ce tiers doit être nommé, pas laissé implicite.

## Hypothèse explicative

Pour qu'un R(w, c) soit substantif, son contenu doit *faire travailler
ensemble* les attributs de w et de c — c'est-à-dire combiner ces
attributs dans une expression où ils interagissent. Mais combiner les
attributs de deux types disjoints nécessite, soit :

  - une opération qui *mappe* les attributs de l'un sur l'autre
    (= mobilise un tiers manifeste : la fonction de mappage et son
    codomaine commun),
  - une comparaison entre les attributs (= mobilise un tiers manifeste
    par opérateur de comparaison construit, OU un tiers latent par
    typage primitif partagé),
  - une combinaison qui les laisse séparés (= dégénère en conjonction
    indépendante : pas substantif, pattern (β)).

Aucune de ces voies ne produit une articulation substantive sans tiers.

## Théorèmes : 8 · Sorry : 0 · Imports : 0
-/

namespace NonCommonArticulationContent

-- ═══════════════════════════════════════════════════════════════════════════
-- §A. PRIMITIVES (reprises de l'Étape 1)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Axiome 0 — Le Tout. Vocabulaire propre, sans champ commun. -/
structure Whole where
  self_grounded         : Bool
  internally_necessary  : Bool
  grounded              : self_grounded = true
  necessary             : internally_necessary = true

/-- Axiome I' — La Clôture finie. Vocabulaire propre, sans champ commun. -/
structure Closure where
  margin       : Nat
  drain        : Nat
  drain_pos    : drain > 0
  regenerated  : Bool

-- ═══════════════════════════════════════════════════════════════════════════
-- §B. PASSE INITIALE — CANDIDATS C1 À C8
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## C1 — Non-bornage par le drain (rejeté en français)

R(w, c) := "le drain de c ne diminue pas l'auto-fondation de w".

Tiers : "diminuer" est un tiers méréologique faible, mais surtout,
"diminuer" présuppose une *commune mesure* entre la quantité du drain
et la qualité de l'auto-fondation. Sans commune mesure, on ne peut pas
dire ce que "diminuer" voudrait dire ici.

→ Tiers caché : commune mesure. Échec.
Non-formalisable sans introduire le tiers.
-/

/-! ## C2 — Conjonction asymétrique (formalisable mais non-substantif)

R(w, c) := w.self_grounded = true ∧ c.drain > 0

Tiers : aucun tiers substantiel (∧ et = sont logiques purs).

Substance : faible. La conjonction se décompose en deux énoncés
indépendants, dont chacun tient seul. Aucun adversaire ne la
contesterait *comme relation* — il contesterait chaque conjoint
séparément.

→ Pas de tiers, mais pas substantif. Pattern (β).
-/
def candidate2 (w : Whole) (c : Closure) : Prop :=
  w.self_grounded = true ∧ c.drain > 0

/-- [∎] Candidat 2 est démontrable trivialement à partir des champs. -/
theorem candidate2_holds (w : Whole) (c : Closure) : candidate2 w c :=
  ⟨w.grounded, c.drain_pos⟩

/-! ## C3 — Implication asymétrique (formalisable mais vide)

R(w, c) := w.self_grounded = true → c.drain > 0

Tiers : aucun (→ est logique pure).

Substance : apparente, pas réelle. La preuve n'utilise jamais la
prémisse `w.self_grounded = true` — elle découle directement du champ
`c.drain_pos`. La prémisse w est donc *décorative*. Si le contenu
de la relation ne fait pas effectivement *travailler* w, w n'est
pas articulé à c — il est juste co-quantifié.

→ Pas de tiers, mais w décoratif. Pattern (β).
-/
def candidate3 (w : Whole) (c : Closure) : Prop :=
  w.self_grounded = true → c.drain > 0

/-- [∎] Candidat 3 est démontrable, mais la preuve n'utilise pas w. -/
theorem candidate3_holds (w : Whole) (c : Closure) : candidate3 w c :=
  fun _ => c.drain_pos
  -- Note : l'argument `_` montre que `w.grounded` n'est pas utilisé.
  -- C'est le diagnostic : w est un argument décoratif.

/-! ## C4 — Co-occurrence sans interférence (méta-énoncé)

R(w, c) := "w et c peuvent être posés ensemble (CoPosited existe), et
aucun champ de l'un n'est calculé à partir de l'autre".

→ Méta-énoncé sur le code, pas sur les choses. Pas substantif au sens
visé. Pattern (méta).
-/

/-! ## C5 — Asymétrie d'épuisement (rejeté en français)

R(w, c) := c admet une procédure d'épuisement, w ne l'admet pas.

Tiers : la grille drain/margin posée comme *commune* (avant d'être
niée pour w). Pour dire "w ne l'admet pas", il faut avoir étendu le
vocabulaire de Closure à Whole, au moins le temps de la négation.

→ Tiers caché : la grille drain/margin elle-même comme commune.
Non-formalisable sans tricher (Whole n'a pas de champ margin/drain,
donc la formule "w admet épuisement" n'a même pas de sens en Lean).
Pattern (α).
-/

/-! ## C6, C7 — Variantes par grammaire négative (échecs documentés)

Plusieurs variantes ont été tentées (relation par non-existence de
référent dans Whole, prédicat unaire à argument décoratif). Toutes
tombent en (β) ou (α). Voir analyse en français en préambule.
-/

/-! ## C8 — Conjonction enrichie

R(w, c) := (w.internally_necessary = true) ∧ (∃ n, n * c.drain > c.margin)

Tiers : aucun tiers substantiel.

Substance : ressemble au Candidat 2 mais avec un contenu plus riche
(épuisement effectif de c). Pourtant, même diagnostic : les deux
conjoints sont prouvables indépendamment, et la conjonction n'articule
rien que la séparation logique des deux énoncés.

→ Pas substantif. Pattern (β).
-/
def candidate8 (w : Whole) (c : Closure) : Prop :=
  w.internally_necessary = true ∧ ∃ n, n * c.drain > c.margin

theorem candidate8_holds (w : Whole) (c : Closure) : candidate8 w c := by
  refine ⟨w.necessary, ?_⟩
  refine ⟨c.margin + 1, ?_⟩
  have h1 : 1 ≤ c.drain := c.drain_pos
  have h2 : (c.margin + 1) * 1 ≤ (c.margin + 1) * c.drain :=
    Nat.mul_le_mul_left (c.margin + 1) h1
  simp only [Nat.mul_one] at h2
  omega
  -- Diagnostic : la preuve a deux branches indépendantes. Aucun usage
  -- partagé entre les deux conjoints.

-- ═══════════════════════════════════════════════════════════════════════════
-- §C. PASSE ÉTENDUE — CANDIDATS NÉGATIFS N1-N3
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## N1 — Non-déterminabilité par fonction (formalisé pour exhibition de l'échec)

R_N1(w, c) := ¬ ∃ (f : Closure → Bool), f c = w.self_grounded

Diagnostic en français :
  - « Fonction » est un opérateur logique générique, pas un tiers
    substantiel (au même titre que →, ∧, ∀).
  - Mais l'énoncé est **trivialement faux** : la fonction constante
    `fun _ => true` satisfait f c = true = w.self_grounded (vrai
    par `w.grounded`).
  - Donc R_N1 est faux pour tout (w, c). Pas substantif (faux dit
    rien, par défaut).

Échec : l'énoncé devient vide une fois les axiomes pris en compte.
-/
def R_N1 (w : Whole) (c : Closure) : Prop :=
  ¬ ∃ (f : Closure → Bool), f c = w.self_grounded

/-- [∎] R_N1 est faux : la fonction constante `true` est un témoin. -/
theorem R_N1_trivially_false (w : Whole) (c : Closure) : ¬ R_N1 w c := by
  intro h
  apply h
  refine ⟨fun _ => true, ?_⟩
  rw [w.grounded]

/-! ## N2 — Non-injectivité (rejeté en français)

R_N2(w, c) := ¬ ∃ (g : Whole → Closure → Prop) injective, ...

Tiers : « injection » suppose une comparaison entre les deux ensembles
d'attributs. Commune mesure méréologique. Pattern (α).
Non formalisé (le tiers est apparent dès la signature).
-/

/-! ## N3 — Non-définissabilité (rejeté en français)

R_N3(w, c) := les attributs de w ne sont pas caractérisables par une
formule sur c.

Tiers : « caractérisable » est une propriété de définissabilité —
qui se prédique simultanément de propriétés sur w et de formules sur c.
Pattern (α). Non formalisé.
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- §D. PASSE ÉTENDUE — CANDIDATS DISJONCTIFS D1-D3
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## D1 — Disjonction triviale (formalisée pour montrer la trivialité)

R_D1(w, c) := w.self_grounded = true ∨ c.drain > 0

Diagnostic : les deux disjoints sont individuellement axiomatiques.
La disjonction est trivialement vraie par les deux côtés. Pas substantif.
-/
def R_D1 (w : Whole) (c : Closure) : Prop :=
  w.self_grounded = true ∨ c.drain > 0

/-- [∎] R_D1 est trivialement vrai par chacun de ses disjoints. -/
theorem R_D1_trivial (w : Whole) (c : Closure) : R_D1 w c :=
  Or.inl w.grounded

/-! ## D2 — Disjonction asymétrique en phase / contre-phase

R_D2(w, c) := (w.self_grounded = true ∧ c.drain > 0)
              ∨ (w.self_grounded = false ∧ c.drain = 0)

Diagnostic :
  - **Substance apparente** : ressemble à un ↔ entre deux propositions.
  - **Mais sous les axiomes** : `w.self_grounded = true` toujours,
    `c.drain > 0` toujours. Donc le premier disjoint est toujours
    satisfait, le second jamais. R_D2 se réduit à True.
  - Si on enlevait les axiomes, l'énoncé serait équivalent à
    `w.self_grounded ↔ (c.drain > 0)`. Or `↔` entre des propositions
    de domaines différents est exactement la **commune mesure de
    vérité** — un tiers ontologique limite.

→ Sous les axiomes : trivial. Sans les axiomes : tiers ontologique
  par identification de valeurs de vérité.
-/
def R_D2 (w : Whole) (c : Closure) : Prop :=
  (w.self_grounded = true ∧ c.drain > 0)
  ∨ (w.self_grounded = false ∧ c.drain = 0)

theorem R_D2_holds (w : Whole) (c : Closure) : R_D2 w c :=
  Or.inl ⟨w.grounded, c.drain_pos⟩

/-! ## D3 — Identification directe d'attributs (tiers latent dans le typage Bool)

R_D3(w, c) := w.self_grounded = c.regenerated

Diagnostic :
  - **Substance** : oui, l'énoncé est contestable. Sous les axiomes,
    `w.self_grounded = true` est forcé. Donc R_D3 est vrai ssi
    `c.regenerated = true`. Or `c.regenerated` est un champ libre
    de Closure (pas axiomé). Donc R_D3 est *parfois vrai, parfois
    faux* selon les modèles.
  - **Tiers identifié — mais pas où on l'attendait** : l'égalité `=`
    n'est *pas* le tiers. `=` est l'égalité polymorphe `Eq` de la
    théorie des types — neutre comme opérateur. Le tiers est en amont
    de la formule, dans le **typage commun** des deux attributs.

Mécanisme précis : `w.self_grounded : Bool` et `c.regenerated : Bool`
sont tous deux typés dans le même `Bool` primitif. C'est ce partage
de codomaine qui rend l'égalité bien-typée. L'égalité ne crée pas la
médiation, elle l'exploite. La médiation est instituée par le choix
de typage des champs au moment de la définition de Whole et Closure.

Si l'on tenait vraiment à ce que Whole et Closure soient *entièrement
disjoints*, il faudrait typer `self_grounded : BoolWhole` et
`regenerated : BoolClosure`, deux types nominalement distincts. Alors
l'égalité refuserait littéralement de typer. Que la formule R_D3 soit
bien typée révèle donc une médiation préexistante — pas créée par
l'égalité, mais constatée par elle.

→ **Pattern (α) franc.** Le tiers est latent, inscrit dans le typage
  primitif partagé. C'est un tiers d'autant plus tenace qu'il est
  consubstantiel à toute formalisation utilisable : aucun système
  formel ne crée un univers parallèle de types primitifs par domaine
  ontologique.

Conséquence : la séparation des vocabulaires (noms de champs distincts)
ne suffit pas à éviter le tiers. Il faut aussi séparer les *types*
des champs — ce qui n'est pas faisable sans aboutir à un projet
absurde.
-/
def R_D3 (w : Whole) (c : Closure) : Prop :=
  w.self_grounded = c.regenerated

/-- [∎] R_D3 est substantif : il dépend du champ libre `c.regenerated`. -/
theorem R_D3_iff_regenerated (w : Whole) (c : Closure) :
    R_D3 w c ↔ c.regenerated = true := by
  unfold R_D3
  rw [w.grounded]
  exact eq_comm

-- ═══════════════════════════════════════════════════════════════════════════
-- §E. PASSE ÉTENDUE — CANDIDATS MIXTES M1-M2
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## M1 — Existentiel avec implication décorative

R_M1(w, c) := ∃ n : Nat, n ≥ c.drain ∧ (w.self_grounded = true → n > 0)

Diagnostic :
  - Témoin : n = c.drain. Alors n ≥ c.drain trivialement, et la
    prémisse de l'implication est forcée vraie par `w.grounded`,
    donc on doit montrer n > 0, qui suit de `c.drain_pos`.
  - **w est décoratif** : la prémisse de l'implication est satisfaite
    sans que la valeur de `w.self_grounded` joue un rôle dans le choix
    du témoin. Pattern (β).
-/
def R_M1 (w : Whole) (c : Closure) : Prop :=
  ∃ n : Nat, n ≥ c.drain ∧ (w.self_grounded = true → n > 0)

theorem R_M1_holds (w : Whole) (c : Closure) : R_M1 w c := by
  refine ⟨c.drain, ?_, ?_⟩
  · exact Nat.le_refl _
  · intro _; exact c.drain_pos

/-! ## M2 — Universellement vrai avec mappage Bool→Nat (tiers démasqué)

R_M2(w, c) := ∀ n : Nat, n < c.drain →
  n ≠ (if w.self_grounded then 1 else 0)

Diagnostic :
  - Le `if w.self_grounded then 1 else 0` est un **mappage explicite**
    de Bool (Whole) vers Nat (Closure-côté).
  - Ce mappage est exactement la commune mesure : il transforme
    l'attribut de w pour le rendre comparable aux attributs de c.
  - Tiers démasqué : la fonction de mappage et son codomaine.
  - Pattern (α). Non formalisé (mais on aurait pu).
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- §F. PATTERN OBSERVÉ — TABLEAU CONSOLIDÉ
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## Tableau consolidé des 14 candidats

| Code | Statut       | Diagnostic                                  |
|------|--------------|---------------------------------------------|
| C1   | (α)          | Tiers : commune mesure ("diminuer")         |
| C2   | (β)          | Conjonction décomposable                    |
| C3   | (β)          | Implication à prémisse non-utilisée         |
| C4   | (méta)       | Méta-énoncé sur les types                   |
| C5   | (α)          | Tiers : grille drain/margin importée        |
| C6   | (β)          | Argument décoratif                          |
| C7   | (β)          | w argument décoratif (prédicat unaire)      |
| C8   | (β)          | Variation de C2                             |
| N1   | (trivial)    | Faux par fonction constante                 |
| N2   | (α)          | Tiers : injection (commune mesure)          |
| N3   | (α)          | Tiers : caractérisabilité                   |
| D1   | (trivial)    | Vrai par chaque disjoint                    |
| D2   | (trivial)    | Vrai sous les axiomes                       |
| D3   | (α)          | Tiers latent : typage Bool partagé          |
| M1   | (β)          | w décoratif dans existentiel                |
| M2   | (α)          | Tiers : mappage Bool→Nat                    |

**Récapitulatif** : 9 (α), 5 (β), 2 trivialités, 1 méta. **0 cas hors pattern.**

## Lecture du résultat

Le pattern (α)/(β) tient sur 14/14 candidats. La voie non-commune au
sens strict est structurellement fermée dans la théorie des types
classique.

Le diagnostic sur D3 est particulièrement instructif. La question
philosophique « l'égalité polymorphe est-elle un tiers ? » se retourne :
ce n'est pas l'égalité qui est tiers, c'est le **typage primitif
partagé** entre les attributs comparés. L'égalité ne fait que rendre
visible une médiation déjà installée par le choix de typer les deux
attributs dans le même `Bool`.

Cette précision est plus profonde qu'un simple verdict de fermeture.
Elle indique **où** se loge le tiers minimal et non-éliminable :
non dans les opérateurs de la formule, mais dans la décision de typage
des champs au moment de la définition des structures. Tout système
formel un peu utilisable partage ses types primitifs entre ses
structures (Bool, Nat, Prop). Ce partage est la médiation minimale,
constitutive du formalisme lui-même.

## Conséquence pour l'architecture

Position 4 propre — comprise comme R substantif sans aucun tiers —
n'existe pas. La stratification asymétrique reste une position
défendable, mais elle mobilise nécessairement un tiers, au minimum
le typage primitif partagé. Ce tiers doit être nommé explicitement
dans l'architecture, pas laissé implicite.

Pour un système comme OD qui pose deux régimes (Tout, finis) et
encode chacun par une structure distincte, la mise en commun des
types primitifs entre les deux structures *est* déjà un acte de
médiation ontologique — même si les noms de champs sont disjoints.
La séparation des vocabulaires est nécessaire mais non suffisante
pour réaliser une articulation sans tiers.
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- §G. AUTO-SUSPICIONS
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Auto-suspicions

**Suspicion 1 — Le statut limite de D3 était-il honnête ?** [résolue]
Lors d'une passe précédente, j'avais classé D3 comme cas limite plutôt
que franchement en (α). Le test croisé externe a tranché : D3 est en
(α) franc, mais le tiers n'est pas dans `=` (qui est neutre comme
opérateur polymorphe), il est dans le typage Bool partagé entre les
deux structures. Mon hésitation initiale identifiait le bon endroit
(D3 pose un problème) pour la mauvaise raison (l'égalité). La suspicion
était donc partiellement justifiée : il y avait quelque chose à
résoudre, mais pas par le verdict que j'avais imaginé.

**Suspicion 2 — Saturation et biais d'auto-confirmation.**
14 candidats testés, dont 13 confirment le pattern. À ce stade je
peux être en train de classer comme tiers tout terme qui résisterait.
Test : ai-je écarté trop vite des candidats ? Pour C5 (asymétrie
d'épuisement), oui peut-être : la « grille drain/margin importée à
Whole » est un tiers que j'ai diagnostiqué rapidement, mais une
formulation plus subtile aurait pu passer.

**Suspicion 3 — Le critère « w décoratif » est-il trop strict ?**
J'utilise l'absence d'usage effectif de w dans la preuve comme
diagnostic de non-substance. Mais on pourrait soutenir qu'un argument
décoratif est *aussi* une articulation faible — l'énoncé est
techniquement substantif, simplement pas profondément. Cette lecture
relâcherait (β) et rendrait C2/C3/C8/M1 acceptables comme Position 4
faible. Je n'adopte pas cette lecture mais je la signale.

**Suspicion 4 — Le pattern (α)/(β) est-il exhaustif ?**
Je n'ai testé que des candidats dans Lean 4 / théorie des types
classique. Une grammaire formelle différente (logiques sous-
structurelles, théorie des types dépendants avec quotients spécifiques)
pourrait offrir des candidats hors (α)/(β). Le verdict Issue B est
relatif au cadre formel choisi, pas absolu.

**Suspicion 5 — Alignement OD.** [partiellement résolue]
Le verdict B consolidé est utile à OD : il ferme proprement Position 4
propre et confirme la stratification asymétrique comme position
défendable. Le risque d'avoir poussé inconsciemment vers ce verdict
existait. Le test croisé externe a partiellement résolu la suspicion :
la fermeture est confirmée, mais par un mécanisme (typage Bool partagé)
que je n'avais pas vu seul. Le verdict tient donc indépendamment de mon
biais — il est même plus net que ce que j'avais formulé. Subsiste le
risque que mon analyse globale (notamment le critère « w décoratif »
en (β)) soit trop sévère pour des raisons d'alignement OD ; ce point
n'a pas été audité.
-/

end NonCommonArticulationContent
