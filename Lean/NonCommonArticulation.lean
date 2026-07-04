/-!
# NonCommonArticulation — Test de la voie non-commune

## Objet

Cette consigne demande de tester si l'on peut produire une articulation
formelle entre Axiome 0 (Whole) et Axiome I' (Closure) qui :

  (C1) N'utilise aucun prédicat prenant les deux comme arguments.
  (C2) N'utilise aucune typeclass commune.
  (C3) N'introduit aucune instance englobante.
  (C4) N'utilise aucun vocabulaire métaphorique partagé.
  (C5) Fait émerger le rapport comme propriété du couple, pas comme
       conséquence d'un fondement commun ni d'une dérivation.
  (C6) Auto-test honnête à chaque étape.

Trois issues possibles : A (compile, contraintes respectées),
B (échec documenté), C (compile mais triche déclarée).

## Verdict (anticipé en haut de fichier pour transparence)

**Issue B — échec documenté.**

La voie non-commune ne tient pas sous lecture stricte des contraintes.
Le verrou est la Contrainte 1 : tout énoncé qui articule Whole et
Closure doit prendre les deux comme arguments d'un prédicat ou d'un
théorème, ce qui viole C1 par définition. Les tentatives ci-dessous
documentent où et comment l'échec se produit, et ce qu'il faudrait
relâcher pour qu'une articulation existe.

Le fichier compile parce qu'il ne contient que des définitions séparées
et des observations triviales. **Aucun théorème de relation entre
Whole et Closure n'a pu être écrit sans violation.**

## Théorèmes : 4 (chacun sur un seul des deux types) · Sorry : 0 · Imports : 0
-/

namespace NonCommonArticulation

-- ═══════════════════════════════════════════════════════════════════════════
-- §A. PRIMITIVES SÉPARÉES
-- ═══════════════════════════════════════════════════════════════════════════

/-- Axiome 0 — Le Tout.

    Vocabulaire propre : auto-fondation, nécessité interne.
    Aucun champ numérique, aucun champ de coût, aucun « acte ». -/
structure Whole where
  self_grounded         : Bool
  internally_necessary  : Bool
  grounded              : self_grounded = true
  necessary             : internally_necessary = true

/-- Axiome I' — La Clôture finie.

    Vocabulaire propre : marge, drain, régénération.
    Aucun champ « fondation », aucun champ « nécessité ». -/
structure Closure where
  margin       : Nat
  drain        : Nat
  drain_pos    : drain > 0
  regenerated  : Bool

/-! ### Auto-test C1-C4 sur les primitives

  - C1 : aucun prédicat n'a été défini. ✓
  - C2 : aucune typeclass n'a été déclarée. ✓
  - C3 : aucune `inductive` à constructeurs Whole/Closure. ✓
  - C4 : `self_grounded` (Whole) ≠ `regenerated` (Closure) lexicalement.
    Pas de mot commun. ✓
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- §B. CE QU'ON VOUDRAIT POUVOIR ARTICULER (en français)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Ce qu'on voudrait dire

Quatre formulations candidates ont été examinées :

**B1.** « Les clôtures n'épuisent pas le Tout. »
    Problème : « épuiser » est un terme tiers qui se dirait des deux.
    → Violation latente de C4 (vocabulaire métaphorique partagé).

**B2.** « Le Tout n'a pas de complémentaire. »
    Problème : « complémentaire » suppose un cadre englobant.
    → Violation C3.

**B3.** « Toute clôture est partielle. »
    Pas de violation, mais ne dit rien du Tout.
    → Pas une articulation. Énoncé interne à Closure.

**B4.** « Pour tout (w : Whole) et (c : Closure), c ne sature pas w. »
    Problème : « ne sature pas » est un prédicat qui prend Whole et
    Closure comme arguments.
    → Violation C1 frontale.

**B5.** « Toute formulation qui mettrait Whole et Closure en rapport
    requiert un prédicat ou un type qui les prend tous les deux. »
    C'est la méta-observation. Elle n'est pas une articulation —
    elle est le constat que l'articulation est impossible sous C1
    en lecture stricte.

-/

-- ═══════════════════════════════════════════════════════════════════════════
-- §C. TENTATIVES FORMELLES — CHACUNE ÉCHOUE OU TRICHE
-- ═══════════════════════════════════════════════════════════════════════════

/-! ### Tentative 1 — prédicat binaire (échec C1)

On voudrait écrire :

    def saturates (w : Whole) (c : Closure) : Prop := ...

Mais cette signature même viole C1 frontalement : `saturates` prend
Whole **et** Closure comme arguments. Aucune ré-écriture ne contourne
ce point — un prédicat qui parle du rapport entre les deux *doit*
les prendre tous les deux.

On ne peut donc pas définir cette fonction sous lecture stricte de C1.
On ne l'écrit pas dans ce fichier.
-/

/-! ### Tentative 2 — curryfication (échec déguisé)

On pourrait tenter :

    def whole_property (w : Whole) : (Closure → Prop) := fun c => ...

Mais le type de retour `Closure → Prop` mentionne Closure dans la
signature de `whole_property`. La curryfication ne supprime pas la
co-occurrence des deux types — elle la cache dans le type de retour.

Lecture stricte de C1 : violation par la signature globale.
-/

/-! ### Tentative 3 — paramètre implicite (échec C3)

On pourrait tenter de poser un type tiers `Pair` qui contient les deux :

    structure Pair where
      tout : Whole
      fini : Closure

Et formuler les théorèmes sur `Pair`. Mais `Pair` est exactement une
**instance englobante** au sens de C3. Violation directe.

C'était d'ailleurs la structure `CoPosited` du fichier précédent
`Axiom0Axiom1Prime.lean` (T2c). Elle est légitime pour la consolidation
de la stratification (montrer qu'on peut co-poser sans dépendance),
mais elle viole C3 si on prétend en faire le support d'une articulation.
-/

/-! ### Tentative 4 — référence indirecte par constantes (triche C4)

On pourrait poser :

    def not_saturated_by (n : Nat) : Prop := n > 0
    -- appliqué à Closure :  not_saturated_by c.drain
    -- appliqué à Whole :    pas applicable (Whole n'a pas de Nat)

Mais ceci ne dit rien du Tout — on n'a fait que reformuler une
propriété de Closure. Comme B3 : pas une articulation.

Si on tentait de lier les deux par `not_saturated_by c.drain ∧ w.grounded`,
on aurait à nouveau un énoncé qui prend `w` et `c` comme arguments
implicites du contexte de preuve — violation C1 différée.
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- §D. CE QUI RESTE PROUVABLE — UNIQUEMENT INTERNE À CHAQUE TYPE
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## Résultats compilables

Sous lecture stricte de C1-C4, seuls des théorèmes **internes à chaque
type** sont prouvables. Ils ne constituent pas une articulation au sens
de la consigne — ils confirment seulement que les deux types sont
intelligibles séparément. -/

/-- [∎] Whole-1 — Si Whole est instancié, son auto-fondation est vraie. -/
theorem whole_self_grounded_holds (w : Whole) :
    w.self_grounded = true := w.grounded

/-- [∎] Whole-2 — Si Whole est instancié, sa nécessité interne est vraie. -/
theorem whole_internally_necessary_holds (w : Whole) :
    w.internally_necessary = true := w.necessary

/-- [∎] Closure-1 — Toute clôture a un drain strictement positif. -/
theorem closure_drain_positive (c : Closure) :
    c.drain > 0 := c.drain_pos

/-- [∎] Closure-2 — Le drain d'une clôture épuise sa marge en temps fini. -/
theorem closure_finite_exhaustion (c : Closure) :
    ∃ n, n * c.drain > c.margin := by
  refine ⟨c.margin + 1, ?_⟩
  have h1 : 1 ≤ c.drain := c.drain_pos
  have h2 : (c.margin + 1) * 1 ≤ (c.margin + 1) * c.drain :=
    Nat.mul_le_mul_left (c.margin + 1) h1
  simp only [Nat.mul_one] at h2
  omega

/-! ### Observation cruciale

Aucun des quatre théorèmes ci-dessus ne prend Whole **et** Closure comme
arguments. Chacun reste strictement interne à un type. Il n'y a donc
aucune articulation entre les deux niveaux dans ce fichier — seulement
deux discours parallèles qui ne se rencontrent jamais. -/

-- ═══════════════════════════════════════════════════════════════════════════
-- §E. DIAGNOSTIC TECHNIQUE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Pourquoi la voie non-commune échoue sous lecture stricte

Le verrou est **Contrainte 1**. Toute énonciation d'un rapport entre
deux entités requiert, en théorie des types, un prédicat ou une fonction
qui prend les deux comme arguments. Ceci est un fait formel, pas un
choix de design : un énoncé qui dit « R(w, c) » a forcément la
signature `R : Whole → Closure → Prop` (ou une équivalente curryfiée).

Les seules manières d'éviter cette signature sont :
  (i)  ne rien dire du rapport (les deux types restent isolés) — c'est
       la situation de §D ci-dessus, qui ne constitue pas une
       articulation.
  (ii) introduire un type ou une typeclass qui englobe les deux —
       violation de C2 ou C3.
  (iii) introduire un terme tiers qui se dit des deux — violation
       de C4 (et structurellement, de C5 puisqu'on aurait un opérateur
       commun).

Aucune de ces voies ne respecte les six contraintes. La voie
non-commune, sous lecture stricte, n'admet donc **aucune articulation
formelle** — seulement deux discours séparés.

## Lecture relâchée

Si l'on relâche C1 en autorisant les prédicats binaires *à condition
qu'ils ne mobilisent aucun terme tiers commun*, alors un énoncé comme
B4 (« c ne sature pas w ») devient écrivable. Mais cela revient à
remplacer C1 par une C1' plus faible. C'est une décision philosophique :
considère-t-on que la signature binaire est en soi un opérateur commun ?

  - Lecture stricte (C1 telle qu'écrite) : oui, et la voie non-commune
    est impossible.
  - Lecture relâchée (signature binaire admise sans terme tiers) : non,
    et la voie non-commune devient testable. Reste à examiner si les
    énoncés écrits dans cette lecture relâchée tiennent contre la
    critique substantiel/nominal du test croisé précédent.

Cette question — « la signature binaire est-elle déjà un opérateur
commun ? » — n'est pas tranchée par Lean. Elle est philosophique.
Elle correspond au débat entre l'autre LLM (qui dirait probablement
« oui, le simple fait de pouvoir prédiquer R(w, c) suppose un lieu
logique tiers ») et la position OD (qui pourrait soutenir que la
prédication binaire n'est pas en soi unification).

## Conclusion technique

  - Issue B confirmée sous lecture stricte de C1.
  - Issue A possible sous lecture relâchée de C1, mais nécessite de
    rejouer le test adversarial contre la critique substantiel/nominal.
  - Position 4 propre n'est pas tranchée par cette tentative — elle
    bute sur une décision métathéorique préalable (que faut-il que
    « non-commun » veuille dire ?).

## Auto-suspicion (Contrainte 6)

Points où une triche aurait pu se glisser sans que je la voie :

  (a) Les deux structures partagent le constructeur de structures Lean
      lui-même (`structure ... where`). Est-ce un opérateur commun ?
      Réponse : non, c'est de la syntaxe Lean, pas un terme du
      vocabulaire ontologique. Mais c'est limite.
  (b) Les champs `Bool` et `Nat` apparaissent dans les deux structures
      en tant que types des champs. Est-ce du vocabulaire partagé ?
      Réponse : non, ce sont des types Lean primitifs, pas des termes
      ontologiques. Mais c'est aussi limite.
  (c) Le mot `theorem` lui-même s'applique aux deux côtés. Idem :
      syntaxe Lean, pas vocabulaire ontologique.

Si l'auditeur externe considère que (a), (b), ou (c) sont déjà des
violations, alors le fichier ne tient pas même sa version restreinte.
Je signale ces points sans les résoudre.
-/

end NonCommonArticulation
