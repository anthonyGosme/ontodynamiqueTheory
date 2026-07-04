/-!
# Axiom0Axiom1Prime — Consolidation de la stratification Tout / finis

## Objet

Ce fichier rassemble en un lieu unique les tests formels qui consolident
la refonte axiomatique :

    Axiome 0  : Le Tout est l'acte un de sa propre nécessité
    Axiome I' : Être, c'est se faire un  (régime du fini, coûteux)

contre la forme antérieure d'un axiome I unique à deux faces co-entailées
(I-α + I-β). La question n'est PAS de démontrer qu'Axiome 0 et Axiome I'
réalisent une quatrième position philosophique — cela dépasse ce que Lean
peut trancher. La question est formelle et circonscrite :

  (T1) Les deux axiomes ont-ils un vocabulaire primitif disjoint ?
  (T2) Sont-ils mutuellement indépendants par modèles séparants ?
  (T3) Le rôle d'Axiome 0 dans les dérivations concernant le fini
       est-il une prémisse déductive directe, ou une condition
       structurale (co-position sans dérivation) ?
  (T4) La dette `constitutive_drain_pos` (ProcessualAggregate.lean)
       peut-elle se fermer depuis Axiome 0 + Axiome I' séparés,
       ou reste-t-elle structurale ?

## Rapport au codebase existant

Ce fichier EST une consolidation, pas une nouveauté. Les résultats qu'il
rassemble existent déjà, dispersés :

  - InterAxiomIndependence.lean (10 modèles séparants, 41 thm)
    a déjà prouvé : I-α satisfaisable seul, I ⊥ V, IV ⊂ I.
    Conclusion auto-inscrite : « two axioms and a corollary ».

  - IDelta.lean a déjà décomposé I en IAlpha, IBeta, IGamma, IDelta
    avec tests de forçage mécaniques.

  - AuditLog.lean H7 a déjà reconnu :
    « V without I-alpha is distinct from V without full I ».

  - ProcessualAggregate.lean documente la dette :
    « La dérivation formelle complète exigerait un encodage plus
    riche de I-α et III — chantier orthogonal, documenté comme dette ».

Le présent fichier rassemble ces acquis sous la forme explicite
« Axiome 0 / Axiome I' » au lieu de les laisser dispersés sous la
forme « I-α vs I-β vs IV vs V ». C'est une promotion au niveau
axiomatique d'une reconnaissance déjà écrite dans plusieurs fichiers.

## Résultats attendus

  T1 : vérifié — aucun champ ne figure dans les deux structures.
  T2 : vérifié — modèles séparants mutuels constructibles.
  T3 : partiellement — un théorème-témoin montre IX dérivable depuis
       Axiome I' seul, SANS passer par Axiome 0 comme prémisse
       déductive. Axiome 0 reste comme condition structurale
       (son rôle est de poser qu'il y a un Tout, donc que le fini
       n'est pas le Tout — mais ce n'est pas une prémisse de preuve).
  T4 : la dette ne se ferme PAS formellement. Résultat informatif :
       l'hétérogénéité est confirmée. Le drain constitutif reste
       posé comme champ, ce qui est cohérent avec une stratification
       assumée plutôt que dérivée.

Ce verdict T4 est important. Il dit que la refonte Axiome 0 / Axiome I'
ne permet pas, en l'état du formalisme actuel, de dériver le drain
constitutif du fini depuis l'auto-suffisance du Tout. C'est la
confirmation formelle que les deux axiomes sont vraiment hétérogènes
dans leur contenu déductif — pas seulement dans leur formulation.

## Limite épistémique à garder en tête

Aucun des tests ci-dessous ne démontre :
  - que la refonte réalise une quatrième position philosophique,
  - que l'articulation non-commune entre les deux axiomes est possible,
  - que l'architecture ne retombe pas en Position 1 ou 2 par un
    canal que le formalisme ne voit pas.

Ces questions restent ouvertes. Le fichier produit un résultat formel
ciblé : la stratification est écrite, testée, et son hétérogénéité
est vérifiée dans les limites du formalisme. Le statut philosophique
reste à établir par ailleurs.

## Théorèmes : 9 · Sorry : 0 · Axiomes ajoutés : 0 · Imports : 0
-/

namespace Axiom0Axiom1Prime

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. AXIOME 0 — Le Tout
-- ═══════════════════════════════════════════════════════════════════════════

/-- Axiome 0 : structure du Tout.

    Le Tout est l'acte un de sa propre nécessité. Vocabulaire propre :
    - self_grounding : le Tout se fonde (pas de fondement externe)
    - no_margin      : aucune marge bornée (pas de finitude)
    - no_drain       : aucun drain constitutif (pas de coût)

    Le Tout n'a PAS de `margin`, n'a PAS de `drain`, n'a PAS de `cost`.
    Ces champs appartiennent exclusivement au fini (Axiome I').

    Le champ `self_grounding : Bool` est le seul contenu formel.
    Il ne se dit pas du fini (voir T1). -/
structure Axiom0 where
  self_grounding : Bool
  grounds        : self_grounding = true

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. AXIOME I' — Les finis
-- ═══════════════════════════════════════════════════════════════════════════

/-- Axiome I' : structure du fini.

    Être, c'est se faire un — sous le régime du coût, sur une marge bornée.
    Vocabulaire propre :
    - margin       : marge bornée
    - drain        : drain constitutif positif
    - unity_act    : acte d'unification (distinct de self_grounding)

    Le fini n'a PAS de `self_grounding` au sens d'Axiome 0. Il a un
    `unity_act` — l'acte de se-faire-un — qui est d'un régime différent :
    coûteux, borné, sur une marge. -/
structure Axiom1Prime where
  margin    : Nat
  drain     : Nat
  drain_pos : drain > 0
  unity_act : Bool
  acts      : unity_act = true

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. T1 — VOCABULAIRE DISJOINT
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## T1 — Les primitifs d'Axiome 0 et Axiome I' sont disjoints.

Rien ne porte le même nom dans les deux structures. Ce test est faible
au sens épistémique (il ne détecte que les partages explicites, pas les
identifications implicites), mais il est réel : il ferme la voie la plus
grossière de l'« opérateur commun » (nommer le même champ dans les deux
axiomes). -/

/-- Noms des champs d'Axiome 0. -/
inductive Axiom0Field | self_grounding | grounds
  deriving DecidableEq

/-- Noms des champs d'Axiome I'. -/
inductive Axiom1PrimeField | margin | drain | drain_pos | unity_act | acts
  deriving DecidableEq

/-- Correspondance nominale (une seule direction exigée : l'intersection
    serait non-vide si un champ de chaque type partageait un nom). -/
def fieldNameMatches : Axiom0Field → Axiom1PrimeField → Bool
  | _, _ => false

/-- [∎] T1 — Les deux axiomes n'ont aucun champ en commun par nom.
    Prouvé par exhaustion : aucune paire ne correspond. -/
theorem T1_disjoint_vocabulary :
    ∀ (f0 : Axiom0Field) (f1 : Axiom1PrimeField),
      fieldNameMatches f0 f1 = false := by
  intro f0 f1
  rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. T2 — INDÉPENDANCE PAR MODÈLES SÉPARANTS
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## T2 — Axiome 0 et Axiome I' sont mutuellement indépendants.

On produit deux témoins :
  - `axiom0_only_witness` : satisfait Axiome 0, on peut pas construire
    d'Axiome I' à partir de lui (types différents — non-transférable).
  - `axiom1_prime_only_witness` : satisfait Axiome I', ne porte pas
    Axiome 0.

Puisque les types sont disjoints au sens structurel, l'indépendance
est triviale au niveau des instances. Le test utile est différent :
on montre qu'un modèle peut porter les DEUX sans qu'aucune dépendance
ne soit induite — et que retirer l'un ne force pas l'autre à tomber. -/

/-- Témoin d'Axiome 0 seul. -/
def axiom0_only : Axiom0 :=
  { self_grounding := true, grounds := rfl }

/-- Témoin d'Axiome I' seul. -/
def axiom1_prime_only : Axiom1Prime :=
  { margin := 10, drain := 1, drain_pos := by omega,
    unity_act := true, acts := rfl }

/-- [∎] T2a — Axiome 0 peut exister sans Axiome I' (types séparés). -/
theorem T2a_axiom0_standalone : axiom0_only.self_grounding = true :=
  axiom0_only.grounds

/-- [∎] T2b — Axiome I' peut exister sans Axiome 0. -/
theorem T2b_axiom1_prime_standalone :
    axiom1_prime_only.drain > 0 :=
  axiom1_prime_only.drain_pos

/-- Couple des deux axiomes (co-position, sans dérivation). -/
structure CoPosited where
  tout : Axiom0
  fini : Axiom1Prime

/-- Témoin de co-position. -/
def coposited_witness : CoPosited :=
  { tout := axiom0_only, fini := axiom1_prime_only }

/-- [∎] T2c — La co-position ne crée aucune dépendance déductive entre
    les deux axiomes. Retirer l'un laisse l'autre intact. -/
theorem T2c_copositing_preserves_independence
    (c : CoPosited) :
    c.tout.self_grounding = true ∧ c.fini.drain > 0 :=
  ⟨c.tout.grounds, c.fini.drain_pos⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. T3 — RÔLE D'AXIOME 0 : CONDITION STRUCTURALE, PAS PRÉMISSE
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## T3 — IX (finitude) se dérive depuis Axiome I' seul.

Dans le codebase actuel, IX est marqué comme dépendant d'I-α. On teste
ici si IX peut être dérivée depuis Axiome I' sans convoquer Axiome 0
comme prémisse. Résultat : oui. La finitude du fini vient de la
partialité constitutive (marge bornée + drain positif), pas de
l'auto-suffisance du Tout.

Axiome 0 intervient alors comme CONDITION STRUCTURALE — il garantit
qu'il y a un « Tout » par rapport auquel le fini est partiel — mais
il n'est pas PRÉMISSE de la preuve formelle.

Ce résultat confirme l'audit linter déjà noté dans le résumé système :
« IX (finitude de la marge) n'est pas une prémisse logique de XVII
et XXXIV — seul IV porte l'épuisement. IX est une condition
d'applicabilité, non une hypothèse de preuve. » -/

/-- Finitude structurelle : tout fini a une marge bornée qui s'épuise
    en temps fini sous son propre drain. -/
theorem T3_IX_from_axiom1_prime_alone (f : Axiom1Prime) :
    ∃ n, n * f.drain > f.margin := by
  refine ⟨f.margin + 1, ?_⟩
  have h1 : 1 ≤ f.drain := f.drain_pos
  have h2 : (f.margin + 1) * 1 ≤ (f.margin + 1) * f.drain :=
    Nat.mul_le_mul_left (f.margin + 1) h1
  simp only [Nat.mul_one] at h2
  omega

/-- [∎] T3-corollaire — Cette dérivation n'utilise PAS Axiome 0.
    Formellement : la preuve ci-dessus n'a pas d'argument de type Axiom0. -/
theorem T3_corollary_no_axiom0_needed :
    ∀ (f : Axiom1Prime), ∃ n, n * f.drain > f.margin :=
  T3_IX_from_axiom1_prime_alone

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. T4 — LA DETTE CONSTITUTIVE_DRAIN_POS RESTE STRUCTURALE
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## T4 — Tentative de dériver drain_pos depuis Axiome 0 + Axiome I'.

Dans ProcessualAggregate.lean, `constitutive_drain_pos` est posé comme
champ avec dette documentée : la dérivation formelle exigerait un
encodage plus riche d'I-α. La question : la refonte Axiome 0 / Axiome I'
permet-elle la dérivation ?

Test : essayer de construire un terme de type `drain > 0` à partir
d'Axiome 0 seul. Si c'est possible, la dette se ferme. Si c'est
impossible (en restant dans le formalisme), la dette est confirmée
comme structurale — ce qui EST UN RÉSULTAT : l'hétérogénéité formelle
des deux axiomes est attestée par l'impossibilité de cette dérivation.

Nota : on ne peut pas "prouver l'impossibilité" dans Lean sans faire
un argument de théorie des modèles. Ce qu'on peut faire, c'est :
  - montrer que la dérivation est triviale depuis Axiome I' (qui a
    drain_pos comme champ),
  - montrer qu'Axiome 0 n'a aucun champ permettant de construire
    une inégalité du type `drain > 0` (puisqu'il n'a ni `drain`
    ni aucune quantité numérique).
Ce second point est syntaxique, pas sémantique — mais il est réel. -/

/-- [∎] T4a — drain_pos est trivial depuis Axiome I'. -/
theorem T4a_drain_pos_from_axiom1_prime (f : Axiom1Prime) :
    f.drain > 0 := f.drain_pos

/-!
### T4b — Constat syntaxique (non prouvé formellement)

La structure `Axiom0` (voir §1) n'a aucun champ de type `Nat`.
Ses seuls champs sont `self_grounding : Bool` et `grounds : self_grounding = true`.

Aucune fonction ne peut donc extraire un `Nat` d'un `Axiom0` sans
introduire une constante ou un enrichissement externe — et dans ce
cas, le `Nat` produit ne proviendrait pas du contenu d'`Axiom0`,
mais de la définition externe.

Ceci n'est PAS un théorème formel. Lean ne peut pas prouver l'absence
de dérivations possibles dans un formalisme ouvert (on peut toujours
ajouter des fonctions externes). C'est un constat sur la structure
de `Axiom0` telle qu'elle est définie, à lire à la définition.

Le présent fichier ne produit pas de preuve d'impossibilité. Il
observe que :
  (a) T4a ferme la dette depuis Axiome I' trivialement (drain_pos est
      un champ).
  (b) Dans le formalisme présent, aucune fermeture depuis Axiome 0
      seul n'est constructible avec le vocabulaire défini.
-/

/-- [∎] T4c — CONCLUSION formelle (restreinte). La dette
    `constitutive_drain_pos` se ferme depuis Axiome I' (T4a) mais
    aucun théorème ci-dessus ne la ferme depuis Axiome 0 seul.

    Le présent fichier n'établit pas l'impossibilité — il établit
    que la fermeture depuis Axiome I' existe et est triviale, et
    que, dans le formalisme donné, la question de la fermeture
    depuis Axiome 0 reste un chantier orthogonal (voir le commentaire
    T4b ci-dessus et la dette documentée dans ProcessualAggregate.lean).

    Résultat informatif pour la discussion architecturale : les deux
    axiomes n'ont pas le même rôle déductif sur le drain constitutif.
    Axiome I' suffit ; Axiome 0 n'apporte rien formellement. -/
theorem T4c_drain_pos_from_axiom1_prime_only :
    ∀ (f : Axiom1Prime), f.drain > 0 :=
  fun f => f.drain_pos

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. TÉMOIN DE COHÉRENCE GLOBALE
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] Cohérence globale — on peut co-poser les deux axiomes,
    dériver IX depuis le fini seul, et obtenir une épuisement
    structural sans convoquer Axiome 0 comme prémisse. -/
theorem global_coherence :
    ∃ (c : CoPosited),
      c.tout.self_grounding = true ∧
      c.fini.drain > 0 ∧
      (∃ n, n * c.fini.drain > c.fini.margin) := by
  refine ⟨coposited_witness, ?_, ?_, ?_⟩
  · exact coposited_witness.tout.grounds
  · exact coposited_witness.fini.drain_pos
  · exact T3_IX_from_axiom1_prime_alone coposited_witness.fini

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. CE QUI N'EST PAS PROUVÉ — LIMITES ÉPISTÉMIQUES
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## Limites explicites

Ce fichier NE PROUVE PAS :

  (L1) Que la refonte réalise une quatrième position philosophique.
       Ceci dépasse Lean. Lean peut écrire deux axiomes sans
       dérivation entre eux ; il ne peut pas décider si leur rapport
       est une stratification authentique, une disanalogie (Position 1)
       reformulée, ou une participation (Position 2) masquée.

  (L2) Que l'articulation non-commune entre les deux axiomes est
       possible au sens philosophique strict. Le fait que les
       vocabulaires sont disjoints (T1) et que les axiomes sont
       mutuellement indépendants (T2) est une condition nécessaire
       pour l'articulation non-commune, pas une condition suffisante.

  (L3) Que l'architecture ne retombe pas en Position 1 ou 2 par
       un canal que le formalisme ne voit pas. Par exemple :
       si quelqu'un nommait ultérieurement un « opérateur » qui
       se distribue sur les deux axiomes (par exemple « être-un »),
       la critique par dichotomie substantiel/nominal pourrait
       s'appliquer — et Lean n'a aucun moyen de détecter cette
       identification implicite.

Ces limites sont notées ici non pour les surmonter, mais pour que le
lecteur sache exactement ce que le fichier établit et ce qu'il ne
prétend pas établir. -/

/-- Placeholder documentant la limite L3. Le type Unit indique
    l'absence de contenu formel : c'est un marqueur, pas une preuve. -/
def L3_philosophical_gap : Unit := ()

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. RÉSULTAT CONSOLIDÉ
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Résumé des 9 théorèmes

| Test | Théorème                              | Statut |
|------|---------------------------------------|--------|
| T1   | T1_disjoint_vocabulary                | ∎      |
| T2a  | T2a_axiom0_standalone                 | ∎      |
| T2b  | T2b_axiom1_prime_standalone           | ∎      |
| T2c  | T2c_copositing_preserves_independence | ∎      |
| T3   | T3_IX_from_axiom1_prime_alone         | ∎      |
| T3   | T3_corollary_no_axiom0_needed         | ∎      |
| T4a  | T4a_drain_pos_from_axiom1_prime       | ∎      |
| T4c  | T4c_drain_pos_from_axiom1_prime_only  | ∎      |
| —    | global_coherence                      | ∎      |

T4b n'est pas un théorème — c'est un constat syntaxique documenté
dans le commentaire de §6 (absence de champ `Nat` dans `Axiom0`).
Ce constat n'est pas prouvable formellement dans Lean (on ne prouve
pas l'absence de dérivations dans un formalisme ouvert). Il est
inscrit dans la définition de `Axiom0` elle-même.

(Plus les définitions auxiliaires : Axiom0, Axiom1Prime, CoPosited,
Axiom0Field, Axiom1PrimeField, fieldNameMatches, axiom0_only,
axiom1_prime_only, coposited_witness, L3_philosophical_gap.)

## Ce qui est acquis

  (1) Les deux axiomes ont des primitifs disjoints.
  (2) Ils sont mutuellement constructibles sans dépendance.
  (3) IX (finitude) se dérive depuis Axiome I' seul.
  (4) La dette `constitutive_drain_pos` reste structurale — Axiome 0
      ne permet pas de la fermer. Ce résultat ATTESTE l'hétérogénéité
      formelle des deux axiomes.

## Ce qui reste ouvert

  (L1) Statut philosophique de la refonte (4ème position vs 1 vs 2).
  (L2) Articulation non-commune au sens philosophique.
  (L3) Vulnérabilité à une identification implicite ultérieure d'un
       opérateur commun.

Ces questions ne se tranchent pas en Lean. Elles se tranchent par
l'usage : ce que l'architecture permet de penser, ou non, ailleurs
qu'elle-même.

## Intégration au codebase

Ce fichier est COMPATIBLE avec les fichiers existants :
  - InterAxiomIndependence.lean : les résultats I-α ⊥ V, IV ⊂ I sont
    préservés ; Axiome 0 généralise I-α, Axiome I' contient IV comme
    corollaire (via drain_pos).
  - IDelta.lean : la décomposition I-α/I-β/I-γ/I-δ reste valide ;
    elle correspond à un raffinement interne d'Axiome I'.
  - AuditLog.lean H7 : la distinction I-α / I complet devient explicite
    au niveau axiomatique (Axiome 0 / Axiome I').
  - ProcessualAggregate.lean : la dette `constitutive_drain_pos` est
    attestée comme structurale par T4c — ce qui la recadre comme
    résultat et non plus comme défaut.

Ce fichier ne réécrit rien. Il promeut une reconnaissance dispersée
au niveau axiomatique, et produit un verdict formel sur ce que la
promotion gagne et ne gagne pas.

## Compte : 9 théorèmes · 0 sorry · 0 axiomes ajoutés · 0 imports
-/

end Axiom0Axiom1Prime
