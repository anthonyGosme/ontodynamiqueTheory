/-!
# Probe_MixedStatic.lean — sondage : le mixte statique diverge-t-il de la convention ?

## Question unique

Le corpus (`gradient.mixed_zone_is_closure`) pose PAR CONVENTION :
  profil statiquement mixte (self > 0 ∧ host > 0) → clôture.
Frontière : `self = 0`. Tout self > 0 est clôture, quelle que soit la part hôte.

La règle gloutonne (« absorber sur marge propre, externaliser le débordement »)
classe par la TRACE sous perturbation. On demande :

  une entité qui PUISE DÉJÀ en régime permanent (host_permanent > 0)
  ET régénère (self > 0) — le profil mixte du litige, l'organisme qui mange —
  est-elle classée clôture (accord avec la convention) ou portage (divergence) ?

Ce fichier ne prouve pas de théorème général. Il calcule le verdict de la règle
gloutonne sur des témoins mixtes, et le compare à la convention `= closure`.
Le résultat décide la forme du B substantiel :
  - convergence  → B = théorème de coïncidence sur trois profils.
  - divergence   → B = théorème de divergence dynamique/statique (résultat fort).

## Statut : sondage · 0 sorry · 0 import.
-/

namespace Probe

-- ── Le régime, minimal ──
inductive Regime where
  | closure | portage | aggregate
  deriving DecidableEq, Repr

-- ── La convention STATIQUE du corpus (répliquée de gradient.regimeOf) ──
--    self > 0 → closure ; sinon host > 0 → portage ; sinon aggregate.
def staticRegime (self host : Nat) : Regime :=
  if self > 0 then Regime.closure
  else if host > 0 then Regime.portage
  else Regime.aggregate

-- ── L'entité mixte statique : régénère (self) ET puise en permanence (hostPerm) ──
structure MixedEntity where
  self       : Nat   -- capacité de régénération propre (part clôture)
  hostPerm   : Nat   -- ponction permanente sur l'hôte, HORS choc (mixité statique)
  demand     : Nat   -- coût de compensation d'une perturbation

-- ── La règle GLOUTONNE, honnête sur la mixité statique ──
--    Marge propre disponible au choc = self MOINS ce qui est déjà engagé en
--    ponction permanente ? Deux lectures possibles — on les teste toutes deux.

/-- Lecture 1 : la marge d'absorption au choc est la capacité propre `self`,
    indépendamment de la ponction permanente (l'hôte permanent ne mange pas la
    marge de choc). -/
def traceRegime_indep (e : MixedEntity) : Regime :=
  if e.demand ≤ e.self then Regime.closure   -- tout absorbé sur marge propre
  else Regime.portage                        -- débordement → hôte

/-- Lecture 2 : la ponction permanente RÉDUIT la marge disponible au choc
    (l'entité mixte a déjà une partie de sa marge engagée dehors). Marge
    effective = self - hostPerm (bornée à 0). -/
def effectiveMargin (e : MixedEntity) : Nat := e.self - e.hostPerm

def traceRegime_coupled (e : MixedEntity) : Regime :=
  if e.demand ≤ effectiveMargin e then Regime.closure
  else Regime.portage

-- ═══════════════════════════════════════════════════════════════════════════
-- TÉMOINS — le cas réel : self > 0, hostPerm > 0 (mixte statique), demandes variées
-- ═══════════════════════════════════════════════════════════════════════════

/-- Organisme : régénère 5, puise 3 en permanence, choc de coût 4. -/
def organism : MixedEntity := ⟨5, 3, 4⟩

/-- La convention du corpus : mixte statique → clôture (self=5>0). -/
theorem convention_says_closure :
    staticRegime organism.self organism.hostPerm = Regime.closure := by
  unfold staticRegime organism; decide

/-- Lecture 1 (marge indépendante) : demand 4 ≤ self 5 → clôture. ACCORD. -/
theorem indep_says_closure :
    traceRegime_indep organism = Regime.closure := by
  unfold traceRegime_indep organism; decide

/-- Lecture 2 (marge couplée) : marge effective = 5-3 = 2 ; demand 4 > 2 → portage.
    DIVERGENCE avec la convention. -/
theorem coupled_says_portage :
    traceRegime_coupled organism = Regime.portage := by
  unfold traceRegime_coupled effectiveMargin organism; decide

-- ═══════════════════════════════════════════════════════════════════════════
-- LE VERDICT DU SONDAGE
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] SONDAGE — sur le MÊME organisme mixte statique, la convention du corpus
    dit CLÔTURE, la lecture couplée de la règle gloutonne dit PORTAGE.
    La divergence prédite EXISTE — et elle dépend de la lecture de la marge :
      · marge indépendante (lecture 1) : accord avec la convention ;
      · marge couplée     (lecture 2) : divergence.
    Donc la question du B substantiel se réduit à UNE décision ontologique :
    la ponction permanente mange-t-elle la marge de choc, oui ou non ? -/
theorem probe_verdict :
    staticRegime organism.self organism.hostPerm = Regime.closure
    ∧ traceRegime_indep organism = Regime.closure
    ∧ traceRegime_coupled organism = Regime.portage :=
  ⟨convention_says_closure, indep_says_closure, coupled_says_portage⟩

end Probe

/-!
## LECTURE DU SONDAGE

La divergence prédite par la critique existe, mais elle n'est pas inconditionnelle :
elle dépend d'une décision ontologique que le fichier a rendue visible plutôt que
de l'enterrer.

- Si la ponction permanente sur l'hôte **n'entame pas** la marge de choc
  (lecture 1, `traceRegime_indep`), la règle gloutonne **converge** avec la
  convention du corpus : le mixte statique est clôture. Alors B substantiel est
  un théorème de coïncidence sur les trois profils, et `mixed_zone_is_closure`
  est validé dynamiquement.

- Si la ponction permanente **réduit** la marge disponible au choc
  (lecture 2, `traceRegime_coupled`), la règle **diverge** : un organisme qui
  mange déjà beaucoup (hostPerm élevé) bascule en portage sous un choc que sa
  capacité brute `self` aurait absorbé. Alors B substantiel est un théorème de
  **divergence** dynamique/statique — le premier résultat où le modèle
  contredit une convention du corpus, et un résultat fort.

La question n'est donc plus « B converge-t-il ou diverge-t-il » (les deux, selon
la lecture) mais **« la marge de choc est-elle couplée à la ponction permanente ? »**
C'est une thèse sur ce qu'est une marge, tranchable indépendamment de B — et
c'est elle, pas un ordre de `if`, qui décide la forme du théorème central.

Intuition physique en faveur du couplage (lecture 2) : une entité qui consacre
déjà une part de sa capacité à se maintenir contre une ponction permanente a
d'autant moins de réserve pour absorber un choc. C'est cohérent avec la finitude
de la marge (IX) et avec l'idée que « exister coûte » en continu (XII). Sous cette
intuition, la divergence est réelle et B est un théorème de divergence.
-/
