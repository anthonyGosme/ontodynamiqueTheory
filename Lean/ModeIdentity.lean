/-!
# ModeIdentity.lean — M1 et M2 : l'identité des modes et l'espace des modes

## Place dans le chantier

`ModeFlux.lean` a livré M3 (le mode détermine le profil économique) avant M1 et
M2. Ce fichier ferme la marche arrière :

  M1 — IDENTITÉ : deux entités sont le même mode ssi elles sont indiscernables
       par leur réponse au choc (bisimulation de coût). Théorème : cette
       équivalence a un INVARIANT COMPLET — la marge de choc. Le mode d'une
       entité finie EST sa marge : un seul nombre, ce qui lui reste.

  M2 — ESPACE : l'espace des modes est exactement ℕ (toute marge est réalisée,
       deux marges distinctes sont deux modes distincts). La pluralité des
       modes — pendante depuis le tour 2 — est DÉRIVÉE, pas posée : il y a une
       infinité de modes, y compris une infinité INTRA-régime (des clôtures de
       marges différentes sont des modes distincts). Le mode de marge 0 est un
       fond distingué : l'exsangue, qui ne peut jamais être clôture.

## Réplique (autoportant, fidélité vérifiable à la main)
`Regime`, `Entity`, `netLoad`, `shockMargin`, `dynamicRegime` : répliqués à
l'identique de `ModeFlux.lean` (§1–§4), y compris la correction du cas
dégénéré (`demand = 0 → aggregate`).

## Statut : 16 théorèmes · 0 sorry · 0 import (Lean 4 core).
-/

namespace ModeIdentity

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. RÉPLIQUE DE ModeFlux (§1–§4)
-- ═══════════════════════════════════════════════════════════════════════════

inductive Regime where
  | closure | portage | aggregate
  deriving DecidableEq, Repr

structure Entity where
  self        : Nat
  ownCost     : Nat
  ownCost_pos : ownCost > 0
  hostInflow  : Nat
  outflow     : Nat

def netLoad (e : Entity) : Nat := (e.ownCost + e.outflow) - e.hostInflow

def shockMargin (e : Entity) : Nat := e.self - netLoad e

def dynamicRegime (e : Entity) (demand : Nat) : Regime :=
  if demand = 0 then Regime.aggregate
  else if demand ≤ shockMargin e then Regime.closure
  else Regime.portage

-- Lemmes de calcul (répliques des motifs de preuve de ModeFlux).

theorem regime_closure_of_local (e : Entity) (d : Nat)
    (hd : d > 0) (h : d ≤ shockMargin e) :
    dynamicRegime e d = Regime.closure := by
  unfold dynamicRegime
  rw [if_neg (by omega : ¬ d = 0), if_pos h]

theorem regime_portage_of_overflow (e : Entity) (d : Nat)
    (hd : d > 0) (h : d > shockMargin e) :
    dynamicRegime e d = Regime.portage := by
  unfold dynamicRegime
  rw [if_neg (by omega : ¬ d = 0), if_neg (by omega : ¬ d ≤ shockMargin e)]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. M1 — L'IDENTITÉ DES MODES : bisimulation de coût
-- ═══════════════════════════════════════════════════════════════════════════

/-- Deux entités sont LE MÊME MODE ssi aucun choc ne les distingue : même
    régime dynamique sous toute demande. C'est la bisimulation de coût —
    l'identité par le comportement, pas par la structure. -/
def SameMode (e e' : Entity) : Prop :=
  ∀ demand, dynamicRegime e demand = dynamicRegime e' demand

/-- [∎] SameMode est une équivalence (réflexivité). -/
theorem sameMode_refl (e : Entity) : SameMode e e := fun _ => rfl

/-- [∎] Symétrie. -/
theorem sameMode_symm {e e' : Entity} (h : SameMode e e') : SameMode e' e :=
  fun d => (h d).symm

/-- [∎] Transitivité. -/
theorem sameMode_trans {a b c : Entity}
    (h1 : SameMode a b) (h2 : SameMode b c) : SameMode a c :=
  fun d => (h1 d).trans (h2 d)

/-- [∎] M1-a — MÊME MARGE ⟹ MÊME MODE.
    La marge détermine intégralement la réponse au choc. -/
theorem sameMode_of_margin_eq (e e' : Entity)
    (h : shockMargin e = shockMargin e') : SameMode e e' := by
  intro demand
  unfold dynamicRegime
  rw [h]

/-- [∎] M1-b — MÊME MODE ⟹ MÊME MARGE.
    Réciproque, par choc séparateur : si les marges diffèrent, la demande
    `min(m,m') + 1` classe l'une clôture et l'autre portage. L'invariant est
    donc COMPLET : rien de plus fin que la marge n'est observable au choc.
    (Core pur : trichotomie explicite, pas de by_contra/rcases.) -/
theorem margin_eq_of_sameMode (e e' : Entity) (h : SameMode e e') :
    shockMargin e = shockMargin e' := by
  cases Nat.lt_trichotomy (shockMargin e) (shockMargin e') with
  | inl hlt =>
      -- margin e < margin e' : le choc (margin e)+1 déborde e, tient sur e'
      have heq := h (shockMargin e + 1)
      rw [regime_portage_of_overflow e _ (by omega) (by omega)] at heq
      rw [regime_closure_of_local e' _ (by omega) (by omega)] at heq
      exact absurd heq (by decide)
  | inr h2 =>
      cases h2 with
      | inl heqm => exact heqm
      | inr hgt =>
          -- margin e' < margin e : symétrique
          have heq := h (shockMargin e' + 1)
          rw [regime_closure_of_local e _ (by omega) (by omega)] at heq
          rw [regime_portage_of_overflow e' _ (by omega) (by omega)] at heq
          exact absurd heq (by decide)

/-- [∎] M1 — LE MODE EST LA MARGE.
    L'identité comportementale (bisimulation de coût) coïncide exactement avec
    l'égalité des marges de choc. Le mode d'une entité finie est un seul
    nombre : ce qui lui reste. -/
theorem M1_mode_is_margin (e e' : Entity) :
    SameMode e e' ↔ shockMargin e = shockMargin e' :=
  ⟨margin_eq_of_sameMode e e', sameMode_of_margin_eq e e'⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. M2 — L'ESPACE DES MODES : ℕ, dérivé
-- ═══════════════════════════════════════════════════════════════════════════

/-- Le représentant canonique du mode m : pur-clôture de marge exactement m. -/
def canonical (m : Nat) : Entity :=
  { self := m + 1, ownCost := 1, ownCost_pos := by omega,
    hostInflow := 0, outflow := 0 }

/-- [∎] Le canonique réalise sa marge : shockMargin (canonical m) = m.
    Calcul : (m+1) − ((1+0) − 0) = m. Réduction forcée par `show`, puis omega. -/
theorem canonical_margin (m : Nat) : shockMargin (canonical m) = m := by
  show m + 1 - ((1 + 0) - 0) = m
  omega

/-- [∎] M2-a — RÉALISATION : toute marge est un mode habité. -/
theorem M2_realization (m : Nat) : ∃ e : Entity, shockMargin e = m :=
  ⟨canonical m, canonical_margin m⟩

/-- [∎] M2-b — TRICHOTOMIE : sous toute demande, toute entité tombe dans
    exactement un des trois régimes (exhaustivité par demande). -/
theorem regime_trichotomy (e : Entity) (d : Nat) :
    dynamicRegime e d = Regime.aggregate ∨
    dynamicRegime e d = Regime.closure ∨
    dynamicRegime e d = Regime.portage := by
  unfold dynamicRegime
  by_cases h0 : d = 0
  · left; rw [if_pos h0]
  · by_cases hle : d ≤ shockMargin e
    · right; left; rw [if_neg h0, if_pos hle]
    · right; right; rw [if_neg h0, if_neg hle]

/-- [∎] M2-c — PLURALITÉ INTRA-RÉGIME (la question pendante depuis le tour 2).
    Deux marges distinctes non nulles sont deux modes DISTINCTS qui se
    comportent tous deux en CLÔTURE sous petit choc. La pluralité des modes
    n'est pas posée : elle est dérivée, et elle est intra-régime — il y a une
    infinité de manières d'être une clôture, indexées par la marge. -/
theorem intra_regime_plurality (m m' : Nat)
    (hne : m ≠ m') (hm : m > 0) (hm' : m' > 0) :
    ¬ SameMode (canonical m) (canonical m') ∧
    dynamicRegime (canonical m) 1 = Regime.closure ∧
    dynamicRegime (canonical m') 1 = Regime.closure := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hmm := margin_eq_of_sameMode _ _ h
    rw [canonical_margin, canonical_margin] at hmm
    exact hne hmm
  · exact regime_closure_of_local _ 1 (by omega) (by rw [canonical_margin]; omega)
  · exact regime_closure_of_local _ 1 (by omega) (by rw [canonical_margin]; omega)

/-- [∎] M2-d — LE FOND DE L'ESPACE : le mode de marge 0 ne peut JAMAIS être
    clôture, sous aucune demande. C'est le mode de l'exsangue — celui que
    `hbite`/`hroom` excluaient des théorèmes de dégradation, ici caractérisé
    positivement : un mode distingué, pas un cas pathologique. -/
theorem margin_zero_never_closure (e : Entity)
    (h : shockMargin e = 0) (d : Nat) :
    dynamicRegime e d ≠ Regime.closure := by
  intro hcl
  unfold dynamicRegime at hcl
  by_cases h0 : d = 0
  · rw [if_pos h0] at hcl; exact absurd hcl (by decide)
  · by_cases hle : d ≤ shockMargin e
    · omega
    · rw [if_neg h0, if_neg hle] at hcl; exact absurd hcl (by decide)

/-- [∎] M2 — L'ESPACE DES MODES EST ℕ.
    Section (toute marge est réalisée) + invariant complet (M1) : le quotient
    Entity / SameMode est en bijection avec ℕ par la marge. L'espace des modes
    est dérivé, dénombrable, totalement ordonné — et son ordre est l'ordre des
    marges, c'est-à-dire l'ordre de la résistance au choc. -/
theorem M2_mode_space_is_Nat :
    (∀ m : Nat, shockMargin (canonical m) = m) ∧
    (∀ e e' : Entity, SameMode e e' ↔ shockMargin e = shockMargin e') :=
  ⟨canonical_margin, M1_mode_is_margin⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. PROFILS vs MODES — la structure est plus fine que le comportement
-- ═══════════════════════════════════════════════════════════════════════════

/-- Le subventionné de ModeFlux : self 5, ownCost 3, apport 3, rien versé. -/
def subsidizedOrganism : Entity :=
  { self := 5, ownCost := 3, ownCost_pos := by omega, hostInflow := 3, outflow := 0 }

/-- Le relais (découvert par le contre-exemple d'omega) : verse 3, reçoit 10. -/
def relayEntity : Entity :=
  { self := 5, ownCost := 3, ownCost_pos := by omega, hostInflow := 10, outflow := 3 }

/-- [∎] PROFILS ≠ MODES — le subventionné et le relais ont des profils de flux
    DIFFÉRENTS (l'un verse, l'autre non) mais sont LE MÊME MODE (même marge 5,
    même comportement sous tout choc). Le mode est un quotient STRICT de la
    structure de flux : la bisimulation efface la différence subvention/relais
    que le typage des flux avait créée. Les deux axes sont donc réels et
    distincts — le profil dit COMMENT l'entité tient, le mode dit CE QU'ELLE
    TIENT. -/
theorem profiles_strictly_finer_than_modes :
    SameMode subsidizedOrganism relayEntity ∧
    subsidizedOrganism.outflow ≠ relayEntity.outflow := by
  constructor
  · apply sameMode_of_margin_eq
    show (5 : Nat) - ((3 + 0) - 3) = 5 - ((3 + 3) - 10)
    omega
  · decide

end ModeIdentity

/-!
## NOTE — ce que M1/M2 financent, et leur dette

**Financé.** La théorie des modes réclamée depuis le tour 2 a maintenant ses
trois pièces : M1 (identité : le mode est la marge — invariant complet de la
bisimulation de coût), M2 (espace : ℕ, dérivé — pluralité infinie, intra-régime
comprise, avec un fond distingué en marge 0), M3 (`ModeFlux` : le mode détermine
le destin économique sous choc, coïncidence/divergence localisée). « Nul acte
sans mode » (I-γ) reçoit un contenu : tout acte fini a une marge, la marge est
son mode, et il y en a une infinité.

**Le résultat structurel inattendu.** Le quotient modal est STRICT
(`profiles_strictly_finer_than_modes`) : la structure de flux (quatre champs)
se projette sur un seul nombre. En particulier le relais et le subventionné —
que la localisation de ModeFlux distinguait par leur flux — sont le même mode.
La quadripartition des régimes et l'espace des modes ne sont donc PAS le même
étage : les régimes classent les COMPORTEMENTS (par demande), les modes classent
les ENTITÉS (par marge), les profils classent les STRUCTURES (par flux). Trois
grains, ordonnés : profil > mode > régime-sous-demande.

**Dette nommée (interface-relativité).** La bisimulation est relative à son
interface d'observation : SameMode observe `dynamicRegime` sous toutes les
demandes, rien d'autre. Une interface plus riche (observer les traces complètes,
absorbed/externalized/residual, ou le comportement itéré sous chocs successifs
avec marge décroissante) donnerait un quotient plus fin — le relais et le
subventionné y seraient peut-être séparés (leurs hôtes, eux, ne vivent pas la
même chose). Le choix de l'interface est une décision, assumée ici : le mode au
sens de M1 est le mode SOUS CHOC UNIQUE. L'extension aux chocs itérés est le
chantier naturel suivant — et c'est elle qui dira si « profil > mode » survit à
la dynamique.
-/
