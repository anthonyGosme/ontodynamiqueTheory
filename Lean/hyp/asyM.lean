/-!
  AsymmetryDerivation.lean — Dérivation de l'asymétrie des coûts

  L'asymétrie `construction_cost > maintenance_cost` était posée
  comme champ dans TransitionSystem (R_XVIII.lean). Ce fichier
  la dérive d'un principe plus fondamental :

    « Un acte guidé par un template coûte moins qu'un acte sans template. »

  Le template = la structure existante que l'acte de maintenance réplique.
  L'acte de construction n'a pas de template — il crée de novo.

  Axiomes mobilisés :
    IV  : tout acte a un coût positif (raw_cost > 0)
    IV' : même guidé, l'acte coûte (template_saving < raw_cost)
    Nouveau : un template réduit le coût (template_saving > 0)

  Le « nouveau » contenu est : la contrainte structurelle réduit le coût.
  C'est dérivable de IV : un acte dont le résultat est contraint par une
  structure existante a un espace de possibilités réduit, donc un coût
  réduit. La contrainte ne crée pas de l'énergie — elle canalise l'acte.

  Théorèmes : 7
  Sorry : 0
  Import : aucun
-/

namespace AsymmetryDerivation

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Le coût fondé sur le template
-- ═══════════════════════════════════════════════════════════════════════════

/-- Un acte avec possibilité de template.
    Le coût brut est le coût de l'acte sans aucune guidance.
    Le template_saving est la réduction obtenue quand l'acte
    est guidé par une structure existante. -/
structure ActCost where
  /-- Coût brut d'un acte non guidé (IV : tout acte coûte) -/
  raw_cost : Nat
  raw_cost_pos : raw_cost > 0
  /-- Réduction de coût quand un template guide l'acte.
      Philosophiquement : la contrainte réduit l'espace de possibilités,
      donc réduit le coût exploratoire. -/
  template_saving : Nat
  /-- Un template aide (la guidance n'est pas nulle) -/
  saving_pos : template_saving > 0
  /-- Un template ne rend pas l'acte gratuit (IV préservé) -/
  saving_bound : template_saving < raw_cost

/-- Construction = acte sans template. Coût = coût brut. -/
def construction_cost (a : ActCost) : Nat := a.raw_cost

/-- Maintenance = acte avec template. Coût = brut - saving. -/
def maintenance_cost (a : ActCost) : Nat := a.raw_cost - a.template_saving

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. L'asymétrie comme théorème
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] ASYMÉTRIE DÉRIVÉE — La construction coûte plus que la maintenance.
    Preuve : construction = raw, maintenance = raw - saving, saving > 0.
    Ce n'est plus un postulat — c'est une conséquence de IV + template. -/
theorem asymmetry_derived (a : ActCost) :
    construction_cost a > maintenance_cost a := by
  unfold construction_cost maintenance_cost
  have := a.saving_pos
  have := a.saving_bound
  omega

/-- [∎] La maintenance coûte strictement plus que zéro.
    IV est préservé même pour l'acte guidé. -/
theorem maintenance_pos (a : ActCost) :
    maintenance_cost a > 0 := by
  unfold maintenance_cost
  have := a.raw_cost_pos
  have := a.saving_bound
  omega

/-- [∎] La construction coûte strictement plus que zéro (IV direct). -/
theorem construction_pos (a : ActCost) :
    construction_cost a > 0 := by
  unfold construction_cost
  exact a.raw_cost_pos

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Construction du TransitionSystem avec asymétrie prouvée
-- ═══════════════════════════════════════════════════════════════════════════

/-- TransitionSystem dont l'asymétrie est DÉRIVÉE, pas posée.
    Identique à R_XVIII.TransitionSystem mais sans le champ `asymmetry`. -/
structure DerivedTransitionSystem where
  /-- Structure de coût avec template -/
  act : ActCost
  /-- Érosion par step sans maintenance (IV + V) -/
  degradation : Nat
  degradation_pos : degradation > 0
  /-- Capacité d'investissement par step (IX : finie) -/
  capacity : Nat
  capacity_pos : capacity > 0

/-- Coût de construction extrait du système. -/
def DerivedTransitionSystem.constr (s : DerivedTransitionSystem) : Nat :=
  construction_cost s.act

/-- Coût de maintenance extrait du système. -/
def DerivedTransitionSystem.maint (s : DerivedTransitionSystem) : Nat :=
  maintenance_cost s.act

/-- [∎] L'asymétrie est une propriété dérivée du système, pas un axiome. -/
theorem system_asymmetry (s : DerivedTransitionSystem) :
    s.constr > s.maint := asymmetry_derived s.act

/-- [∎] Constructeur de pont : DerivedTransitionSystem satisfait toutes
    les propriétés de R_XVIII.TransitionSystem.
    Les trois propriétés de coût (construction_pos, maintenance_pos,
    asymmetry) sont PROUVÉES, pas posées. -/
theorem derived_system_properties (s : DerivedTransitionSystem) :
    s.constr > 0 ∧
    s.maint > 0 ∧
    s.constr > s.maint :=
  ⟨construction_pos s.act,
   maintenance_pos s.act,
   asymmetry_derived s.act⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Le gap persiste avec le coût dérivé
-- ═══════════════════════════════════════════════════════════════════════════

/-- Constructible au niveau n dans le système dérivé. -/
def can_build (s : DerivedTransitionSystem) (n : Nat) : Prop :=
  n * s.maint + s.constr ≤ s.capacity

/-- Maintenable au niveau n dans le système dérivé. -/
def can_maintain (s : DerivedTransitionSystem) (n : Nat) : Prop :=
  n * s.maint ≤ s.capacity

/-- [∎] Le Lemme 2 (inclusion) tient avec le coût dérivé. -/
theorem derived_build_implies_maintain (s : DerivedTransitionSystem) (n : Nat)
    (h : can_build s n) : can_maintain s n := by
  unfold can_build at h; unfold can_maintain
  have : s.constr > 0 := construction_pos s.act
  omega

/-- [∎] Le Lemme 3 (gap d'hystérésis) tient avec le coût dérivé.
    La preuve est identique — seule la SOURCE de l'asymétrie change. -/
theorem derived_hysteresis (s : DerivedTransitionSystem) :
    ∃ n, can_maintain s n ∧ ¬can_build s n := by
  have hm_pos : s.maint > 0 := maintenance_pos s.act
  refine ⟨s.capacity / s.maint, ?_, ?_⟩
  · unfold can_maintain
    have h_dam := Nat.div_add_mod s.capacity s.maint
    have hcomm : s.capacity / s.maint * s.maint =
                 s.maint * (s.capacity / s.maint) :=
      Nat.mul_comm _ _
    omega
  · unfold can_build
    intro h_absurd
    have h_dam := Nat.div_add_mod s.capacity s.maint
    have h_mod := Nat.mod_lt s.capacity hm_pos
    have h_asym := system_asymmetry s
    have hcomm : s.capacity / s.maint * s.maint =
                 s.maint * (s.capacity / s.maint) :=
      Nat.mul_comm _ _
    omega

-- ═══════════════════════════════════════════════════════════════════════════
-- RÉSUMÉ
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Inventaire

  | # | Théorème | Contenu |
  |---|----------|---------|
  | 1 | asymmetry_derived | construction > maintenance (DÉRIVÉ) |
  | 2 | maintenance_pos | maintenance > 0 (DÉRIVÉ) |
  | 3 | construction_pos | construction > 0 (IV direct) |
  | 4 | system_asymmetry | asymétrie au niveau du système |
  | 5 | derived_system_properties | les 3 propriétés de coût prouvées |
  | 6 | derived_build_implies_maintain | Lemme 2 avec coût dérivé |
  | 7 | derived_hysteresis | Lemme 3 avec coût dérivé |

  **7 théorèmes, 0 sorry, 0 import.**

  ## Ce qui est posé vs prouvé

  | Posé (champs de ActCost) | Prouvé (théorèmes) |
  |---|---|
  | raw_cost > 0 (IV) | construction > maintenance |
  | template_saving > 0 (contrainte réduit coût) | maintenance > 0 |
  | template_saving < raw_cost (IV préservé) | construction > 0 |
  | | hystérésis (Lemme 3) |

  ## Ce qui a changé

  Avant (R_XVIII.lean) :
    `asymmetry : construction_cost > maintenance_cost` — CHAMP

  Après (ce fichier) :
    `theorem asymmetry_derived : construction_cost a > maintenance_cost a` — THÉORÈME

  Le postulat a été décomposé en trois champs plus fondamentaux :
  1. `raw_cost > 0` — IV pur (tout acte coûte)
  2. `saving_pos` — un template réduit le coût (nouveau, minimal)
  3. `saving_bound` — un template ne rend pas l'acte gratuit (IV préservé)

  Le contenu réellement nouveau est `saving_pos` : la contrainte structurelle
  réduit le coût d'un acte. C'est le noyau irréductible de l'asymétrie.
-/

end AsymmetryDerivation
