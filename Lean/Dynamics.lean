/-!
# Dynamics.lean — Inter-regime dynamics and cost asymmetry


Theorems : 7 (AsymmetryDerivation) + 20 (RXVIII) = 27
Sorry : 0
Imports: none
-/

/-!
  AsymmetryDerivation.lean — Derivation de l'asymmetry des costs

  The asymmetry `construction_cost > maintenance_cost` était positede
  comme champ dans TransitionSystem (R_XVIII.lean). Ce fichier
  la drift d'un principle plus fondamental :

    « A acte guided by a template coste less qu'a acte without template. »

  The template = the structure existante that the acte of maintenance replica.
  L'acte de construction n'a pas de template — il creates de novo.

  Axioms mobilisés :
    IV  : tout acte a un cost positif (raw_cost > 0)
    IV' : same guided, the acte coste (template_saving < raw_cost)
    Nouveau : un template reduced le cost (template_saving > 0)

  Le « nouveau » contenu est : la constraint structurelle reduced le cost.
  This is derivable of IV : a acte dont the result is contraint by a
  structure existante a un espace de possibilitys reduced, donc un cost
  reduced. La constraint ne creates pas de l'energy — elle canalise l'acte.

  Theorems : 7
  Sorry : 0
  Imports: none
-/

namespace AsymmetryDerivation

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. The cost founded on the template
-- ═══════════════════════════════════════════════════════════════════════════

/-- Un acte avec possibility de template.
    The cost brut is the cost of the acte without aucune guidance.
    The template_saving is the reduction obtenue quand the acte
    is guided by a structure existante. -/
structure ActCost where
  /-- Cost brut of a acte non guided (IV : all acte coste) -/
  raw_cost : Nat
  raw_cost_pos : raw_cost > 0
  /-- Reduction de cost quand un template guide l'acte.
      Philosophiquement : the constraint reduced the espace of possibilitys,
      donc reduced le cost exploratoire. -/
  template_saving : Nat
  /-- A template aide (the guidance is not nulle) -/
  saving_pos : template_saving > 0
  /-- Un template ne rend pas l'acte gratuit (IV preserved) -/
  saving_bound : template_saving < raw_cost

/-- Construction = acte sans template. Cost = cost brut. -/
def construction_cost (a : ActCost) : Nat := a.raw_cost

/-- Maintenance = acte avec template. Cost = brut - saving. -/
def maintenance_cost (a : ActCost) : Nat := a.raw_cost - a.template_saving

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. L'asymmetry comme theorem
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] ASYMMETRY DERIVEDE — La construction coste plus que la maintenance.
    Preuve : construction = raw, maintenance = raw - saving, saving > 0.
    This n'is more a postulat — this is a consequence of IV + template. -/
theorem asymmetry_derived (a : ActCost) :
    construction_cost a > maintenance_cost a := by
  unfold construction_cost maintenance_cost
  have := a.saving_pos
  have := a.saving_bound
  omega

/-- [∎] La maintenance coste strictly plus que zero.
    IV is preserved same for the acte guided. -/
theorem maintenance_pos (a : ActCost) :
    maintenance_cost a > 0 := by
  unfold maintenance_cost
  have := a.raw_cost_pos
  have := a.saving_bound
  omega

/-- [∎] La construction coste strictly plus que zero (IV direct). -/
theorem construction_pos (a : ActCost) :
    construction_cost a > 0 := by
  unfold construction_cost
  exact a.raw_cost_pos

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Construction du TransitionSystem avec asymmetry provede
-- ═══════════════════════════════════════════════════════════════════════════

/-- TransitionSystem dont the asymmetry is DERIVEDE, pas positede.
    Identique at R_XVIII.TransitionSystem but without the champ `asymmetry`. -/
structure DerivedTransitionSystem where
  /-- Structure de cost avec template -/
  act : ActCost
  /-- Erosion by step without maintenance (IV + V) -/
  degradation : Nat
  degradation_pos : degradation > 0
  /-- Capacity of investissement by step (IX : finie) -/
  capacity : Nat
  capacity_pos : capacity > 0

/-- Cost de construction extrait du system. -/
def DerivedTransitionSystem.constr (s : DerivedTransitionSystem) : Nat :=
  construction_cost s.act

/-- Cost de maintenance extrait du system. -/
def DerivedTransitionSystem.maint (s : DerivedTransitionSystem) : Nat :=
  maintenance_cost s.act

/-- [∎] The asymmetry is a property derived of the system, pas a axiom. -/
theorem system_asymmetry (s : DerivedTransitionSystem) :
    s.constr > s.maint := asymmetry_derived s.act

/-- [∎] Constructeur de pont : DerivedTransitionSystem satisfait toutes
    les propertys de R_XVIII.TransitionSystem.
    Les trois propertys de cost (construction_pos, maintenance_pos,
    asymmetry) are PROUVÉES, not positedes. -/
theorem derived_system_properties (s : DerivedTransitionSystem) :
    s.constr > 0 ∧
    s.maint > 0 ∧
    s.constr > s.maint :=
  ⟨construction_pos s.act,
   maintenance_pos s.act,
   asymmetry_derived s.act⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Le gap persiste avec le cost derived
-- ═══════════════════════════════════════════════════════════════════════════

/-- Constructible au level n dans le system derived. -/
def can_build (s : DerivedTransitionSystem) (n : Nat) : Prop :=
  n * s.maint + s.constr ≤ s.capacity

/-- Maintenable au level n dans le system derived. -/
def can_maintain (s : DerivedTransitionSystem) (n : Nat) : Prop :=
  n * s.maint ≤ s.capacity

/-- [∎] Le Lemme 2 (inclusion) tient avec le cost derived. -/
theorem derived_build_implies_maintain (s : DerivedTransitionSystem) (n : Nat)
    (h : can_build s n) : can_maintain s n := by
  unfold can_build at h; unfold can_maintain
  have : s.constr > 0 := construction_pos s.act
  omega

/-- [∎] The Lemme 3 (gap of hysteresis) tient with the cost derived.
    The preuve is identique — only the SOURCE of the asymmetry change. -/
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
-- SUMMARY
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Inventaire

  | # | Theorem | Contenu |
  |---|----------|---------|
  | 1 | asymmetry_derived | construction > maintenance (DERIVED) |
  | 2 | maintenance_pos | maintenance > 0 (DERIVED) |
  | 3 | construction_pos | construction > 0 (IV direct) |
  | 4 | system_asymmetry | asymmetry au level du system |
  | 5 | derived_system_properties | les 3 propertys de cost provedes |
  | 6 | derived_build_implies_maintain | Lemme 2 avec cost derived |
  | 7 | derived_hysteresis | Lemme 3 avec cost derived |

  **7 theorems, 0 sorry, 0 import.**

  ## This which is posited vs proved

  | Posé (champs of ActCost) | Prouvé (theorems) |
  |---|---|
  | raw_cost > 0 (IV) | construction > maintenance |
  | template_saving > 0 (constraint reduced cost) | maintenance > 0 |
  | template_saving < raw_cost (IV preserved) | construction > 0 |
  | | hysteresis (Lemme 3) |

  ## What a changed

  Avant (R_XVIII.lean) :
    `asymmetry : construction_cost > maintenance_cost` — CHAMP

  After (ce fichier) :
    `theorem asymmetry_derived : construction_cost a > maintenance_cost a` — THEOREM

  The postulat a été decomposed en trois champs more fondamentaux :
  1. `raw_cost > 0` — IV pur (tout acte coste)
  2. `saving_pos` — un template reduced le cost (nouveau, minimal)
  3. `saving_bound` — un template ne rend pas l'acte gratuit (IV preserved)

  The contenu reallement nouveau is `saving_pos` : the constraint structurelle
  reduced the cost of a acte. This is the core irreducible of the asymmetry.
-/

end AsymmetryDerivation

-- ═══════════════════════════════════════════════════════════════════════════
-- RXVIII — Dynamique inter-regime (anciennement R_XVIII.lean)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  R_XVIII.lean — Dynamique inter-regime (R-XVIII)

  Result : Les transitions entre regimes de composition (R-XVII) sont
  soumises at a hysteresis structurelle derived of the asymmetry of costs
  (construction > maintenance). The regime of a system depends of its
  histoire, not seulement of its état.

  Architecture :
    §1  AlphaState — degree of auto-production (paire Nat)
    §2  TransitionSystem — costs asymmetrics + capacity + degradation
    §3  Lemme 1 — decay by default of α (IV + IX → XXXII)
    §4  Lemme 2 — can_build → can_maintain (asymmetry → inclusion)
    §5  Lemme 3 — zone d'hysteresis (∃ level maintainable ∧ ¬buildable)
    §6  Regimes and dependency at the histoire
    §7  Lemme 4 — crossing de threshold (bifurcation)
    §8  Instability of the zone intermediate
    §9  R-XVIII — assemblage

  Axioms mobilisés : I (being=doing), IV (cost > 0, asymmetry),
    V (pression/degradation), IX (finitude/capacity bounded),
    XXXII (dissolution), R-XVII (regimes)

  Statut inferential :
    (a)(b)(c)(d)(i)(ii) : ∎  — déductifs
    (iii) bimodalité : ≈₁   — hypothesis populationnelle, hors Lean

  Theorems : 24
  Sorry : 0
  Imports: none
-/

namespace RXVIII

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. AlphaState — Degree of auto-production of constraint
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  α = constraint endogenous / constraint totale.
  Formalisé as paire of Nat (not of division, not of Q, not of ℝ).
  The comparaisons itself font on the numérateurs/dénominateurs separatement.
-/

/-- The degree of auto-production of a system. -/
structure AlphaState where
  /-- Contrainte auto-produite par le system -/
  endogenous : Nat
  /-- Contrainte totale necessary au maintien -/
  total : Nat
  total_pos : total > 0
  bound : endogenous ≤ total

/-- α = 0 : aggregate pur (aucune auto-production). -/
def AlphaState.isAggregate (a : AlphaState) : Prop := a.endogenous = 0

/-- α > 0 : auto-production active. -/
def AlphaState.isActive (a : AlphaState) : Prop := a.endogenous > 0

/-- [∎] Aggregate et actif sont mutually exclusive. -/
theorem aggregate_active_exclusive (a : AlphaState) :
    ¬(a.isAggregate ∧ a.isActive) := by
  intro ⟨h0, hp⟩
  unfold AlphaState.isAggregate at h0
  unfold AlphaState.isActive at hp
  omega

/-- [∎] Aggregate et actif sont exhaustifs. -/
theorem aggregate_active_exhaustive (a : AlphaState) :
    a.isAggregate ∨ a.isActive := by
  unfold AlphaState.isAggregate AlphaState.isActive
  by_cases h : a.endogenous = 0
  · exact Or.inl h
  · right; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. TransitionSystem — Structure des costs et capacity
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  Enrichissement de IV : deux types de cost sur un same acte.
  - construction_cost : cost for CRÉER a unity of constraint endogenous
  - maintenance_cost : cost for MAINTENIR a unity existante

  The asymmetry (construction > maintenance) is the source of the hysteresis.
  It drift of IV : a acte dont the result is indetermined (construction)
  coste more qu'a acte guided by the structure existante (maintenance).
-/

/-- Un system de transition entre regimes de composition. -/
structure TransitionSystem where
  /-- Cost by unity for construire a nouvelle constraint (IV) -/
  construction_cost : Nat
  /-- Cost by unity for maintenir a constraint existante (IV) -/
  maintenance_cost : Nat
  /-- IV : tout acte de construction a un cost positif -/
  construction_pos : construction_cost > 0
  /-- IV : tout acte de maintenance a un cost positif -/
  maintenance_pos : maintenance_cost > 0
  /-- LEMME 2 structural : construire coste plus que maintenir -/
  asymmetry : construction_cost > maintenance_cost
  /-- Erosion by step without maintenance (IV + V : pression of exteriority) -/
  degradation : Nat
  degradation_pos : degradation > 0
  /-- Capacity of investissement by step (IX : finie) -/
  capacity : Nat
  capacity_pos : capacity > 0

/-- Un system peut CONSTRUIRE au level n : payer la maintenance
    of n unitys existantes PLUS the construction of a unity nouvelle. -/
def can_build_at (s : TransitionSystem) (n : Nat) : Prop :=
  n * s.maintenance_cost + s.construction_cost ≤ s.capacity

/-- Un system peut MAINTENIR au level n : payer la maintenance
    de n unitys existantes. Pas de construction. -/
def can_maintain_at (s : TransitionSystem) (n : Nat) : Prop :=
  n * s.maintenance_cost ≤ s.capacity

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Lemme 1 — Decay by default of α
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Lemme 1 : Sans regeneration active, α decreases.

  XXXII applied at the parameter α. The irreversibility of the cost (IV) and
  la finitude de la capacity (IX) garantissent l'erosion.
  The default is the degradation — the stability exige a acte.
-/

/-- [∎] LEMME 1a — DECAY PAR DEFAULT.
    After `steps` steps sans maintenance, si le drain cumulative exceeds
    the level endogenous, the reserve is exhausted.
    Pas besoin de poser degradation > 0 : h_fatal suffit. -/
theorem alpha_decay (endogenous degradation steps : Nat)
    (h_fatal : steps * degradation > endogenous) :
    ¬(endogenous ≥ steps * degradation) := by
  omega

/-- [∎] LEMME 1b — DURATION DE VIE FINIE DE α.
    It exists a nombre fini of steps for exhaustsr every constraint
    endogenous. Pattern identique at lifespan_bound (v5.3). -/
theorem alpha_exhaustion (endogenous degradation : Nat)
    (h_pos : degradation > 0) :
    ∃ k, k * degradation > endogenous := by
  refine ⟨endogenous + 1, ?_⟩
  have h1 : 1 ≤ degradation := h_pos
  have h2 : (endogenous + 1) * 1 ≤ (endogenous + 1) * degradation :=
    Nat.mul_le_mul_left (endogenous + 1) h1
  simp only [Nat.mul_one] at h2
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Lemme 2 — Asymmetry des costs (construction > maintenance)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Lemme 2 : La construction coste plus que la maintenance.

  Consequence directe : all this which is constructible is maintenable,
  but pas the inverse. The asymmetry creates a irreversibility structurelle
  dans les transitions entre regimes.
-/

/-- [∎] LEMME 2a — INCLUSION : constructible → maintenable.
    Si le system peut payer maintenance + construction, il peut
    payer maintenance seule. -/
theorem build_implies_maintain (s : TransitionSystem) (n : Nat)
    (h : can_build_at s n) :
    can_maintain_at s n := by
  unfold can_build_at at h
  unfold can_maintain_at
  have := s.construction_pos
  omega

/-- [∎] LEMME 2b — Le surcost de construction est strictly positif. -/
theorem construction_overhead (s : TransitionSystem) (n : Nat) :
    n * s.maintenance_cost < n * s.maintenance_cost + s.construction_cost := by
  have := s.construction_pos; omega

/-- [∎] LEMME 2c — Le level 0 est toujours maintenable.
    Un system sans constraint endogenous ne paie rien en maintenance. -/
theorem maintain_at_zero (s : TransitionSystem) :
    can_maintain_at s 0 := by
  unfold can_maintain_at; simp

/-- [∎] LEMME 2d — Monotonie descendante of the maintainability.
    If the level n is maintenable, all level less than the is also. -/
theorem maintain_monotone (s : TransitionSystem) (n m : Nat)
    (h_le : m ≤ n) (h : can_maintain_at s n) :
    can_maintain_at s m := by
  unfold can_maintain_at at *
  have : m * s.maintenance_cost ≤ n * s.maintenance_cost :=
    Nat.mul_le_mul_right s.maintenance_cost h_le
  omega

/-- [∎] LEMME 2e — Monotonie descendante of the constructibility.
    If the level n is constructible, all level less than the is also. -/
theorem build_monotone (s : TransitionSystem) (n m : Nat)
    (h_le : m ≤ n) (h : can_build_at s n) :
    can_build_at s m := by
  unfold can_build_at at *
  have : m * s.maintenance_cost ≤ n * s.maintenance_cost :=
    Nat.mul_le_mul_right s.maintenance_cost h_le
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Lemme 3 — Zone d'hysteresis
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Lemme 3 : It exists a zone maintainable-but-non-constructible.

  C'est le CORE de R-XVIII. L'asymmetry des costs creates un GAP
  entre le plafond de construction et le plafond de maintenance.
  In this gap, the regime depends of the histoire of the system.

  The preuve utilise the division entière. The witness is
  n = capacity / maintenance_cost (le plus haut level maintenable).
  On montre that this level not is PAS constructible, car the surcost
  de construction (c > m) ne tient pas dans le residue (cap % m < m).
-/

/-- Utilitaire : produit de deux positifs est positif. -/
theorem mul_pos_of_pos (a b : Nat) (ha : a > 0) (hb : b > 0) :
    a * b > 0 := by
  have h1 : 1 ≤ a := ha
  have h2 : 1 ≤ b := hb
  have h3 : 1 * 1 ≤ a * b := Nat.mul_le_mul h1 h2
  omega

/-- [∎] LEMME 3 — ZONE D'HYSTERESIS.
    Il exists un level maintenable mais non constructible.

    Preuve : n = cap / m.
    - n * m ≤ cap  (division Nat)
    - n * m + c > cap  (car c > m > cap % m)

    La preuve connecte l'asymmetry (c > m) at l'existence du gap
    via the structure of the division entière. It n'is PAS
    un omega trivial — elle mobilise Nat.div_add_mod et Nat.mod_lt. -/
theorem hysteresis_zone_exists (s : TransitionSystem) :
    ∃ n, can_maintain_at s n ∧ ¬can_build_at s n := by
  let n := s.capacity / s.maintenance_cost
  refine ⟨n, ?_, ?_⟩
  · -- PARTIE 1 : can_maintain_at n (n * m ≤ cap)
    unfold can_maintain_at
    have h_dam := Nat.div_add_mod s.capacity s.maintenance_cost
    -- h_dam : m * (cap / m) + cap % m = cap
    have hcomm : n * s.maintenance_cost =
                 s.maintenance_cost * (s.capacity / s.maintenance_cost) :=
      Nat.mul_comm n s.maintenance_cost
    -- m * n ≤ cap (car m * n + remainder = cap)
    omega
  · -- PARTIE 2 : ¬can_build_at n (n * m + c > cap)
    unfold can_build_at
    intro h_absurd
    have h_dam := Nat.div_add_mod s.capacity s.maintenance_cost
    have h_mod := Nat.mod_lt s.capacity s.maintenance_pos
    -- h_mod : cap % m < m
    have h_asym := s.asymmetry
    -- h_asym : c > m
    have hcomm : n * s.maintenance_cost =
                 s.maintenance_cost * (s.capacity / s.maintenance_cost) :=
      Nat.mul_comm n s.maintenance_cost
    -- De h_dam : m * n = cap - cap % m
    -- De h_mod + h_asym : c > m > cap % m, donc c > cap % m
    -- Donc n * m + c = (cap - cap % m) + c > cap  (car c > cap % m)
    -- Contradiction avec h_absurd : n * m + c ≤ cap
    omega

/-- [∎] L'inclusion build → maintain est STRICTE.
    La converse est fausse : il exists un system et un level
    which is maintenable but pas constructible.
    Preuve by instantiation concrete + hysteresis_zone_exists. -/
theorem maintain_not_implies_build :
    ¬(∀ (s : TransitionSystem) (n : Nat),
        can_maintain_at s n → can_build_at s n) := by
  intro h_all
  have ⟨n, hn_m, hn_nb⟩ := hysteresis_zone_exists {
    construction_cost := 3, maintenance_cost := 1,
    construction_pos := by omega, maintenance_pos := by omega,
    asymmetry := by omega,
    degradation := 1, degradation_pos := by omega,
    capacity := 2, capacity_pos := by omega
  }
  exact hn_nb (h_all _ n hn_m)

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Regimes and dependency at the histoire
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Classification par regime + hysteresis

  R-XVII definedt trois regimes : aggregate, portage, closure.
  R-XVIII montre that the classification depends of the direction
  (ascent vs descente) in the zone of hysteresis.
-/

/-- Les trois regimes de composition (R-XVII). -/
inductive Regime where
  | closure    -- R-XVII-1 : auto-maintenance endogenous
  | portage    -- R-XVII-2 : cost externalized
  | aggregate  -- R-XVII-3 : pas de cycle
  deriving DecidableEq, Repr

/-- Direction de la trajectoire de α. -/
inductive Direction where
  | ascending   -- α en phase montante (construction)
  | descending  -- α en phase descendante (erosion ou maintenance)
  deriving DecidableEq, Repr

/-- Classification of a level in a regime.
    - Si n = 0 : aggregate (pas d'auto-production)
    - Si n > 0, ascendant : closure ssi n ≥ threshold montant
    - Si n > 0, descendant : closure ssi n ≥ threshold descendant
    Le threshold montant > threshold descendant = hysteresis. -/
def classify (n threshold_up threshold_down : Nat) (dir : Direction) : Regime :=
  if n = 0 then .aggregate
  else if dir = .ascending then
    (if n ≥ threshold_up then .closure else .portage)
  else
    (if n ≥ threshold_down then .closure else .portage)

/-- [∎] DEPENDENCE At The HISTOIRE — It exists a level classified
    differently selon the direction. This is the hysteresis qualitative.
    Witness : the threshold descendant lui-same (classified portage en ascent,
    closure en descente). -/
theorem regime_depends_on_history (th_up th_down : Nat)
    (h_hyst : th_down < th_up) (h_pos : th_down > 0) :
    classify th_down th_up th_down .ascending ≠
    classify th_down th_up th_down .descending := by
  have h_asc : classify th_down th_up th_down .ascending = .portage := by
    unfold classify
    rw [if_neg (show th_down ≠ 0 from by omega)]
    rw [if_pos (rfl : Direction.ascending = Direction.ascending)]
    rw [if_neg (show ¬(th_down ≥ th_up) from by omega)]
  have h_desc : classify th_down th_up th_down .descending = .closure := by
    unfold classify
    rw [if_neg (show th_down ≠ 0 from by omega)]
    rw [if_neg (show ¬(Direction.descending = Direction.ascending) from by decide)]
    rw [if_pos (show th_down ≥ th_down from Nat.le_refl _)]
  rw [h_asc, h_desc]; decide

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. Lemme 4 — Franchissement de threshold (bifurcation)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Lemme 4 : Bifurcation conditional

  Les transitions entre regimes se produisent quand α franchit un threshold.
  The discontinuité is ENDOGENOUS — produite by the structure of thresholds
  (hysteresis of the Lemme 3), not by a supplément extrinsèque (contra Badiou).

  Deux cas : crossing graduel (step par step) ou par choc (saut brusque).
  In the deux cas, the changement of regime is determined by the position
  relative de α et du threshold.
-/

/-- [∎] LEMME 4a — CROSSING MONTANT.
    A system en dessous of the threshold montant which the atteint passe
    de portage at closure. -/
theorem crossing_up (alpha th_up th_down delta : Nat)
    (h_pos : alpha > 0) (h_below : alpha < th_up)
    (h_cross : alpha + delta ≥ th_up)
    (h_delta_pos : delta > 0) :
    classify alpha th_up th_down .ascending = .portage ∧
    classify (alpha + delta) th_up th_down .ascending = .closure := by
  constructor
  · -- Avant : alpha < th_up → portage
    unfold classify
    rw [if_neg (show alpha ≠ 0 from by omega)]
    rw [if_pos (rfl : Direction.ascending = Direction.ascending)]
    rw [if_neg (show ¬(alpha ≥ th_up) from by omega)]
  · -- After : alpha + delta ≥ th_up → closure
    unfold classify
    rw [if_neg (show alpha + delta ≠ 0 from by omega)]
    rw [if_pos (rfl : Direction.ascending = Direction.ascending)]
    rw [if_pos h_cross]

/-- [∎] LEMME 4b — CROSSING DESCENDANT.
    Un system au-dessus du threshold descendant qui passe en dessous
    quitte la closure. -/
theorem crossing_down (alpha th_up th_down loss : Nat)
    (h_above : alpha ≥ th_down) (h_pos : alpha > 0)
    (h_drop : alpha - loss < th_down)
    (h_remain_pos : alpha - loss > 0) :
    classify alpha th_up th_down .descending = .closure ∧
    classify (alpha - loss) th_up th_down .descending = .portage := by
  constructor
  · -- Avant : alpha ≥ th_down → closure
    unfold classify
    rw [if_neg (show alpha ≠ 0 from by omega)]
    rw [if_neg (show ¬(Direction.descending = Direction.ascending) from by decide)]
    rw [if_pos (show alpha ≥ th_down from h_above)]
  · -- After : alpha - loss < th_down → portage
    unfold classify
    rw [if_neg (show alpha - loss ≠ 0 from by omega)]
    rw [if_neg (show ¬(Direction.descending = Direction.ascending) from by decide)]
    rw [if_neg (show ¬(alpha - loss ≥ th_down) from by omega)]

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. Instability of the zone intermediate
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Consequence (ii) de R-XVIII : la zone entre les thresholds est instable.

  A system in the zone of hysteresis en phase ascendante :
  - ne peut PAS construire davantage (plafond)
  - is condamné at decreasesre (Lemme 1)
  - son maintien exige un investissement continu

  This is pourquoi the systems ne restent pas in the zone :
  ils the traversent rapidement (observation empirique : médiane 1 mois).
-/

/-- [∎] INSTABILITY ASCENDANTE — A system actif which cannot
    construire subit a triple piège :
    1. Il ne peut pas monter (plafond de construction)
    2. Il finira par descendre (duration de vie finie, Lemme 1)
    3. Rester au same level coste (pas gratuit)
    Note : h_maintain retiré — the conclusion not the utilise not.
    The theorem is PLUS FORT that the instability of zone : il s'applique
    at tout system actif non-constructible, same hors zone. -/
theorem ascending_instability (s : TransitionSystem) (n : Nat)
    (h_not_build : ¬can_build_at s n)
    (h_active : n > 0) :
    ¬can_build_at s n ∧
    (∃ k, k * s.degradation > n) ∧
    n * s.maintenance_cost > 0 := by
  refine ⟨h_not_build, ?_, ?_⟩
  · exact alpha_exhaustion n s.degradation s.degradation_pos
  · exact mul_pos_of_pos n s.maintenance_cost h_active s.maintenance_pos

/-- [∎] INERTIA DE LA CLOSURE — Si le system peut construire au
    level n, il peut maintenir au level n+1.
    Preuve : build(n) paie n*m + c. maintain(n+1) paie (n+1)*m = n*m + m.
    Comme c > m (asymmetry), n*m + c > n*m + m, donc
    si n*m + c ≤ cap alors n*m + m ≤ cap. -/
theorem closure_inertia (s : TransitionSystem) (n : Nat)
    (h_build : can_build_at s n) :
    can_maintain_at s (n + 1) := by
  unfold can_build_at at h_build
  unfold can_maintain_at
  -- (n+1) * m = n * m + m  (Nat.succ_mul)
  rw [Nat.succ_mul]
  -- Goal : n * m + m ≤ cap
  -- From h_build : n * m + c ≤ cap, and c > m (asymmetry)
  have := s.asymmetry
  omega

/-- [∎] PAS DE MAINTIEN GRATUIT — Si le level est actif (n > 0),
    la maintenance a un cost strictly positif.
    The default n'is jamais neutre for a system en acte. -/
theorem no_free_maintenance (s : TransitionSystem) (n : Nat)
    (h_active : n > 0) :
    n * s.maintenance_cost > 0 :=
  mul_pos_of_pos n s.maintenance_cost h_active s.maintenance_pos

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. R-XVIII — Assemblage
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## R-XVIII — Theorem de synthesis

  Pour tout TransitionSystem (being fini en acte sous cost et pression) :

  (a) α decreases by default en the absence of regeneration active [Lemme 1]
  (b) all what is constructible is maintenable, not the inverse [Lemme 2]
  (c) il exists une zone maintenable-non-constructible [Lemme 3, hysteresis]

  Consequences :
  (i)  les transitions montantes exigent un surcost de construction [Lemme 2]
  (ii) the zone intermediate is instable for the ascendants [§8]

  Hors Lean (≈₁) :
  (iii) a population under pressions variées exhibe a distribution
        bimodal of the degree of closure [hypothesis populationnelle]
-/

/-- [∎] R-XVIII — INTER-REGIME DYNAMICS.
    Theorem de synthesis combinant les quatre lemmes. -/
theorem rxviii (s : TransitionSystem) :
    -- (a+b) Inclusion stricte : constructible ⊂ maintenable
    (∀ n, can_build_at s n → can_maintain_at s n) ∧
    -- (c) Zone d'hysteresis non vide
    (∃ n, can_maintain_at s n ∧ ¬can_build_at s n) ∧
    -- (ii) Duration de vie finie de toute constraint non maintenue
    (∀ endogenous, ∃ k, k * s.degradation > endogenous) :=
  ⟨build_implies_maintain s,
   hysteresis_zone_exists s,
   fun e => alpha_exhaustion e s.degradation s.degradation_pos⟩

/-- [∎] R-XVIII consequence (i) — L'inertia de la closure.
    All level constructible donne accès at the level maintenu at the-dessus.
    But the level maintenu at the-dessus is not necessaryment
    constructible : il can se trouver in the zone of hysteresis. -/
theorem rxviii_consequence_i (s : TransitionSystem) :
    -- Si on peut construire at n, on peut maintenir at n+1
    (∀ n, can_build_at s n → can_maintain_at s (n + 1)) ∧
    -- Mais maintenir at n+1 n'implique pas pouvoir construire at n+1
    (∃ n, can_maintain_at s n ∧ ¬can_build_at s n) :=
  ⟨fun n h => closure_inertia s n h, hysteresis_zone_exists s⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- SUMMARY
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Inventaire

  | # | Theorem | Section | Contenu |
  |---|----------|---------|---------|
  | 1 | aggregate_active_exclusive | §1 | α=0 et α>0 exclusive |
  | 2 | aggregate_active_exhaustive | §1 | α=0 ou α>0 |
  | 3 | alpha_decay | §3 | Lemme 1a : drain > endogenous → épuisé |
  | 4 | alpha_exhaustion | §3 | Lemme 1b : ∃ k, k*deg > endogenous |
  | 5 | build_implies_maintain | §4 | Lemme 2a : constructible → maintenable |
  | 6 | construction_overhead | §4 | Lemme 2b : surcost > 0 |
  | 7 | maintain_at_zero | §4 | Lemme 2c : level 0 maintenable |
  | 8 | maintain_monotone | §4 | Lemme 2d : maintenable monotone ↓ |
  | 9 | build_monotone | §4 | Lemme 2e : constructible monotone ↓ |
  | 10 | mul_pos_of_pos | §5 | Utilitaire : a>0 ∧ b>0 → a*b>0 |
  | 11 | hysteresis_zone_exists | §5 | Lemme 3 : ∃ gap (CORE) |
  | 12 | maintain_not_implies_build | §5 | Inclusion stricte |
  | 13 | regime_depends_on_history | §6 | Hysteresis qualitative |
  | 14 | crossing_up | §7 | Lemme 4a : crossing montant |
  | 15 | crossing_down | §7 | Lemme 4b : crossing descendant |
  | 16 | ascending_instability | §8 | Zone instable (ascendant) |
  | 17 | closure_inertia | §8 | Inertie : build(n) → maintain(n+1) |
  | 18 | no_free_maintenance | §8 | Pas de maintien gratuit |
  | 19 | rxviii | §9 | R-XVIII synthesis |
  | 20 | rxviii_consequence_i | §9 | Consequence (i) |

  **20 theorems, 0 sorry, 0 import.**

  ### Statut inferential
  - Lemme 1 (decay) : ∎ — de IV + IX
  - Lemme 2 (asymmetry) : ∎ — structural (champ asymmetry)
  - Lemme 3 (hysteresis) : ∎ — of Lemme 2 + division entière
  - Lemme 4 (bifurcation) : ∎ — analyse de cas
  - (i) inertia : ∎ — de Lemme 2 + Lemme 3
  - (ii) instability : ∎ — de Lemme 1 + Lemme 3
  - (iii) bimodalité : ≈₁ — hors Lean (hypothesis populationnelle)

  ### Enrichissement axiomatic
  - TransitionSystem enrichit IV avec deux costs (construction, maintenance)
  - L'asymmetry (construction > maintenance) est un CHAMP, pas un theorem
  - This is a choix délibéré : driftr the asymmetry of IV pur exigerait
    a formalisation of the indétermination of the acte of création (faisable,
    but hors scope of this première formalisation)
  - The asymmetry pourrait being promue en theorem in a version future
    if a formalisation of « constraint structurelle on the acte » is addede

  ### Contact empirique (Gosme 2025, arXiv:2512.09352)
  - Bimodality of Γ (dip p=0.013) ← hysteresis (Lemme 3) → (iii) ≈₁
  - Zone traversée en 1 mois ← instability (§8) → (ii) ∎
  - 41% of régressions ← decay by default (Lemme 1) → (a) ∎
  - Coupling ratio 0.65→0.94 ← α grows → definition de α
  - Variance collapse 1.77× ← bassin étroit at the-dessus of α↑ → Lemme 3 + §8
-/

end RXVIII