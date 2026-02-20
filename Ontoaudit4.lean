import Lean

/-!
# ONTODYNAMIQUE — PHASE 4 : CADRE UNIFIÉ (post-CR v3)

Le primitif `incorporation` unifie Phases 1–3.
I-β : structMeasure(b) + cost(a,b) ≤ structMeasure(a) + incorporation(a,b)

## Note architecturale : ax_III — encodage pairwise

III dans le texte : « Aucune isolation causale entre déterminations
n'est absolue. » Encodé pairwise : tout être fini est couplé à toute
autre détermination (y compris le Tout).

IX-bis (pression constitutive du Tout) est un THÉORÈME dérivé de
ax_III + ax_I_α_exists + ax_I_α_not_finite. Il n'est pas un axiome.
Le système a 5 axiomes ontodynamiques (I–VI). Le code aussi.

## Note architecturale : statut de `incorporation`

Le champ `incorporation : Det → Det → Nat` encode la possibilité que certaines
transformations aient un bilan structurel non-négatif. Dans le texte
philosophique, ce concept est nommé **V-bis** et a le statut **◇**
(constructibilité).

### Pourquoi primitif et non dérivé ?

Les axiomes I–VI forment une axiomatique de la dissolution : coût (IV),
incompatibilité (V), exclusion (VI), finitude (VIII), incompressibilité
(VIII-bis). Aucun axiome ne pose que l'extériorité peut être source de gain
structurel. La compensation est constructible (V-bis ◇) mais pas dérivable ∎.

Un modèle valide de I–VI SANS compensation (incorporation = 0 partout) est
le modèle où tout se dissout (ThreeDetDiss ci-dessous). C'est conforme aux
axiomes. La compensation est un fait de domaine, pas une nécessité axiomatique.

### Correspondances texte ↔ code

| Texte                     | Code                              | Force |
|---------------------------|-----------------------------------|-------|
| III (non-isolation)       | `ax_III` (pairwise)               | ∎     |
| I-β (endogénéité)         | `ax_I_β` (bilan sur marge propre) | ∎     |
| IV (économie)             | `ax_IV` (cost > 0)                | ∎     |
| V-bis (compensation ◇)   | `incorporation` (champ)           | ◇     |
| IX-bis (pression du Tout) | `IX_bis` (THÉORÈME, pas axiome)   | ∎     |
| XXXII (métabolisation)    | instanciation : incorp > 0        | ∎     |

### Asymétrie axiomatique

`step_without_incorp` (décroissance quand incorporation = 0) est DÉRIVÉ de
`ax_I_β` + `ax_IV`. C'est le régime par défaut — la dissolution. La
compensation (incorporation > 0) est une possibilité non dérivée — elle
dépend du modèle.
-/

namespace OntoUnified

-- ============================================================
-- SECTION 1 : AXIOMATIQUE
-- ============================================================

/-! ### extDegree — aplatissement couplage/incompatibilité

Dans le texte, III (couplage) et VI (exclusion/incompatibilité) sont
des concepts distincts :
- III : tout est causalement relié (connexion)
- VI : toute détermination exclut (incompatibilité)

L'incompatibilité implique le couplage, pas l'inverse. Dans le code,
`extDegree` encode les deux. Conséquence : `ax_VI_persist`
(excludes → extDegree > 0) est logiquement redondant avec `ax_III`
(pairwise → extDegree > 0). La redondance est un artefact de
l'aplatissement, pas une erreur du texte.

Un encodage plus riche séparerait `coupling` (III) et
`incompatibility` (VI). Raffinement futur optionnel — aucun
théorème actuel n'en dépend.

Le `b ≠ .whole` dans `excludes` (ThreeDet, ThreeDetDiss) est
philosophiquement correct : on n'exclut pas le Tout, on est en
tension constitutive avec lui (IX-bis). L'exclusion est un rapport
entre déterminations finies. -/

class Ontology (Det : Type) where
  structMeasure : Det → Nat
  transforms : Det → Det → Prop
  cost : Det → Det → Nat
  extDegree : Det → Det → Nat
  excludes : Det → Det → Prop
  isWhole : Det → Prop
  isFinite : Det → Prop
  annihilationCost : Det → Nat
  incorporation : Det → Det → Nat

  ax_I_α_exists : ∃ w, isWhole w
  ax_I_α_not_finite : ∀ w, isWhole w → ¬ isFinite w
  ax_I_β : ∀ a b, transforms a b → a ≠ b →
    structMeasure b + cost a b ≤ structMeasure a + incorporation a b
  -- ── III : Non-isolation causale (pairwise) ──
  -- « Aucune isolation causale entre déterminations n'est absolue. »
  -- Encodé pairwise : tout être fini est couplé à toute autre
  -- détermination (y compris le Tout). IX-bis en découle.
  ax_III : ∀ a, isFinite a → ∀ b, a ≠ b → extDegree a b > 0
  ax_IV : ∀ a b, transforms a b → a ≠ b → cost a b > 0
  ax_V : ∀ a, isFinite a →
    ∃ b, extDegree a b > 0 ∧
    cost a b > 0 ∧ cost a b < annihilationCost a ∧
    transforms a b ∧ a ≠ b
  ax_VI : ∀ a, isFinite a → ∃ b, excludes a b
  ax_VI_persist : ∀ a b, excludes a b → extDegree a b > 0
  bridge_finite : ∀ a, isFinite a → ¬ isWhole a
  bridge_coupling_acts : ∀ a b, isFinite a → extDegree a b > 0 →
    ∃ a', transforms a a' ∧ a ≠ a' ∧ incorporation a a' = 0

variable {Det : Type} [Ontology Det]


-- ============================================================
-- SECTION 2 : LEMMES DE PHASE 1
-- ============================================================

theorem VII (w : Det) (hw : Ontology.isWhole w) : ¬ Ontology.isFinite w :=
  Ontology.ax_I_α_not_finite w hw

theorem IX (a : Det) (ha : Ontology.isFinite a) :
    ∃ b, b ≠ a ∧ Ontology.extDegree a b > 0 := by
  have ⟨w, hw⟩ := Ontology.ax_I_α_exists (Det := Det)
  have hne : a ≠ w := fun h => absurd (h ▸ ha) (Ontology.ax_I_α_not_finite w hw)
  exact ⟨w, hne.symm, Ontology.ax_III a ha w hne⟩

theorem step_without_incorp (a b : Det)
    (h_trans : Ontology.transforms a b) (h_ne : a ≠ b)
    (h_no_incorp : Ontology.incorporation a b = 0) :
    Ontology.structMeasure b < Ontology.structMeasure a := by
  have h_balance := Ontology.ax_I_β a b h_trans h_ne
  have h_cost := Ontology.ax_IV a b h_trans h_ne
  rw [h_no_incorp] at h_balance; omega

theorem XV_pressure (a : Det) (ha : Ontology.isFinite a) :
    ∃ a', Ontology.transforms a a' ∧ a ≠ a' ∧
    Ontology.structMeasure a' < Ontology.structMeasure a := by
  have ⟨b, hne, hb_ext⟩ := IX a ha
  have ⟨a', h_trans, h_ne, h_no_incorp⟩ :=
    Ontology.bridge_coupling_acts a b ha hb_ext
  exact ⟨a', h_trans, h_ne, step_without_incorp a a' h_trans h_ne h_no_incorp⟩

/-- [THM] IX-bis : Le Tout exerce une pression constitutive sur le fini.
    DÉRIVÉ de ax_III (pairwise) + ax_I_α_exists + ax_I_α_not_finite.
    N'est PAS un axiome — c'est un corollaire de III. -/
theorem IX_bis (a : Det) (ha : Ontology.isFinite a) :
    ∃ w, Ontology.isWhole w ∧ Ontology.extDegree a w > 0 := by
  have ⟨w, hw⟩ := Ontology.ax_I_α_exists (Det := Det)
  have hne : a ≠ w := fun h => absurd (h ▸ ha) (Ontology.ax_I_α_not_finite w hw)
  exact ⟨w, hw, Ontology.ax_III a ha w hne⟩

/-- [THM] IX-bis → pression destructurante.
    La pression constitutive du Tout produit une altération destructurante.
    Combine IX-bis + bridge_coupling_acts + step_without_incorp. -/
theorem IX_bis_pressure (a : Det) (ha : Ontology.isFinite a) :
    ∃ w, Ontology.isWhole w ∧ Ontology.extDegree a w > 0 ∧
    ∃ a', Ontology.transforms a a' ∧ a ≠ a' ∧
    Ontology.structMeasure a' < Ontology.structMeasure a := by
  have ⟨w, hw, hext⟩ := IX_bis a ha
  have ⟨a', h_trans, h_ne, h_no_incorp⟩ :=
    Ontology.bridge_coupling_acts a w ha hext
  exact ⟨w, hw, hext, a', h_trans, h_ne,
    step_without_incorp a a' h_trans h_ne h_no_incorp⟩


-- ============================================================
-- SECTION 3 : TRAJECTOIRES
-- ============================================================

structure Trajectory (Det : Type) [Ontology Det] where
  state : Nat → Det
  h_transforms : ∀ n, Ontology.transforms (state n) (state (n + 1))
  h_ne : ∀ n, state n ≠ state (n + 1)

def Trajectory.marge (t : Trajectory Det) (n : Nat) : Nat :=
  Ontology.structMeasure (t.state n)

def Trajectory.persists (t : Trajectory Det) : Prop :=
  ∀ n, t.marge n > 0

def Trajectory.isDestructAt (t : Trajectory Det) (n : Nat) : Prop :=
  Ontology.incorporation (t.state n) (t.state (n + 1)) = 0

def Trajectory.isCompensAt (t : Trajectory Det) (n : Nat) : Prop :=
  Ontology.incorporation (t.state n) (t.state (n + 1)) > 0


-- ============================================================
-- SECTION 4 : DESCENTE ET SEGMENTS
-- ============================================================

theorem no_infinite_descent (f : Nat → Nat) (h : ∀ n, f (n + 1) < f n) :
    False := by
  suffices aux : ∀ n, f n + n ≤ f 0 by
    have := aux (f 0 + 1); omega
  intro n; induction n with
  | zero => omega
  | succ k ih => have := h k; omega

theorem destruct_step_drops (t : Trajectory Det) (n : Nat)
    (h_dest : t.isDestructAt n) :
    t.marge (n + 1) < t.marge n :=
  step_without_incorp (t.state n) (t.state (n + 1))
    (t.h_transforms n) (t.h_ne n) h_dest

def Trajectory.pureSegment (t : Trajectory Det) (start len : Nat) : Prop :=
  ∀ k, k < len → t.isDestructAt (start + k)

theorem segment_bound (t : Trajectory Det)
    (start len : Nat) (h_pure : t.pureSegment start len) :
    t.marge (start + len) + len ≤ t.marge start := by
  induction len with
  | zero => simp [Nat.add_zero]
  | succ k ih =>
    have ih_app := ih (fun j hj => h_pure j (by omega))
    have h_step := destruct_step_drops t (start + k) (h_pure k (by omega))
    unfold Trajectory.marge at ih_app h_step ⊢
    have h_eq : start + (k + 1) = start + k + 1 := by omega
    rw [h_eq]; omega


-- ============================================================
-- SECTION 5 : XXVII
-- ============================================================

theorem XXVII_positive (t : Trajectory Det)
    (h_persists : t.persists) (N : Nat) :
    ∃ n, n ≥ N ∧ t.isCompensAt n :=
  Classical.byContradiction fun h_no_comp => by
    have h_all : ∀ n, n ≥ N → t.isDestructAt n := by
      intro n hn
      unfold Trajectory.isDestructAt Trajectory.isCompensAt at *
      cases h_eq : Ontology.incorporation (t.state n) (t.state (n + 1)) with
      | zero => rfl
      | succ k => exact absurd ⟨n, hn, by omega⟩ h_no_comp
    let L := t.marge N + 1
    have h_pure : t.pureSegment N L := fun k _ => h_all (N + k) (by omega)
    have h_bound := segment_bound t N L h_pure
    have := h_persists (N + L); omega

theorem XXVII_complete (t : Trajectory Det) :
    t.persists ∨ ∃ n, t.marge n = 0 := by
  rcases Classical.em t.persists with h | h
  · exact Or.inl h
  · exact Or.inr (by
      have hex : ∃ n, ¬ (t.marge n > 0) :=
        Classical.byContradiction fun hall => h (fun n =>
          Classical.byContradiction fun hn => hall ⟨n, hn⟩)
      let ⟨n, hn⟩ := hex; exact ⟨n, by omega⟩)


-- ============================================================
-- SECTION 6 : CLÔTURE, PORTAGE, AGRÉGAT
-- ============================================================

def Trajectory.isClosed (t : Trajectory Det) : Prop :=
  t.persists ∧ ∀ n, t.isCompensAt n → ∃ m, m < n ∧ t.isDestructAt m

def Trajectory.isPortage (t : Trajectory Det) : Prop :=
  t.persists ∧ ∃ n, t.isCompensAt n ∧ ¬ ∃ m, m < n ∧ t.isDestructAt m

def Trajectory.isAggregate (t : Trajectory Det) : Prop :=
  ∀ n, t.isDestructAt n


-- ============================================================
-- SECTION 7 : THÉORÈMES FONDAMENTAUX
-- ============================================================

theorem aggregate_dissolves (t : Trajectory Det)
    (h_agg : t.isAggregate) : ¬ t.persists := by
  intro h_persists
  exact no_infinite_descent t.marge (fun n => destruct_step_drops t n (h_agg n))

theorem R_XVI_dichotomy (t : Trajectory Det) (h_persists : t.persists) :
    t.isClosed ∨ t.isPortage := by
  rcases Classical.em
    (∀ n, t.isCompensAt n → ∃ m, m < n ∧ t.isDestructAt m) with h | h
  · exact Or.inl ⟨h_persists, h⟩
  · right; refine ⟨h_persists, ?_⟩
    exact Classical.byContradiction fun h_none => h fun n hn =>
      Classical.byContradiction fun h_no_ant => h_none ⟨n, hn, h_no_ant⟩

theorem XXXVIII_partition (t : Trajectory Det) (n : Nat) :
    t.isDestructAt n ∨ t.isCompensAt n := by
  unfold Trajectory.isDestructAt Trajectory.isCompensAt
  cases Ontology.incorporation (t.state n) (t.state (n + 1)) with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (by omega)

theorem XXXVIII_nondegen (t : Trajectory Det)
    (h_persists : t.persists) (N : Nat) :
    ∃ n, n ≥ N ∧ t.isCompensAt n :=
  XXVII_positive t h_persists N

theorem XXXIX_constitutive (t : Trajectory Det)
    (h_persists : t.persists) (N : Nat)
    (h_all_destruct : ∀ n, n ≥ N → t.isDestructAt n) : False := by
  have h_pure : t.pureSegment N (t.marge N + 1) :=
    fun k _ => h_all_destruct (N + k) (by omega)
  have h_bound := segment_bound t N (t.marge N + 1) h_pure
  have := h_persists (N + (t.marge N + 1)); omega

theorem XI_a_cost (a b c : Det)
    (hab : Ontology.transforms a b) (hbc : Ontology.transforms b c)
    (hab_ne : a ≠ b) (hbc_ne : b ≠ c) :
    Ontology.cost a b + Ontology.cost b c ≥ 2 := by
  have h1 := Ontology.ax_IV a b hab hab_ne
  have h2 := Ontology.ax_IV b c hbc hbc_ne; omega


-- ============================================================
-- SECTION 8 : MODÈLE CONCRET — ThreeDet
-- ============================================================

-- Trois états :
--   high (marge 2) — l'être structuré
--   mid  (marge 1) — l'être altéré
--   whole (marge 0) — le Tout (non fini, pas d'activité propre)
--
-- Transitions :
--   high → mid : destructurant (incorp = 0), marge 2 → 1
--   mid → high : compensatoire (incorp = 2), marge 1 → 2
--   high → whole : dissolution (incorp = 0), marge 2 → 0
--   mid → whole : dissolution (incorp = 0), marge 1 → 0
--
-- whole est NON FINI : pas de transition sortante.
-- bridge_coupling_acts : high peut aller vers mid (incorp=0),
--                        mid peut aller vers whole (incorp=0).

inductive ThreeDet where | high | mid | whole
deriving DecidableEq

-- Helpers @[simp] pour que Lean réduise les champs d'instance
@[simp] def smMeasure : ThreeDet → Nat | .high => 2 | .mid => 1 | .whole => 0
@[simp] def smCost (_ _ : ThreeDet) : Nat := 1
@[simp] def smIncorp : ThreeDet → ThreeDet → Nat | .mid, .high => 2 | _, _ => 0
@[simp] def smTrans : ThreeDet → ThreeDet → Prop
  | .whole, _ => False | a, b => a ≠ b
@[simp] def smExt (a b : ThreeDet) : Nat :=
  if a ≠ b ∧ a ≠ .whole then 1 else 0
@[simp] def smExcludes (a b : ThreeDet) : Prop :=
  a ≠ b ∧ a ≠ .whole ∧ b ≠ .whole

instance : Ontology ThreeDet where
  structMeasure := smMeasure
  transforms := smTrans
  cost := smCost
  extDegree := smExt
  excludes := smExcludes
  isWhole := fun a => a = .whole
  isFinite := fun a => a ≠ .whole
  annihilationCost := fun _ => 3
  incorporation := smIncorp

  ax_I_α_exists := ⟨.whole, rfl⟩
  ax_I_α_not_finite := by intro w hw hf; cases w <;> simp_all

  ax_I_β := by
    intro a b ht hne
    cases a <;> cases b <;> simp_all [smMeasure, smCost, smIncorp, smTrans]

  ax_III := by
    intro a ha b hne
    show smExt a b > 0
    simp [smExt, hne, ha]

  ax_IV := by intro a b _ _; simp [smCost]

  ax_V := by
    intro a ha
    cases a with
    | whole => exact absurd rfl ha
    | high =>
      refine ⟨.mid, ?_, ?_, ?_, ?_, ?_⟩
      · simp [smExt]
      · simp [smCost]
      · simp [smCost]
      · show smTrans .high .mid; exact ThreeDet.noConfusion
      · exact ThreeDet.noConfusion
    | mid =>
      refine ⟨.high, ?_, ?_, ?_, ?_, ?_⟩
      · simp [smExt]
      · simp [smCost]
      · simp [smCost]
      · show smTrans .mid .high; exact fun h => ThreeDet.noConfusion h
      · exact fun h => ThreeDet.noConfusion h

  ax_VI := by
    intro a ha
    cases a with
    | whole => exact absurd rfl ha
    | high =>
      refine ⟨.mid, ?_, ?_, ?_⟩
      · exact ThreeDet.noConfusion
      · exact ThreeDet.noConfusion
      · exact ThreeDet.noConfusion
    | mid =>
      refine ⟨.high, ?_, ?_, ?_⟩
      · exact fun h => ThreeDet.noConfusion h
      · exact ThreeDet.noConfusion
      · exact ThreeDet.noConfusion

  ax_VI_persist := by
    intro a b ⟨h1, h2, _⟩
    show smExt a b > 0
    simp [smExt, h1, h2]

  bridge_finite := by intro a ha hw; cases a <;> simp_all

  bridge_coupling_acts := by
    intro a b ha _
    cases a with
    | whole => exact absurd rfl ha
    | high =>
      -- high → mid : incorp = 0
      refine ⟨.mid, ?_, ?_, ?_⟩
      · show smTrans .high .mid; exact ThreeDet.noConfusion
      · exact ThreeDet.noConfusion
      · show smIncorp .high .mid = 0; rfl
    | mid =>
      -- mid → whole : incorp = 0, mais whole n'est pas fini
      -- C'est la dissolution — le bridge ici signifie que
      -- le couplage PEUT produire une altération purement destructurante.
      refine ⟨.whole, ?_, ?_, ?_⟩
      · show smTrans .mid .whole; exact ThreeDet.noConfusion
      · exact ThreeDet.noConfusion
      · show smIncorp .mid .whole = 0; rfl


-- ============================================================
-- SECTION 9 : TRAJECTOIRE OSCILLANTE
-- ============================================================

def oscillating : Trajectory ThreeDet where
  state := fun n => if n % 2 = 0 then .high else .mid
  h_transforms := by
    intro n
    show smTrans (if n % 2 = 0 then .high else .mid)
      (if (n + 1) % 2 = 0 then .high else .mid)
    split <;> split <;> simp_all [smTrans] <;> omega
  h_ne := by
    intro n
    show (if n % 2 = 0 then ThreeDet.high else ThreeDet.mid) ≠
      (if (n + 1) % 2 = 0 then ThreeDet.high else ThreeDet.mid)
    split <;> split <;> simp_all <;> omega

theorem oscillating_destruct_even (n : Nat) (h : n % 2 = 0) :
    oscillating.isDestructAt n := by
  show smIncorp (if n % 2 = 0 then ThreeDet.high else ThreeDet.mid)
    (if (n + 1) % 2 = 0 then ThreeDet.high else ThreeDet.mid) = 0
  rw [if_pos h, if_neg (show ¬ ((n + 1) % 2 = 0) from by omega)]
  simp

theorem oscillating_compens_odd (n : Nat) (h : n % 2 = 1) :
    oscillating.isCompensAt n := by
  show smIncorp (if n % 2 = 0 then ThreeDet.high else ThreeDet.mid)
    (if (n + 1) % 2 = 0 then ThreeDet.high else ThreeDet.mid) > 0
  rw [if_neg (show ¬ (n % 2 = 0) from by omega),
      if_pos (show (n + 1) % 2 = 0 from by omega)]
  simp

theorem oscillating_persists : oscillating.persists := by
  intro n
  show smMeasure (if n % 2 = 0 then ThreeDet.high else ThreeDet.mid) > 0
  split <;> simp

theorem oscillating_is_closed :
    ∀ n, oscillating.isCompensAt n →
    ∃ m, m < n ∧ oscillating.isDestructAt m := by
  intro n hn
  have h_odd : n % 2 = 1 := by
    have h_lt : n % 2 < 2 := Nat.mod_lt n (by omega)
    have h_ne_zero : n % 2 ≠ 0 := by
      intro h_even
      have h_dest := oscillating_destruct_even n h_even
      unfold Trajectory.isDestructAt at h_dest
      unfold Trajectory.isCompensAt at hn
      omega
    omega
  exact ⟨n - 1, by omega, oscillating_destruct_even (n - 1) (by omega)⟩


-- ============================================================
-- SECTION 10 : V-bis ◇ — CONSTRUCTIBILITÉ COMPENSATOIRE
-- ============================================================

/-- [WIT] V-bis : il existe des modèles où incorporation > 0.
    Force : ◇ (constructibilité) — pas dérivable des axiomes I–VI.
    Le témoin est ThreeDet (mid → high, incorporation = 2). -/
theorem V_bis_witness :
    ∃ (a b : ThreeDet), Ontology.incorporation a b > 0 :=
  ⟨.mid, .high, by show smIncorp .mid .high > 0; simp⟩


-- ============================================================
-- SECTION 11 : MODÈLE DISSOLUTION PURE (témoin que V-bis est ◇)
-- ============================================================

-- ThreeDetDiss : comme ThreeDet, mais incorporation = 0 PARTOUT.
-- high → mid (destruction), mid → whole (dissolution), high → whole.
-- PAS de mid → high (pas de compensation).
-- Ce modèle satisfait I–VI. Aucune clôture n'y est possible.
-- Son existence PROUVE que V-bis n'est pas ∎.

inductive ThreeDetDiss where | high | mid | whole
deriving DecidableEq

@[simp] def sdMeasure : ThreeDetDiss → Nat | .high => 2 | .mid => 1 | .whole => 0
@[simp] def sdCost (_ _ : ThreeDetDiss) : Nat := 1
@[simp] def sdIncorp (_ _ : ThreeDetDiss) : Nat := 0  -- ← ZERO PARTOUT
-- Transitions : high→mid, high→whole, mid→whole. Pas de mid→high.
@[simp] def sdTrans : ThreeDetDiss → ThreeDetDiss → Prop
  | .high, .mid => True
  | .high, .whole => True
  | .mid, .whole => True
  | _, _ => False
@[simp] def sdExt (a b : ThreeDetDiss) : Nat :=
  if a ≠ b ∧ a ≠ .whole then 1 else 0
@[simp] def sdExcludes (a b : ThreeDetDiss) : Prop :=
  a ≠ b ∧ a ≠ .whole ∧ b ≠ .whole

instance : Ontology ThreeDetDiss where
  structMeasure := sdMeasure
  transforms := sdTrans
  cost := sdCost
  extDegree := sdExt
  excludes := sdExcludes
  isWhole := fun a => a = .whole
  isFinite := fun a => a ≠ .whole
  annihilationCost := fun _ => 3
  incorporation := sdIncorp

  ax_I_α_exists := ⟨.whole, rfl⟩
  ax_I_α_not_finite := by intro w hw hf; cases w <;> simp_all

  ax_I_β := by
    intro a b ht hne
    cases a <;> cases b <;> simp_all [sdMeasure, sdCost, sdIncorp, sdTrans]

  ax_III := by
    intro a ha b hne
    show sdExt a b > 0
    simp [sdExt, hne, ha]

  ax_IV := by intro a b _ _; simp [sdCost]

  ax_V := by
    intro a ha; cases a with
    | whole => exact absurd rfl ha
    | high =>
      -- high → mid : altération partielle (cost = 1 < 3 = annihilationCost)
      refine ⟨.mid, ?_, ?_, ?_, ?_, ?_⟩
      · simp [sdExt]
      · simp [sdCost]
      · simp [sdCost]
      · show sdTrans .high .mid; trivial
      · exact ThreeDetDiss.noConfusion
    | mid =>
      -- mid → whole : cost = 1 < 3 = annihilationCost. V satisfait.
      refine ⟨.whole, ?_, ?_, ?_, ?_, ?_⟩
      · simp [sdExt]
      · simp [sdCost]
      · simp [sdCost]
      · show sdTrans .mid .whole; trivial
      · exact ThreeDetDiss.noConfusion

  ax_VI := by
    intro a ha; cases a with
    | whole => exact absurd rfl ha
    | high =>
      refine ⟨.mid, ?_, ?_, ?_⟩
      · exact ThreeDetDiss.noConfusion
      · exact ThreeDetDiss.noConfusion
      · exact ThreeDetDiss.noConfusion
    | mid =>
      refine ⟨.high, ?_, ?_, ?_⟩
      · exact fun h => ThreeDetDiss.noConfusion h
      · exact ThreeDetDiss.noConfusion
      · exact ThreeDetDiss.noConfusion

  ax_VI_persist := by
    intro a b ⟨h1, h2, _⟩
    show sdExt a b > 0
    simp [sdExt, h1, h2]

  bridge_finite := by intro a ha hw; cases a <;> simp_all

  bridge_coupling_acts := by
    intro a b ha _; cases a with
    | whole => exact absurd rfl ha
    | high =>
      refine ⟨.mid, ?_, ?_, ?_⟩
      · show sdTrans .high .mid; trivial
      · exact ThreeDetDiss.noConfusion
      · show sdIncorp .high .mid = 0; rfl
    | mid =>
      refine ⟨.whole, ?_, ?_, ?_⟩
      · show sdTrans .mid .whole; trivial
      · exact ThreeDetDiss.noConfusion
      · show sdIncorp .mid .whole = 0; rfl

/-- [THM] Dans ThreeDetDiss, aucune trajectoire infinie n'existe.    Toute transformation est destructurante (incorporation = 0 partout).
    Donc toute trajectoire est un agrégat, et tout agrégat se dissout. -/
theorem ThreeDetDiss_all_destruct (t : Trajectory ThreeDetDiss) (n : Nat) :
    t.isDestructAt n := by
  show sdIncorp (t.state n) (t.state (n + 1)) = 0; rfl

theorem ThreeDetDiss_no_persistence (t : Trajectory ThreeDetDiss) :
    ¬ t.persists :=
  aggregate_dissolves t (ThreeDetDiss_all_destruct t)


-- ============================================================
-- SECTION 12 : BILAN
-- ============================================================

-- TRONC ∎ (axiomatique de la dissolution) :
--   step_without_incorp     : DÉRIVÉ (I-β + IV) — régime par défaut
--   XV_pressure             : PROUVÉ — pression destructurante (III + bridge)
--   IX_bis                  : DÉRIVÉ — pression constitutive du Tout (ax_III + I-α)
--   IX_bis_pressure         : DÉRIVÉ — Tout → altération destructurante
--   XXVII_positive          : PROUVÉ — persistance ⇒ compensation récurrente
--   XXVII_complete          : PROUVÉ — disjonction inconditionnelle
--   XXXIX_constitutive      : PROUVÉ — dissolution pure impossible si persistance
--   aggregate_dissolves     : PROUVÉ — agrégat pur se dissout
--
-- CONSTRUCTIBILITÉ ◇ :
--   V_bis_witness           : ThreeDet (mid→high, incorp=2) — la compensation EXISTE
--   ThreeDetDiss_no_persist : sans compensation, tout se dissout — V-bis n'est pas ∎
--
-- CLÔTURE COMME EXCEPTION :
--   R_XVI_dichotomy         : persistant = clôture ∨ portage
--   oscillating_persists    : témoin de clôture
--   oscillating_is_closed   : compensation après destruction
--
-- SORRY : 0

end OntoUnified

#eval IO.println "\n=======================================================\n ✅ ONTO-PHASE 4 : CADRE UNIFIÉ (post-CR v3)\n=======================================================\n AXIOMATIQUE DE LA DISSOLUTION (tronc ∎) :\n [THM] step_without_incorp         : DÉRIVÉ (I-β + IV)\n [THM] XV_pressure                 : DÉRIVÉ (III + bridge) — pression relationnelle\n [THM] IX_bis                      : DÉRIVÉ (III + I-α) — pression constitutive\n [THM] IX_bis_pressure             : DÉRIVÉ — Tout → altération destructurante\n [THM] XXVII_positive              : PROUVÉ — persistance ⇒ compensation\n [THM] XXVII_complete              : PROUVÉ — disjonction inconditionnelle\n [THM] XXXIX_constitutive           : PROUVÉ — dissolution si pas de compensation\n [THM] aggregate_dissolves         : PROUVÉ — agrégat pur se dissout\n\n CONSTRUCTIBILITÉ DE LA COMPENSATION (◇) :\n [WIT] V_bis_witness               : ThreeDet (mid→high, incorp=2)\n [MOD] ThreeDetDiss_no_persistence : sans compensation, tout se dissout\n\n CLÔTURE COMME EXCEPTION :\n [THM] R_XVI_dichotomy             : PROUVÉ — persistant = clôture ∨ portage\n [THM] oscillating_persists        : PROUVÉ — témoin de clôture\n [THM] oscillating_is_closed       : PROUVÉ — compensation après destruction\n-------------------------------------------------------\n SORRY : 0\n AXIOMES LEAN : 5 (fidèle au texte) — IX-bis DÉRIVÉ, pas axiome\n DEUX PRESSIONS : constitutive (IX-bis) + relationnelle (XV)\n ASYMÉTRIE : dissolution = défaut (∎), clôture = exception (◇)\n=======================================================\n"

#print axioms OntoUnified.XXVII_positive
#print axioms OntoUnified.XXXVIII_partition
#print axioms OntoUnified.XXXIX_constitutive
#print axioms OntoUnified.R_XVI_dichotomy
#print axioms OntoUnified.step_without_incorp
#print axioms OntoUnified.XV_pressure
#print axioms OntoUnified.IX_bis
#print axioms OntoUnified.IX_bis_pressure
#print axioms OntoUnified.oscillating_persists
#print axioms OntoUnified.oscillating_is_closed
#print axioms OntoUnified.V_bis_witness
#print axioms OntoUnified.ThreeDetDiss_no_persistence
