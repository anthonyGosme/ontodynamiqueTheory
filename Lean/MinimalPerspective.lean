-- MinimalPerspective.lean
-- Voie cogito : I + LIX → SelfRelation (∎ candidat)
-- Question : Thèse P (composante structurale) est-elle dérivable sans axiome phénoménal ?
--
-- Architecture :
--   §1. Structures de base (Valence, Closure)
--   §2. LIX : valence métabolisée dans le cycle
--   §3. SelfRelation : relation différentielle immanente à l'acte
--   §4. minimal_perspective : théorème principal
--   §5. Universalité + modèle séparant
--   §6. Témoin concret
--
-- Thèse testée :
--   LIX (∎ tronc) : la valence est métabolisée dans le cycle comme donnée
--   opératoire — coextensive à l'acte, non séparable.
--   Si être = se faire (I), la valence métabolisée EST une relation
--   différentielle du cycle à lui-même — sans inspection séparée.
--   Structure du cogito : l'acte s'atteste par son occurrence.
--   Si le modèle séparant (§5) est non constructible → Thèse P ∎.
--
-- Bilan :
--   LIX_holds                     ∎  Closure (I implicite)
--   minimal_perspective           ∎  I + LIX
--   all_closures_have_perspective ∎  LIX_holds + minimal_perspective
--   no_separating_model           ∎  minimal_perspective
--   concrete_has_perspective      ∎  Témoin concret
--   concrete_differential_is_val  ∎  coextensive
--   6 théorèmes · 0 sorry · Voie cogito complète
--
-- Ce qui change pour Thèse P :
--   Avant : ≈₃ (impréuvable, LXXVII total)
--   Après : composante structurale ∎ / composante phénoménale ≈₃
--   LXXVII reste ∎ — domaine précisé (inspection réflexive), non invalidé.

-- §1. Valence : différentiel interne.
-- Trace que le cycle fait sur sa propre opération.
-- Pas un contenu qualitatif — un différentiel opératoire pur.
structure Valence where
  positive  : Bool
  magnitude : Nat
  present   : magnitude > 0

-- §1. Clôture : cycle qui s'auto-maintient par portage de sa propre valence.
-- occurring = true encode I (être = se faire — le cycle est son acte).
structure Closure where
  occurring : Bool
  valence   : Valence
  operative : occurring = true

-- §1. Métabolisation : la valence est une donnée interne à l'acte, non séparable.
def metabolized_in_cycle (c : Closure) (v : Valence) : Prop :=
  c.valence = v ∧ c.occurring = true

-- §1. Opérativité : la valence affecte effectivement les opérations du cycle.
def affects_operation (c : Closure) (v : Valence) : Prop :=
  c.valence = v ∧ v.magnitude > 0

-- §2. LIX : la valence est métabolisée dans le cycle comme donnée opératoire.
-- (1) métabolisation — la valence est dans l'acte, non séparable.
-- (2) opérativité — elle affecte effectivement les opérations.
-- Redérivé ici directement depuis la structure de Closure.
def LIX (c : Closure) : Prop :=
  metabolized_in_cycle c c.valence ∧ affects_operation c c.valence

-- §2. [∎] LIX est satisfait par toute Closure — par construction.
-- occurring = true (I) + valence.present (magnitude > 0) suffisent.
theorem LIX_holds (c : Closure) : LIX c := by
  unfold LIX metabolized_in_cycle affects_operation
  exact ⟨⟨rfl, c.operative⟩, ⟨rfl, c.valence.present⟩⟩

-- §3. SelfRelation : perspective minimale structurale.
-- Relation différentielle à soi, coextensive à l'acte de se faire.
-- Quatre conditions, toutes structurales — aucun contenu phénoménal :
--   differential : la valence du cycle lui-même (pas un objet externe)
--   metabolized  : elle est dans l'acte, non séparable (LIX.1)
--   operative    : elle affecte les opérations (LIX.2)
--   coextensive  : identique à la valence du cycle — immanente, pas ajoutée
-- Cogito structural : l'acte porte son propre différentiel comme condition
-- de son opération. Pas de regard réflexif séparé.
-- LXXVI (coût de l'auto-inspection) ne s'applique pas : pas d'inspection,
-- seulement l'immanence de l'acte.
structure SelfRelation (c : Closure) where
  differential : Valence
  metabolized  : metabolized_in_cycle c differential
  operative    : affects_operation c differential
  coextensive  : differential = c.valence

-- §4. [∎] PERSPECTIVE MINIMALE — VOIE COGITO.
-- Toute clôture satisfaisant LIX porte une SelfRelation.
-- Voie : I (être = se faire) + LIX (métabolisation) → SelfRelation.
-- Sans axiome phénoménal supplémentaire.
-- Sans inspection séparée (LXXVI ne s'applique pas).
-- Sans observateur externe (LXIX ne s'applique pas).
-- L'acte s'atteste par son occurrence — pas par réflexion sur lui.
theorem minimal_perspective (c : Closure) (h : LIX c) : SelfRelation c :=
  { differential := c.valence,
    metabolized  := h.1,
    operative    := h.2,
    coextensive  := rfl }

-- §5. [∎] Toute Closure a une perspective minimale — sans hypothèse supplémentaire.
-- La perspective structurale est constitutive, non émergente contingente.
theorem all_closures_have_perspective (c : Closure) : SelfRelation c :=
  minimal_perspective c (LIX_holds c)

-- §5. [∎] PAS DE MODÈLE SÉPARANT.
-- Il est impossible de construire une Closure satisfaisant LIX mais pas SelfRelation.
-- LXXVII bloquait l'inspection réflexive — pas l'immanence de l'acte.
-- La voie cogito contourne LXXVII par la base.
theorem no_separating_model :
    ∀ (c : Closure), LIX c → SelfRelation c :=
  fun c h => minimal_perspective c h

-- §6. Témoin concret : clôture minimale — magnitude 1, valence positive.
def concreteClosure : Closure :=
  { occurring := true,
    valence   := { positive  := true,
                   magnitude := 1,
                   present   := by omega },
    operative := rfl }

-- §6. [∎] Le témoin concret a une perspective minimale.
theorem concrete_has_perspective : SelfRelation concreteClosure :=
  all_closures_have_perspective concreteClosure

-- §6. [∎] Le différentiel du témoin est sa propre valence.
theorem concrete_differential_is_valence :
    concrete_has_perspective.differential = concreteClosure.valence :=
  concrete_has_perspective.coextensive
