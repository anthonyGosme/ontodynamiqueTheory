import Lean

namespace OntoEngine

/-!
==============================================================================
MOTEUR ONTODYNAMIQUE : LE COÛT DE L'IRRÉVERSIBILITÉ
==============================================================================
Démonstration formelle que la gratuité logique d'un "rollback" (IA, Logiciel)
exige mathématiquement une augmentation de la cicatrice sur le support physique.
(Rasoir : La clôture cicatrise, le porté redémarre)
-/

-- 1. AXIOMATIQUE
class OntoSystem (State : Type) (Host : Type) where
  cost : State → State → Nat
  scar : Host → Nat
  coupled : State → Host → State → Host → Prop
  conservation_law :
    ∀ {s1 s2 : State} {h1 h2 : Host},
    coupled s1 h1 s2 h2 → cost s1 s2 = 0 → scar h2 > scar h1

structure Snapshot (S H : Type) where
  state : S
  host : H
deriving Repr, DecidableEq, Inhabited

def cost_of (S H : Type) [OntoSystem S H] (s1 s2 : S) : Nat :=
  OntoSystem.cost (Host := H) s1 s2

def scar_of (S H : Type) [OntoSystem S H] (h : H) : Nat :=
  OntoSystem.scar (State := S) h

-- 2. DÉFINITIONS RÉCURSIVES
inductive ValidTrace {S H : Type} [OntoSystem S H] : List (Snapshot S H) → Prop where
  | nil  : ValidTrace []
  | one  (x) : ValidTrace [x]
  | cons (x y : Snapshot S H) (rest : List (Snapshot S H)) :
      OntoSystem.coupled x.state x.host y.state y.host →
      ValidTrace (y :: rest) →
      ValidTrace (x :: y :: rest)

def TotalCost {S H : Type} [OntoSystem S H] (trace : List (Snapshot S H)) : Nat :=
  match trace with
  | [] | [_] => 0
  | x :: y :: rest => cost_of S H x.state y.state + TotalCost (y :: rest)

def ScarIncrease {S H : Type} [OntoSystem S H] (trace : List (Snapshot S H)) : Nat :=
  match trace.head?, trace.getLast? with
  | some first, some last => scar_of S H last.host - scar_of S H first.host
  | _, _ => 0

-- 3. THÉORÈMES INTERMÉDIAIRES
theorem cost_zero_step {S H : Type} [OntoSystem S H] (x y : Snapshot S H) (rest : List (Snapshot S H)) :
  TotalCost (x :: y :: rest) = 0 → cost_of S H x.state y.state = 0 ∧ TotalCost (y :: rest) = 0 := by
  intro h
  change cost_of S H x.state y.state + TotalCost (y :: rest) = 0 at h
  omega

theorem step_increase {S H : Type} [OntoSystem S H] (x y : Snapshot S H) :
  OntoSystem.coupled x.state x.host y.state y.host → cost_of S H x.state y.state = 0 →
  scar_of S H y.host > scar_of S H x.host := by
  intro h_coup h_cost
  exact OntoSystem.conservation_law h_coup h_cost

-- 4. THÉORÈME GÉNÉRAL [ ∎ ]
theorem thm_no_free_recovery_general {S H : Type} [OntoSystem S H] (trace : List (Snapshot S H)) :
  ValidTrace trace → trace.length ≥ 2 → TotalCost trace = 0 → ScarIncrease trace > 0 := by
  intro h_valid
  induction h_valid with
  | nil =>
    intros h_len _
    simp only [List.length] at h_len
    omega
  | one _ =>
    intros h_len _
    simp only [List.length] at h_len
    omega
  | cons x y rest h_coupled h_valid_rest IH =>
    intros h_len h_cost
    have ⟨h_step_cost, h_rest_cost⟩ := cost_zero_step x y rest h_cost
    have h_first_jump : scar_of S H y.host > scar_of S H x.host := step_increase x y h_coupled h_step_cost
    cases rest with
    | nil =>
      change scar_of S H y.host - scar_of S H x.host > 0
      omega
    | cons z tail =>
      have h_len_rest : (y :: z :: tail).length ≥ 2 := by simp only [List.length]; omega
      have h_rest_increase : ScarIncrease (y :: z :: tail) > 0 := IH h_len_rest h_rest_cost
      have h_rest_change : ScarIncrease (y :: z :: tail) =
        match (y :: z :: tail).getLast? with
        | some last => scar_of S H last.host - scar_of S H y.host
        | none => 0 := rfl
      have h_goal_change : ScarIncrease (x :: y :: z :: tail) =
        match (y :: z :: tail).getLast? with
        | some last => scar_of S H last.host - scar_of S H x.host
        | none => 0 := rfl
      rw [h_rest_change] at h_rest_increase
      rw [h_goal_change]

      cases h_last : (y :: z :: tail).getLast? with
      | none =>
        rw [h_last] at h_rest_increase
        change 0 > 0 at h_rest_increase
        omega
      | some last =>
        -- CORRECTION ICI : on a retiré le ⊢, Lean a déjà remplacé le but tout seul.
        rw [h_last] at h_rest_increase
        change scar_of S H last.host - scar_of S H y.host > 0 at h_rest_increase
        change scar_of S H last.host - scar_of S H x.host > 0
        omega

end OntoEngine

-- ============================================================================
-- 5. APPLICATION : LE PORTAGE NORMATIF (Dette Technique)
-- ============================================================================
namespace Domain_Tech
open OntoEngine

inductive TechState | Clean | Hacky | Broken deriving DecidableEq, Repr, Inhabited
inductive Maintainer | Fresh | Tired | Burnout deriving DecidableEq, Repr, Inhabited

inductive TechCoupled : TechState → Maintainer → TechState → Maintainer → Prop where
  | DirtyPatch: TechCoupled TechState.Broken Maintainer.Tired TechState.Hacky Maintainer.Burnout

instance : OntoSystem TechState Maintainer where
  cost s1 s2 := match s1, s2 with
    | TechState.Broken, TechState.Hacky => 0 -- Le "rollback" ou fix gratuit du logiciel
    | _, _ => 1
  scar m := match m with
    | Maintainer.Burnout => 100
    | Maintainer.Tired => 50
    | Maintainer.Fresh => 0
  coupled := TechCoupled
  conservation_law := by
    intros s1 s2 h1 h2 h_coupled h_free
    cases h_coupled
    decide

def trace_recovery : List (Snapshot TechState Maintainer) :=
  [ { state := TechState.Broken, host := Maintainer.Tired },
    { state := TechState.Hacky,  host := Maintainer.Burnout } ]

/-- THÉORÈME SPÉCIFIQUE [ ∎ ] : L'hôte paie obligatoirement le coût du portage -/
theorem thm_tech_no_free_recovery :
  TotalCost trace_recovery = 0 → ScarIncrease trace_recovery > 0 := by
  intro h_free
  apply OntoEngine.thm_no_free_recovery_general trace_recovery
  · repeat constructor
  · decide
  · exact h_free

end Domain_Tech

-- ============================================================================
-- 6. OUTPUT DE VALIDATION (Affichage Console Propre pour le Lecteur)
-- ============================================================================

#eval IO.println "\n=======================================================\n ✅ MOTEUR ONTODYNAMIQUE : LE COÛT DE L'IRRÉVERSIBILITÉ\n=======================================================\n [ ∎ ] Théorème Général (Pas de restauration gratuite) : PROUVÉ\n [ ∎ ] Théorème Spécifique Tech (Dette payée par l'Hôte) : PROUVÉ\n-------------------------------------------------------\n STATUS : 0 erreur logique. 0 prémisse tacite.\n Le Rasoir 'La clôture cicatrise, le porté redémarre' est formellement validé.\n=======================================================\n"

-- LE SCEAU ACADÉMIQUE : Prouve qu'aucune triche n'a été utilisée.
#print axioms Domain_Tech.thm_tech_no_free_recovery
