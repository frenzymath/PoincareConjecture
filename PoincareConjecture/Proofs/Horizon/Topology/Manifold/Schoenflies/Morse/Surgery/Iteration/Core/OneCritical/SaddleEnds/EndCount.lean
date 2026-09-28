import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.ComponentCount
import Mathlib.Data.Finset.Card

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}

theorem card_endIndex_eq_sum (A : AnnularEndFamily v g B C) :
    Nat.card A.EndIndex = Nat.card A.LowerCutIndex + Nat.card A.UpperCutIndex :=
  Nat.card_sum

def endCapEquiv (A : AnnularEndFamily v g B C) : A.EndIndex ≃ {D // D ∈ A.caps} := by
  let f : A.EndIndex → {D // D ∈ A.caps} := Sum.elim Subtype.val Subtype.val
  apply Equiv.ofBijective f
  constructor
  · rintro (D | D) (E | E) heq
    · exact congrArg Sum.inl (Subtype.ext heq)
    · have hcenter := congrArg (fun D : {D // D ∈ A.caps} => D.1.center) heq
      have hD := D.2
      have hE := E.2
      have hcuts := A.cuts_lt
      dsimp [f] at hcenter
      exfalso
      linarith
    · have hcenter := congrArg (fun D : {D // D ∈ A.caps} => D.1.center) heq
      have hD := D.2
      have hE := E.2
      have hcuts := A.cuts_lt
      dsimp [f] at hcenter
      exfalso
      linarith
    · exact congrArg Sum.inr (Subtype.ext heq)
  · intro D
    rcases A.cap_side D D.property with hl | hu
    · exact ⟨Sum.inl ⟨D, hl⟩, rfl⟩
    · exact ⟨Sum.inr ⟨D, hu⟩, rfl⟩

theorem caps_nodup (A : AnnularEndFamily v g B C) : A.caps.Nodup := by
  apply A.caps_disjoint.imp
  intro D E hDE heq
  subst E
  have hzero : D.chart 0 ∈ D.chart '' closedBall (0 : E2) 1 :=
    mem_image_of_mem D.chart (by simp)
  exact disjoint_left.mp hDE hzero hzero

theorem card_endIndex_eq_caps_length (A : AnnularEndFamily v g B C) :
    Nat.card A.EndIndex = A.caps.length := by
  classical
  let E : {D // D ∈ A.caps} ≃ ↥A.caps.toFinset :=
    Equiv.subtypeEquivRight (fun _ => List.mem_toFinset.symm)
  calc
    Nat.card A.EndIndex = Nat.card {D // D ∈ A.caps} := Nat.card_congr A.endCapEquiv
    _ = Nat.card ↥A.caps.toFinset := Nat.card_congr E
    _ = A.caps.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = A.caps.length := List.toFinset_card_of_nodup A.caps_nodup

theorem card_endIndex_eq_three_of_cut_counts (A : AnnularEndFamily v g B C)
    (hcounts : (Nat.card A.LowerCutIndex = 1 ∧ Nat.card A.UpperCutIndex = 2) ∨
      (Nat.card A.LowerCutIndex = 2 ∧ Nat.card A.UpperCutIndex = 1)) :
    Nat.card A.EndIndex = 3 := by
  rw [A.card_endIndex_eq_sum]
  rcases hcounts with ⟨hl, hu⟩ | ⟨hl, hu⟩ <;> rw [hl, hu]

theorem caps_length_eq_three_of_cut_counts (A : AnnularEndFamily v g B C)
    (hcounts : (Nat.card A.LowerCutIndex = 1 ∧ Nat.card A.UpperCutIndex = 2) ∨
      (Nat.card A.LowerCutIndex = 2 ∧ Nat.card A.UpperCutIndex = 1)) :
    A.caps.length = 3 :=
  A.card_endIndex_eq_caps_length.symm.trans (A.card_endIndex_eq_three_of_cut_counts hcounts)

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily
