import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace PoincareConjecture.M76.OriginalTriangleCopies

def reversingCornerStep (pair : Fin 4 → Fin 4) (i j : Fin 4) : Prop :=
  j = pair i + 1

private theorem eqvGen_function_fixed {α : Type*} (f : α → α)
    (hf : Function.Injective f) {c : α} (hc : f c = c)
    {a b : α} (h : Relation.EqvGen (fun x y ↦ y = f x) a b) :
    a = c ↔ b = c := by
  induction h with
  | rel x y hxy =>
      rw [hxy]
      constructor
      · rintro rfl
        exact hc
      · intro h
        exact hf (h.trans hc.symm)
  | refl a => rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

theorem reversing_pairing_adjacent_corner_isolated (pair : Fin 4 → Fin 4)
    (hpair : Function.Involutive pair) (i : Fin 4) (hi : pair i = i + 1)
    {j : Fin 4} (h : Relation.EqvGen (reversingCornerStep pair) (i + 1) j) :
    j = i + 1 := by
  have hnext : pair (i + 1) = i := by rw [← hi, hpair]
  have hinj : Function.Injective (fun x ↦ pair x + (1 : Fin 4)) := by
    intro x y hxy
    exact hpair.injective (add_right_cancel hxy)
  exact (eqvGen_function_fixed (fun x ↦ pair x + (1 : Fin 4)) hinj
    (by rw [hnext]) h).mp rfl

theorem reversing_pairing_not_adjacent (pair : Fin 4 → Fin 4)
    (hpair : Function.Involutive pair)
    (hcorners : ∀ i j, Relation.EqvGen (reversingCornerStep pair) i j) :
    ∀ i, pair i ≠ i + 1 := by
  intro i hi
  have he := reversing_pairing_adjacent_corner_isolated pair hpair i hi
    (hcorners (i + 1) i)
  fin_cases i <;> norm_num at he

theorem reversing_one_vertex_pairing_opposite (pair : Fin 4 → Fin 4)
    (hpair : Function.Involutive pair) (hfixed : ∀ i, pair i ≠ i)
    (hcorners : ∀ i j, Relation.EqvGen (reversingCornerStep pair) i j) :
    ∀ i, pair i = i + 2 := by
  have hnext := reversing_pairing_not_adjacent pair hpair hcorners
  have hprev (i : Fin 4) : pair i ≠ i + 3 := by
    intro hi
    have hpi : pair (i + 3) = i := by rw [← hi, hpair]
    have hn := hnext (i + 3)
    rw [hpi] at hn
    apply hn
    rw [add_assoc, show (3 : Fin 4) + 1 = 0 from rfl, add_zero]
  intro i
  have h0 := hfixed i
  have h1 := hnext i
  have h3 := hprev i
  generalize he : pair i = j at h0 h1 h3 ⊢
  fin_cases i <;> fin_cases j <;>
    first | exact (h0 rfl).elim | exact (h1 rfl).elim | exact (h3 rfl).elim | rfl

theorem opposite_pairing_all_corners (pair : Fin 4 → Fin 4)
    (hpair : ∀ i, pair i = i + 2) :
    ∀ i j, Relation.EqvGen (reversingCornerStep pair) i j := by
  have h10 : Relation.EqvGen (reversingCornerStep pair) 1 0 :=
    Relation.EqvGen.rel _ _ (by simp [reversingCornerStep, hpair])
  have h21 : Relation.EqvGen (reversingCornerStep pair) 2 1 :=
    Relation.EqvGen.rel _ _ (by simp [reversingCornerStep, hpair])
  have h32 : Relation.EqvGen (reversingCornerStep pair) 3 2 :=
    Relation.EqvGen.rel _ _ (by simp [reversingCornerStep, hpair])
  have h0 (i : Fin 4) : Relation.EqvGen (reversingCornerStep pair) i 0 := by
    fin_cases i
    · exact Relation.EqvGen.refl _
    · exact h10
    · exact Relation.EqvGen.trans _ _ _ h21 h10
    · exact Relation.EqvGen.trans _ _ _ h32 (Relation.EqvGen.trans _ _ _ h21 h10)
  exact fun i j ↦ Relation.EqvGen.trans _ _ _ (h0 i) (Relation.EqvGen.symm _ _ (h0 j))

theorem reversing_pairing_one_vertex_iff (pair : Fin 4 → Fin 4)
    (hpair : Function.Involutive pair) (hfixed : ∀ i, pair i ≠ i) :
    (∀ i j, Relation.EqvGen (reversingCornerStep pair) i j) ↔
      ∀ i, pair i = i + 2 :=
  ⟨reversing_one_vertex_pairing_opposite pair hpair hfixed, opposite_pairing_all_corners pair⟩

end PoincareConjecture.M76.OriginalTriangleCopies
