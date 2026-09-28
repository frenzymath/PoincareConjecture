import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic












set_option autoImplicit false
open scoped BigOperators

namespace PoincareConjecture.M76

private theorem sum_selected_complement {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid A]
    (f : ι → A) (a : ι) :
    ∑ i, f i = f a + ∑ i : {i : ι // i ≠ a}, f i := by
  classical
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
  rw [Finset.sum_subtype (p := fun i => i ≠ a) _ (by simp) f] at h
  simpa only [add_comm] using h.symm

private theorem sum_two_selected_complement {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid A] (f : ι → A) (a b : ι) (hab : a ≠ b) :
    ∑ i, f i = f a + f b + ∑ i : {i : ι // i ≠ a ∧ i ≠ b}, f i := by
  classical
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
  have h' := Finset.sum_erase_add (Finset.univ.erase a) f
    (show b ∈ Finset.univ.erase a by simp [hab.symm])
  rw [Finset.sum_subtype (p := fun i => i ≠ a ∧ i ≠ b) _
    (by simp [and_comm]) f] at h'
  rw [← h, ← h']
  ac_rfl



theorem residualComplexity_decreases_of_euler_change
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (oldResidual : ι → ℕ) (newResidual : κ → ℕ)
    (oldLabel : ι) (capLabel : Bool → κ)
    (same : {i : ι // i ≠ oldLabel} ≃
      {k : κ // k ≠ capLabel false ∧ k ≠ capLabel true})
    (hSame : ∀ i : {i : ι // i ≠ oldLabel}, oldResidual i = newResidual (same i))
    (hpositive : capLabel false ≠ capLabel true → ∀ b, 0 < newResidual (capLabel b))
    (hEuler : (∑ k, (2 - (newResidual k : ℤ))) =
      (∑ i, (2 - (oldResidual i : ℤ))) + 2) :
    (∑ k, (newResidual k - 1)) < ∑ i, (oldResidual i - 1) := by
  classical
  by_cases hcaps : capLabel false = capLabel true
  · let collapse : {k : κ // k ≠ capLabel false ∧ k ≠ capLabel true} ≃
        {k : κ // k ≠ capLabel false} :=
      Equiv.subtypeEquivRight (fun k => by rw [← hcaps]; exact and_self_iff)
    let single := same.trans collapse
    have hsingle (i : {i : ι // i ≠ oldLabel}) :
        oldResidual i = newResidual (single i) := hSame i
    have hrest := Fintype.sum_equiv single
      (fun i => 2 - (oldResidual i : ℤ))
      (fun k => 2 - (newResidual k : ℤ)) (fun i => by rw [hsingle i])
    rw [sum_selected_complement _ (capLabel false),
      sum_selected_complement _ oldLabel] at hEuler
    have hcount : oldResidual oldLabel = newResidual (capLabel false) + 2 := by omega
    have hcomplex := Fintype.sum_equiv single
      (fun i => oldResidual i - 1) (fun k => newResidual k - 1)
      (fun i => by rw [hsingle i])
    rw [sum_selected_complement _ (capLabel false),
      sum_selected_complement _ oldLabel]
    omega
  · have hrest := Fintype.sum_equiv same
      (fun i => 2 - (oldResidual i : ℤ))
      (fun k => 2 - (newResidual k : ℤ)) (fun i => by rw [hSame i])
    rw [sum_two_selected_complement _ (capLabel false) (capLabel true) hcaps,
      sum_selected_complement _ oldLabel] at hEuler
    have hcount : oldResidual oldLabel =
        newResidual (capLabel false) + newResidual (capLabel true) := by omega
    have hcomplex := Fintype.sum_equiv same
      (fun i => oldResidual i - 1) (fun k => newResidual k - 1)
      (fun i => by rw [hSame i])
    rw [sum_two_selected_complement _ (capLabel false) (capLabel true) hcaps,
      sum_selected_complement _ oldLabel]
    have hl := hpositive hcaps false
    have hr := hpositive hcaps true
    omega

end PoincareConjecture.M76
