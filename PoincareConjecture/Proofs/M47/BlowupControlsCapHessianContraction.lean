import PoincareConjecture.Proofs.M47.BlowupControlsCapHessianTensor

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M47

local notation "Idx" => Fin 4 → Fin 3
local notation "Mat" => Fin 3 → Fin 3 → ℝ

private theorem sum_permuted_hessian (A : Mat) (H : Idx → ℝ)
    (sigma : Equiv.Perm (Fin 4)) :
    (∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) * H (fun j => a (sigma j))) =
      ∑ a : Idx, A (a (sigma.symm 0)) (a (sigma.symm 1)) *
        A (a (sigma.symm 2)) (a (sigma.symm 3)) * H a := by
  let e : Idx ≃ Idx := Equiv.arrowCongr sigma.symm (Equiv.refl (Fin 3))
  apply Fintype.sum_equiv e
  intro a
  simp only [e, Equiv.arrowCongr_apply, Equiv.symm_symm, Function.comp_def, Equiv.refl_apply,
    Equiv.apply_symm_apply]
  rfl

private def hessianCycle : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 1).trans (Equiv.swap 1 2)

private def hessianPairs : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 2).trans (Equiv.swap 1 3)

theorem cap_hessian_scalar_contraction
    (A : Mat) (hA : ∀ i j, A i j = A j i) (H : Idx → ℝ)
    (hH : ∀ a : Idx, H (fun j => a ((Equiv.swap 2 3) j)) = H a) :
    (∑ a : Idx, (A (a 0) (a 1) * A (a 2) (a 3) / 2) *
      (H ![a 2, a 0, a 1, a 3] + H ![a 2, a 1, a 0, a 3] -
        H ![a 2, a 3, a 0, a 1] - H ![a 0, a 2, a 1, a 3] -
        H ![a 0, a 1, a 2, a 3] + H ![a 0, a 3, a 2, a 1])) =
      ∑ a : Idx, capScalarHessianComponents
        (WithLp.toLp 2 (fun p : Fin 3 × Fin 3 => A p.1 p.2)) a * H a := by
  let X := ∑ a : Idx, A (a 0) (a 3) * A (a 1) (a 2) * H a
  let Y := ∑ a : Idx, A (a 0) (a 2) * A (a 1) (a 3) * H a
  let Z := ∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) * H a
  have hXY : X = Y := by
    let e : Idx ≃ Idx := Equiv.arrowCongr (Equiv.swap 2 3) (Equiv.refl (Fin 3))
    apply Fintype.sum_equiv e
    intro a
    change A (a 0) (a 3) * A (a 1) (a 2) * H a =
      A (a 0) (a 3) * A (a 1) (a 2) * H (fun j => a ((Equiv.swap 2 3) j))
    rw [hH a]
  have h1 : (∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) *
      H ![a 2, a 0, a 1, a 3]) = X := by
    have h := sum_permuted_hessian A H hessianCycle
    convert h using 1
    · apply Finset.sum_congr rfl
      intro a _
      congr 1
      apply congrArg H
      funext j
      fin_cases j <;> rfl
    · dsimp only [X]
      apply Finset.sum_congr rfl
      intro a _
      change A (a 0) (a 3) * A (a 1) (a 2) * H a =
        A (a 1) (a 2) * A (a 0) (a 3) * H a
      ring
  have h2 : (∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) *
      H ![a 2, a 1, a 0, a 3]) = X := by
    have h := sum_permuted_hessian A H (Equiv.swap 0 2)
    convert h using 1
    · apply Finset.sum_congr rfl
      intro a _
      congr 1
      apply congrArg H
      funext j
      fin_cases j <;> rfl
    · dsimp only [X]
      apply Finset.sum_congr rfl
      intro a _
      change A (a 0) (a 3) * A (a 1) (a 2) * H a =
        A (a 2) (a 1) * A (a 0) (a 3) * H a
      rw [hA (a 2) (a 1)]
      ring
  have h3 : (∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) *
      H ![a 2, a 3, a 0, a 1]) = Z := by
    have h := sum_permuted_hessian A H hessianPairs
    convert h using 1
    · apply Finset.sum_congr rfl
      intro a _
      congr 1
      apply congrArg H
      funext j
      fin_cases j <;> rfl
    · dsimp only [Z]
      apply Finset.sum_congr rfl
      intro a _
      change A (a 0) (a 1) * A (a 2) (a 3) * H a =
        A (a 2) (a 3) * A (a 0) (a 1) * H a
      ring
  have h4 : (∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) *
      H ![a 0, a 2, a 1, a 3]) = Y := by
    have h := sum_permuted_hessian A H (Equiv.swap 1 2)
    convert h using 1
    · apply Finset.sum_congr rfl
      intro a _
      congr 1
      apply congrArg H
      funext j
      fin_cases j <;> rfl
    · dsimp only [Y]
      apply Finset.sum_congr rfl
      intro a _
      rfl
  have h5 : (∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) *
      H ![a 0, a 1, a 2, a 3]) = Z := by
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    congr 1
    funext j
    fin_cases j <;> rfl
  have h6 : (∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) *
      H ![a 0, a 3, a 2, a 1]) = X := by
    have h := sum_permuted_hessian A H (Equiv.swap 1 3)
    convert h using 1
    · apply Finset.sum_congr rfl
      intro a _
      congr 1
      apply congrArg H
      funext j
      fin_cases j <;> rfl
    · dsimp only [X]
      apply Finset.sum_congr rfl
      intro a _
      change A (a 0) (a 3) * A (a 1) (a 2) * H a =
        A (a 0) (a 3) * A (a 2) (a 1) * H a
      rw [hA (a 2) (a 1)]
  have hleft : (∑ a : Idx, (A (a 0) (a 1) * A (a 2) (a 3) / 2) *
      (H ![a 2, a 0, a 1, a 3] + H ![a 2, a 1, a 0, a 3] -
        H ![a 2, a 3, a 0, a 1] - H ![a 0, a 2, a 1, a 3] -
        H ![a 0, a 1, a 2, a 3] + H ![a 0, a 3, a 2, a 1])) =
      (X + X - Z - Y - Z + X) / 2 := by
    calc
      _ = (1 / 2 : ℝ) *
          ((∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) * H ![a 2, a 0, a 1, a 3]) +
          (∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) * H ![a 2, a 1, a 0, a 3]) -
          (∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) * H ![a 2, a 3, a 0, a 1]) -
          (∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) * H ![a 0, a 2, a 1, a 3]) -
          (∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) * H ![a 0, a 1, a 2, a 3]) +
          (∑ a : Idx, A (a 0) (a 1) * A (a 2) (a 3) * H ![a 0, a 3, a 2, a 1])) := by
        simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [h1, h2, h3, h4, h5, h6]; ring
  have hright : (∑ a : Idx, capScalarHessianComponents
      (WithLp.toLp 2 (fun p : Fin 3 × Fin 3 => A p.1 p.2)) a * H a) =
      (X + Y) / 2 - Z := by
    have heq : (X + Y) / 2 - Z = (1 / 2 : ℝ) * X + (1 / 2 : ℝ) * Y - Z := by ring
    rw [heq]
    dsimp only [X, Y, Z, capScalarHessianComponents]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hleft, hright, hXY]
  ring

end PoincareConjecture.M47
