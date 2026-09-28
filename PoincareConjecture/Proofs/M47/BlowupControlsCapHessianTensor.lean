import PoincareConjecture.Proofs.M47.BlowupControlsCapTensorNormAlgebra

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M47

local notation "Mat" => EuclideanSpace ℝ (Fin 3 × Fin 3)
local notation "Arr" => EuclideanSpace ℝ (Fin 4 → Fin 3)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private def fourPairEquiv : (Fin 4 → Fin 3) ≃ ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) where
  toFun a := ((a 0, a 1), (a 2, a 3))
  invFun p := ![p.1.1, p.1.2, p.2.1, p.2.2]
  left_inv a := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨i, j⟩, ⟨k, l⟩⟩; rfl

private noncomputable def tensorProductArray (K L : Mat) (sigma : Equiv.Perm (Fin 4)) : Arr :=
  WithLp.toLp 2 (fun a => K (a (sigma 0), a (sigma 1)) * L (a (sigma 2), a (sigma 3)))

private theorem tensorProductArray_norm (K L : Mat) (sigma : Equiv.Perm (Fin 4)) :
    ‖tensorProductArray K L sigma‖ = ‖K‖ * ‖L‖ := by
  let e := (Equiv.arrowCongr sigma.symm (Equiv.refl (Fin 3))).trans fourPairEquiv
  have h := cap_array_norm_reindex e (fun p : (Fin 3 × Fin 3) × (Fin 3 × Fin 3) =>
    K p.1 * L p.2)
  have hn := cap_array_product_norm (fun p => K p) (fun p => L p)
  exact h.trans hn

private theorem tensorProductArray_difference_le (K L : Mat) (sigma : Equiv.Perm (Fin 4)) :
    ‖tensorProductArray K K sigma - tensorProductArray L L sigma‖ ≤
      ‖K - L‖ * (‖K‖ + ‖L‖) := by
  have heq : tensorProductArray K K sigma - tensorProductArray L L sigma =
      tensorProductArray (K - L) K sigma + tensorProductArray L (K - L) sigma := by
    ext a
    simp only [tensorProductArray, PiLp.sub_apply, PiLp.add_apply]
    ring
  rw [heq]
  calc
    _ ≤ ‖tensorProductArray (K - L) K sigma‖ +
        ‖tensorProductArray L (K - L) sigma‖ := norm_add_le _ _
    _ = _ := by rw [tensorProductArray_norm, tensorProductArray_norm]; ring

private def scalarFirstPermutation : Equiv.Perm (Fin 4) where
  toFun i := ![0, 3, 1, 2] i
  invFun i := ![0, 2, 3, 1] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

noncomputable def capScalarHessianComponents (K : Mat) : Arr :=
  WithLp.toLp 2 (fun a =>
    (K (a 0, a 3) * K (a 1, a 2) + K (a 0, a 2) * K (a 1, a 3)) / 2 -
      K (a 0, a 1) * K (a 2, a 3))

theorem cap_scalarHessianComponents_difference_le (K L : Mat) :
    ‖capScalarHessianComponents K - capScalarHessianComponents L‖ ≤
      2 * ‖K - L‖ * (‖K‖ + ‖L‖) := by
  let D (sigma : Equiv.Perm (Fin 4)) :=
    tensorProductArray K K sigma - tensorProductArray L L sigma
  have heq : capScalarHessianComponents K - capScalarHessianComponents L =
      (1 / 2 : ℝ) • D scalarFirstPermutation +
        (1 / 2 : ℝ) • D (Equiv.swap 1 2) - D (Equiv.refl _) := by
    ext a
    simp only [capScalarHessianComponents, PiLp.sub_apply, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, D, tensorProductArray]
    norm_num [scalarFirstPermutation, Equiv.swap_apply_def, Matrix.cons_val_two,
      Matrix.cons_val_three, Fin.ext_iff]
    ring
  rw [heq]
  have h1 := tensorProductArray_difference_le K L scalarFirstPermutation
  have h2 := tensorProductArray_difference_le K L (Equiv.swap 1 2)
  have h3 := tensorProductArray_difference_le K L (Equiv.refl _)
  have hn := (norm_sub_le ((1 / 2 : ℝ) • D scalarFirstPermutation +
      (1 / 2 : ℝ) • D (Equiv.swap 1 2)) (D (Equiv.refl _))).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hn
  dsimp only [D] at hn
  linarith

set_option maxRecDepth 4096 in

theorem cap_scalarHessianComponents_identity_norm :
    ‖capScalarHessianComponents (capOperatorComponents (ContinuousLinearMap.id ℝ E₃))‖ = 3 := by
  let T := capScalarHessianComponents (capOperatorComponents (ContinuousLinearMap.id ℝ E₃))
  have hI (i j : Fin 3) :
      capOperatorComponents (ContinuousLinearMap.id ℝ E₃) (i, j) =
        if i = j then 1 else 0 := by
    simp [capOperatorComponents, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left]
  have hT (i j k l : Fin 3) : T ![i, j, k, l] =
      ((if i = l then 1 else 0) * (if j = k then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0)) / 2 -
      (if i = j then 1 else 0) * (if k = l then 1 else 0) := by
    simp only [T, capScalarHessianComponents, WithLp.ofLp_toLp,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, hI]
    rfl
  have hs : ‖T‖ ^ 2 = 9 := by
    change ‖(WithLp.toLp 2 (fun a => T a) : Arr)‖ ^ 2 = 9
    rw [cap_array_norm_sq]
    calc
      _ = ∑ p : (Fin 3 × Fin 3) × (Fin 3 × Fin 3),
          (T ![p.1.1, p.1.2, p.2.1, p.2.2]) ^ 2 := by
        symm
        exact fourPairEquiv.symm.sum_comp (fun a => T a ^ 2)
      _ = 9 := by
        simp only [Fintype.sum_prod_type, hT]
        have h02 : (0 : Fin 3) ≠ 2 := by decide
        have h12 : (1 : Fin 3) ≠ 2 := by decide
        have h21 : (2 : Fin 3) ≠ 1 := by decide
        norm_num [Fin.sum_univ_succ, h02, h12, h21]
  change ‖T‖ = 3
  nlinarith [norm_nonneg T]

theorem cap_scalarHessianComponents_norm_le (K : Mat) :
    ‖capScalarHessianComponents K‖ ≤ 3 +
      2 * ‖K - capOperatorComponents (ContinuousLinearMap.id ℝ E₃)‖ *
        (‖K‖ + Real.sqrt 3) := by
  have h := cap_scalarHessianComponents_difference_le K
    (capOperatorComponents (ContinuousLinearMap.id ℝ E₃))
  rw [cap_operatorComponents_identity_norm] at h
  have ht := norm_le_insert' (capScalarHessianComponents K)
    (capScalarHessianComponents (capOperatorComponents (ContinuousLinearMap.id ℝ E₃)))
  rw [cap_scalarHessianComponents_identity_norm] at ht
  linarith

end PoincareConjecture.M47
