import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Charts
import Mathlib.Topology.Algebra.Module.FiniteDimension


















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M32

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates




noncomputable def evolvingCylinderAxialEquiv (tau : ℝ) (htau : tau < 1) : V ≃L[ℝ] V :=
  (ContinuousLinearEquiv.refl ℝ E2).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt (1 - tau))
      (Real.sqrt_pos.mpr (sub_pos.mpr htau)).ne').toContinuousLinearEquiv

private theorem evolvingCylinderAxialEquiv_apply (tau : ℝ) (htau : tau < 1) (p : V) :
    evolvingCylinderAxialEquiv tau htau p = (p.1, Real.sqrt (1 - tau) * p.2) := by
  rfl




theorem evolving_roundCylinderGram_diagonal (tau : ℝ) (q : UnitTwoSphere) (p : V) :
    roundCylinderGram tau (chartAt E2 q) p =
      Matrix.diagonal ![(1 - tau) * (32 / (‖p.1‖ ^ 2 + 4) ^ 2),
        (1 - tau) * (32 / (‖p.1‖ ^ 2 + 4) ^ 2), 1] := by
  ext i j
  rw [roundCylinderGram_eq_stereographic_formula]
  fin_cases i <;> fin_cases j <;>
    simp [roundCylinderCoordinateBasis, Matrix.diagonal,
      EuclideanSpace.basisFun, EuclideanSpace.inner_single_left] <;> ring

private noncomputable def evolvingSphereFactor (p : V) : ℝ :=
  32 / (‖p.1‖ ^ 2 + 4) ^ 2

private theorem evolvingSphereFactor_hasFDerivAt (p : V) :
    HasFDerivAt evolvingSphereFactor
      ((-128 / (‖p.1‖ ^ 2 + 4) ^ 3) •
        (innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ E2 ℝ)) p := by
  have hn := (hasStrictFDerivAt_norm_sq p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have hne : ‖p.1‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  have hi := (hasFDerivAt_inv (pow_ne_zero 2 hne)).comp p ((hn.add_const 4).pow 2)
  have hd := hi.const_smul (32 : ℝ)
  have hfun : evolvingSphereFactor =
      (32 : ℝ) • ((fun x : ℝ => x⁻¹) ∘ fun y : V => (‖y.1‖ ^ 2 + 4) ^ 2) := by
    funext y
    simp [evolvingSphereFactor, div_eq_mul_inv]
  rw [hfun]
  refine hd.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp [ContinuousLinearMap.comp_apply, smul_eq_mul]
  field_simp
  ring

private theorem evolving_roundCylinderGram_fderiv
    (tau : ℝ) (q : UnitTwoSphere) (p v : V) (i j : Fin 3) :
    fderiv ℝ (fun y => roundCylinderGram tau (chartAt E2 q) y i j) p v =
      (1 - tau) * ((-128 / (‖p.1‖ ^ 2 + 4) ^ 3) * inner ℝ p.1 v.1 *
        inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis j).1) := by
  have heq : (fun y => roundCylinderGram tau (chartAt E2 q) y i j) =
      fun y => (1 - tau) * (evolvingSphereFactor y *
        inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis j).1) +
        (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 := by
    funext y
    rw [roundCylinderGram_eq_stereographic_formula]
    dsimp [evolvingSphereFactor]
    ring
  have hd := (((evolvingSphereFactor_hasFDerivAt p).mul_const
    (inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis j).1)).const_mul
      (1 - tau)).add_const
        ((roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2)
  rw [heq]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun L : V →L[ℝ] ℝ => L v) hd.fderiv

private theorem evolving_roundCylinderGram_inv {tau : ℝ} (htau : tau < 1)
    (q : UnitTwoSphere) (p : V) :
    (roundCylinderGram tau (chartAt E2 q) p)⁻¹ =
      Matrix.diagonal ![((1 - tau) * (32 / (‖p.1‖ ^ 2 + 4) ^ 2))⁻¹,
        ((1 - tau) * (32 / (‖p.1‖ ^ 2 + 4) ^ 2))⁻¹, 1] := by
  have htime : 1 - tau ≠ 0 := (sub_pos.mpr htau).ne'
  have hden : ‖p.1‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  apply Matrix.inv_eq_left_inv
  rw [evolving_roundCylinderGram_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, htime, mul_assoc] <;> field_simp [hden]

set_option maxHeartbeats 800000 in




theorem evolving_roundCylinderChristoffel_eq_zero {tau : ℝ} (htau : tau < 1)
    (q : UnitTwoSphere) (p : V) (a b d : Fin 3) :
    roundCylinderChristoffel tau (chartAt E2 q) p a b d =
      roundCylinderChristoffel 0 (chartAt E2 q) p a b d := by
  have hne : ‖p.1‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  have htime : 1 - tau ≠ 0 := (sub_pos.mpr htau).ne'
  unfold roundCylinderChristoffel
  simp only [evolving_roundCylinderGram_inv htau,
    evolving_roundCylinderGram_inv (tau := 0) (by norm_num), evolving_roundCylinderGram_fderiv]
  fin_cases a <;> fin_cases b <;> fin_cases d <;>
    simp [Matrix.diagonal, roundCylinderCoordinateBasis, EuclideanSpace.basisFun,
      real_inner_comm] <;> field_simp [hne, htime]

private theorem evolving_diagonal_tensor_product {r : ℕ}
    (d : Fin 3 → ℝ) (a b : Fin r → Fin 3) :
    (∏ i, Matrix.diagonal d (a i) (b i)) = if a = b then ∏ i, d (a i) else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp [Matrix.diagonal]
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.diagonal, hi])




theorem evolving_roundCylinderTensorNormSquared_center {tau : ℝ} (htau : tau < 1)
    {r : ℕ} (q : UnitTwoSphere) (z : ℝ) (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared tau (chartAt E2 q) (0, z) T =
      ∑ a, (∏ i, (![(2 * (1 - tau))⁻¹, (2 * (1 - tau))⁻¹, 1] : Fin 3 → ℝ) (a i)) *
        (T a) ^ 2 := by
  classical
  have hcenter : (roundCylinderGram tau (chartAt E2 q) (0, z))⁻¹ =
      Matrix.diagonal ![(2 * (1 - tau))⁻¹, (2 * (1 - tau))⁻¹, 1] := by
    rw [evolving_roundCylinderGram_inv htau]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal, mul_comm]
  unfold roundCylinderTensorNormSquared
  rw [hcenter]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · rw [evolving_diagonal_tensor_product, if_pos rfl]
    ring
  · intro b _ hba
    rw [evolving_diagonal_tensor_product, if_neg (Ne.symm hba), zero_mul, zero_mul]
  · simp




theorem evolving_model_axialNormalization {tau : ℝ} (htau : tau ∈ Icc (-1) 0) :
    ‖(evolvingCylinderAxialEquiv tau (lt_of_le_of_lt htau.2 zero_lt_one) : V →L[ℝ] V)‖ ≤ 2 ∧
      (∀ i : Fin 3,
        evolvingCylinderAxialEquiv tau (lt_of_le_of_lt htau.2 zero_lt_one)
            (roundCylinderCoordinateBasis i) =
          (if i = 2 then Real.sqrt (1 - tau) else 1) • roundCylinderCoordinateBasis i) ∧
      ∀ (q : UnitTwoSphere) (z : ℝ) (p : V) (i j : Fin 3),
        ((1 - tau)⁻¹ * (if i = 2 then Real.sqrt (1 - tau) else 1) *
          (if j = 2 then Real.sqrt (1 - tau) else 1)) *
          roundCylinderGram tau (chartAt E2 q)
            ((0, z) + evolvingCylinderAxialEquiv tau
              (lt_of_le_of_lt htau.2 zero_lt_one) p) i j =
          roundCylinderGram 0 (chartAt E2 q) p i j := by
  have ha : 0 < 1 - tau := by linarith [htau.2]
  have hsqrt : Real.sqrt (1 - tau) ≤ 2 := by
    have hs := Real.sq_sqrt ha.le
    have hn := Real.sqrt_nonneg (1 - tau)
    nlinarith [htau.1]
  refine ⟨?_, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro p
    change ‖evolvingCylinderAxialEquiv tau (lt_of_le_of_lt htau.2 zero_lt_one) p‖ ≤ 2 * ‖p‖
    rw [evolvingCylinderAxialEquiv_apply]
    change max ‖p.1‖ ‖Real.sqrt (1 - tau) * p.2‖ ≤ 2 * max ‖p.1‖ ‖p.2‖
    apply max_le
    · have h := le_max_left ‖p.1‖ ‖p.2‖
      have hn : 0 ≤ max ‖p.1‖ ‖p.2‖ := (norm_nonneg _).trans h
      linarith
    · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))
  · intro i
    rw [evolvingCylinderAxialEquiv_apply]
    fin_cases i <;> simp [roundCylinderCoordinateBasis]
  · intro q z p i j
    rw [evolving_roundCylinderGram_diagonal, evolving_roundCylinderGram_diagonal,
      evolvingCylinderAxialEquiv_apply]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, ha.ne', mul_assoc]
    field_simp
    nlinarith [Real.sq_sqrt ha.le]

end PoincareConjecture.M32
