import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic











set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y



noncomputable def tangentHeightVector (n u : E) : E :=
  u - (⟪n, u⟫ / ⟪n, n⟫) • n


theorem tangentHeightVector_normal (n u : E) (hn : n ≠ 0) :
    ⟪n, tangentHeightVector n u⟫ = 0 := by
  rw [tangentHeightVector, inner_sub_right, inner_smul_right,
    div_mul_cancel₀ _ (inner_self_ne_zero.mpr hn), sub_self]



theorem tangentHeightVector_height (n u : E) (hn : n ≠ 0) :
    ⟪u, tangentHeightVector n u⟫ =
      ⟪tangentHeightVector n u, tangentHeightVector n u⟫ := by
  conv_rhs => lhs; unfold tangentHeightVector
  rw [inner_sub_left, real_inner_smul_left, tangentHeightVector_normal n u hn,
    mul_zero, sub_zero]



noncomputable def tangentHeightField (n u : E) : E :=
  (⟪tangentHeightVector n u, tangentHeightVector n u⟫)⁻¹ • tangentHeightVector n u


theorem tangentHeightField_normal (n u : E) (hn : n ≠ 0) :
    ⟪n, tangentHeightField n u⟫ = 0 := by
  rw [tangentHeightField, inner_smul_right, tangentHeightVector_normal n u hn, mul_zero]



theorem tangentHeightField_height (n u : E) (hn : n ≠ 0)
    (hw : tangentHeightVector n u ≠ 0) : ⟪u, tangentHeightField n u⟫ = 1 := by
  rw [tangentHeightField, inner_smul_right, tangentHeightVector_height n u hn,
    inv_mul_cancel₀ (inner_self_ne_zero.mpr hw)]



theorem tangentHeightVector_contDiffOn {U : Set E} (n : E → E)
    (hn : ContDiffOn ℝ ∞ n U) (hn0 : ∀ x ∈ U, n x ≠ 0) (u : E) :
    ContDiffOn ℝ ∞ (fun x => tangentHeightVector (n x) u) U := by
  exact contDiffOn_const.sub (((hn.inner ℝ contDiffOn_const).div (hn.inner ℝ hn)
    (fun x hx => inner_self_ne_zero.mpr (hn0 x hx))).smul hn)


theorem tangentHeightField_contDiffOn {U : Set E} (n : E → E)
    (hn : ContDiffOn ℝ ∞ n U) (hn0 : ∀ x ∈ U, n x ≠ 0) (u : E)
    (hw0 : ∀ x ∈ U, tangentHeightVector (n x) u ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => tangentHeightField (n x) u) U := by
  have hw := tangentHeightVector_contDiffOn n hn hn0 u
  exact ((hw.inner ℝ hw).inv (fun x hx => inner_self_ne_zero.mpr (hw0 x hx))).smul hw



theorem tangentHeightField_defining_derivative [CompleteSpace E]
    (ρ : E → ℝ) (x u : E) (hn : gradient ρ x ≠ 0) :
    fderiv ℝ ρ x (tangentHeightField (gradient ρ x) u) = 0 := by
  rw [← inner_gradient_left]
  exact tangentHeightField_normal _ _ hn



theorem contDiffOn_gradient_of_isOpen [CompleteSpace E] {U : Set E}
    (hU : IsOpen U) (ρ : E → ℝ) (hρ : ContDiffOn ℝ ∞ ρ U) :
    ContDiffOn ℝ ∞ (gradient ρ) U := by
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hρ.fderiv_of_isOpen hU (by simp))



theorem tangentHeightField_cutoff (n u : E) (hn : n ≠ 0)
    (hw : tangentHeightVector n u ≠ 0) (a : ℝ) :
    ⟪n, a • tangentHeightField n u⟫ = 0 ∧
      ⟪u, a • tangentHeightField n u⟫ = a := by
  simp only [inner_smul_right, tangentHeightField_normal n u hn,
    tangentHeightField_height n u hn hw, mul_zero, mul_one, and_self]

end PoincareConjecture.M25.Topology3D
