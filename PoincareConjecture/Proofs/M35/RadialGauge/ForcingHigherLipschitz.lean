import PoincareConjecture.Proofs.M35.RadialGauge.JetCalculus
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "D" => (V × ℝ) →L[ℝ] ℝ

noncomputable local instance m35ForcingHigherLipschitzLocal1 :
    NormedAddCommGroup D := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35ForcingHigherLipschitzLocal2 :
    NormedSpace ℝ D := ContinuousLinearMap.toNormedSpace
noncomputable local instance m35ForcingHigherLipschitzLocal3 :
    NormedAddCommGroup ((V × ℝ) →L[ℝ] D) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35ForcingHigherLipschitzLocal4 :
    NormedSpace ℝ ((V × ℝ) →L[ℝ] D) := ContinuousLinearMap.toNormedSpace

theorem forcing_higher_derivatives_lipschitz_of_third_bound
    {G : V → ℝ → ℝ} {eta M : ℝ}
    (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2))
    (hbound : ∀ x z, |z| ≤ eta →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun p : V × ℝ => G p.1 p.2))) (x, z)‖ ≤ M)
    (x : V) {a c : ℝ} (ha : |a| ≤ eta) (hc : |c| ≤ eta) :
    ‖fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2) (x, a) -
      fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2) (x, c)‖ ≤ M * |a - c| ∧
    ‖fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2) (x, a) -
      fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2) (x, c)‖ ≤ M * |a - c| := by
  let f := fun p : V × ℝ => G p.1 p.2
  let S : Set (V × ℝ) := univ ×ˢ Icc (-eta) eta
  have hS : Convex ℝ S := convex_univ.prod (convex_Icc (-eta) eta)
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hG).2
  have hdd := (contDiff_infty_iff_fderiv.mp hd).2
  have hfull : ‖fderiv ℝ (fderiv ℝ f) (x, a) - fderiv ℝ (fderiv ℝ f) (x, c)‖ ≤
      M * |a - c| := by
    have h := hS.norm_image_sub_le_of_norm_fderiv_le
      (fun p _ => hdd.differentiable (by simp) p)
      (fun p hp => hbound p.1 p.2 (abs_le.mpr hp.2))
      (show (x, c) ∈ S from ⟨mem_univ _, abs_le.mp hc⟩)
      (show (x, a) ∈ S from ⟨mem_univ _, abs_le.mp ha⟩)
    simpa only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
      Real.norm_eq_abs, max_eq_right (abs_nonneg (a - c))] using h
  let Lx : D →L[ℝ] (V →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ V (V × ℝ) ℝ).flip (ContinuousLinearMap.inl ℝ V ℝ)
  let Lz : D →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (0, (1 : ℝ))
  have hLx : ‖Lx‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖q.comp (ContinuousLinearMap.inl ℝ V ℝ)‖ ≤ 1 * ‖q‖
    calc
      _ ≤ ‖q‖ * ‖ContinuousLinearMap.inl ℝ V ℝ‖ := q.opNorm_comp_le _
      _ ≤ ‖q‖ * 1 := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_inl_le_one ℝ V ℝ) (norm_nonneg q)
      _ = _ := by ring
  have hLz : ‖Lz‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖q (0, 1)‖ ≤ 1 * ‖q‖
    simpa only [Prod.norm_def, norm_zero, norm_one, max_eq_right zero_le_one, mul_one, one_mul]
      using q.le_opNorm (0, 1)
  have hx (y : V × ℝ) : fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2) y =
      Lx.comp (fderiv ℝ (fderiv ℝ f) y) :=
    (Lx.hasFDerivAt.comp y (hd.differentiable (by simp) y).hasFDerivAt).fderiv
  have hz (y : V × ℝ) : fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2) y =
      Lz.comp (fderiv ℝ (fderiv ℝ f) y) :=
    (Lz.hasFDerivAt.comp y (hd.differentiable (by simp) y).hasFDerivAt).fderiv
  constructor
  · rw [hx, hx, ← ContinuousLinearMap.comp_sub]
    exact ((Lx.opNorm_comp_le _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hLx
        (norm_nonneg (fderiv ℝ (fderiv ℝ f) (x, a) - fderiv ℝ (fderiv ℝ f) (x, c))))).trans hfull
  · rw [hz, hz, ← ContinuousLinearMap.comp_sub]
    exact ((Lz.opNorm_comp_le _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hLz
        (norm_nonneg (fderiv ℝ (fderiv ℝ f) (x, a) - fderiv ℝ (fderiv ℝ f) (x, c))))).trans hfull

end PoincareConjecture.M35.RadialGauge
