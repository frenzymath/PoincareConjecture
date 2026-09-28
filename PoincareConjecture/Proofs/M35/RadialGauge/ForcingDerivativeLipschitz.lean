import PoincareConjecture.Proofs.M35.RadialGauge.SourceDerivativeDifference
import Mathlib.Analysis.Calculus.MeanValue










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)



theorem forcing_derivatives_lipschitz_of_second_bound
    {G : V → ℝ → ℝ} {eta M : ℝ}
    (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2))
    (hbound : ∀ x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ 2 (fun p : V × ℝ => G p.1 p.2) (x, z)‖ ≤ M)
    (x : V) {a c : ℝ} (ha : |a| ≤ eta) (hc : |c| ≤ eta) :
    ‖forcingSpaceDeriv G x a - forcingSpaceDeriv G x c‖ ≤ M * |a - c| ∧
      |forcingScalarDeriv G x a - forcingScalarDeriv G x c| ≤ M * |a - c| := by
  let S : Set (V × ℝ) := univ ×ˢ Icc (-eta) eta
  have hS : Convex ℝ S := convex_univ.prod (convex_Icc (-eta) eta)
  have hd := (contDiff_infty_iff_fderiv.mp hG).2
  have hfull : ‖fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, a) -
      fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, c)‖ ≤ M * |a - c| := by
    have h := hS.norm_image_sub_le_of_norm_fderiv_le
      (fun p _ => hd.differentiable (by simp) p)
      (fun p hp => by
        have hz : |p.2| ≤ eta := abs_le.mpr hp.2
        simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
          using hbound p.1 p.2 hz)
      (show (x, c) ∈ S from ⟨mem_univ _, abs_le.mp hc⟩)
      (show (x, a) ∈ S from ⟨mem_univ _, abs_le.mp ha⟩)
    simpa only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
      Real.norm_eq_abs, max_eq_right (abs_nonneg (a - c))] using h
  let q := fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, a) -
    fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, c)
  have hspace : ‖q.comp (ContinuousLinearMap.inl ℝ V ℝ)‖ ≤ ‖q‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      Prod.norm_def, norm_zero, max_eq_left (norm_nonneg v)] using q.le_opNorm (v, 0)
  have hscalar : ‖q (0, 1)‖ ≤ ‖q‖ := by
    simpa only [Prod.norm_def, norm_zero, norm_one, max_eq_right zero_le_one,
      mul_one] using q.le_opNorm (0, 1)
  constructor
  · simpa only [forcingSpaceDeriv, q, ContinuousLinearMap.sub_comp] using hspace.trans hfull
  · simpa only [forcingScalarDeriv, q, sub_apply, Real.norm_eq_abs]
      using hscalar.trans hfull

end PoincareConjecture.M35.RadialGauge
