import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Derivatives
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap InnerProductSpace

namespace Poincare.Analysis.Sobolev.Weak

theorem HasWeakPartialDeriv.inner_toLp_schwartz {d : ℕ} [NeZero d]
    {i : Fin d} {u v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : HasWeakPartialDeriv i v u univ)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (φ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    ⟪hv.toLp v, φ.toLp 2 volume⟫_ℝ =
      -(∫ x, hu.toLp u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
  obtain ⟨R, hR, hKR⟩ :=
    (huc.isCompact.union hvc.isCompact).isBounded.subset_ball_lt 0
      (0 : EuclideanSpace ℝ (Fin d))
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    ⟨R, R + 1, hR, by linarith⟩
  let ψ : EuclideanSpace ℝ (Fin d) → ℝ := fun x => χ x * φ x
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := χ.contDiff.mul (φ.smooth ⊤)
  have he (x : EuclideanSpace ℝ (Fin d))
      (hx : x ∈ tsupport u ∪ tsupport v) : ψ =ᶠ[𝓝 x] φ := by
    filter_upwards [χ.eventuallyEq_one_of_mem_ball (hKR hx)] with y hy
    simp only [ψ, hy, Pi.one_apply, one_mul]
  have huψ : (fun x => u x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
      (fun x => u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    funext x
    by_cases hx : x ∈ tsupport u
    · rw [(he x (Or.inl hx)).fderiv_eq]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hvψ : (fun x => v x * ψ x) = (fun x => v x * φ x) := by
    funext x
    by_cases hx : x ∈ tsupport v
    · rw [(he x (Or.inr hx)).self_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hid := hw ψ hψ χ.hasCompactSupport.mul_right (subset_univ _)
  simp only [Measure.restrict_univ] at hid
  rw [huψ, hvψ] at hid
  calc
    _ = ∫ x, v x * φ x := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hv.coeFn_toLp, φ.coeFn_toLp 2 volume] with x hx hφx
      simp only [hx, hφx, Real.inner_apply]
    _ = -(∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
      linarith
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp] with x hx
      rw [hx]

end Poincare.Analysis.Sobolev.Weak
