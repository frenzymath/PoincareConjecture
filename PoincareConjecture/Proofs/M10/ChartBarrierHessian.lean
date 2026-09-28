import PoincareConjecture.Proofs.M10.ChartHessianCorrection
import PoincareConjecture.Proofs.M10.BilinearDerivativeBound
import PoincareConjecture.Proofs.M10.GradientNorm










set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τ : ℝ}

noncomputable local instance chartBarrierBilinearNormedAddCommGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance chartBarrierBilinearNormedSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option backward.isDefEq.respectTransparency false in

theorem chart_spatial_fderiv_norm_le {f : M × ℝ → ℝ} (q₀ : M)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (extChartAt (𝓡 n) q₀).target)
    (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun q ↦ f (q, τ))
      ((extChartAt (𝓡 n) q₀).symm y))
    {S : ℝ} (hS : 0 ≤ S)
    (hB : ‖pullbackMetricForm (F.metric (T - τ)) (extChartAt (𝓡 n) q₀).symm y‖ ≤ S)
    (hgrad : reducedLengthGradientNormSq F T f τ ((extChartAt (𝓡 n) q₀).symm y) ≤ S) :
    ‖fderiv ℝ ((fun q ↦ f (q, τ)) ∘ (extChartAt (𝓡 n) q₀).symm) y‖ ≤ S := by
  let e := extChartAt (𝓡 n) q₀
  let B := pullbackMetricForm (F.metric (T - τ)) e.symm y
  have hq : e.symm y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source := by
    simpa only [e, extChartAt_source] using e.map_target hy
  apply ContinuousLinearMap.opNorm_le_bound _ hS
  intro v
  have hd := preferredField_scalar_derivative q₀ v hq hf
  rw [e.right_inv hy] at hd
  have hraw := abs_mvfderiv_le_of_gradientNormSq_le hgrad
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
      (E := TangentSpace (𝓡 n)) (x := q₀) v (e.symm y))
  rw [← hd] at hraw
  change |fderiv ℝ ((fun q ↦ f (q, τ)) ∘ e.symm) y v| ≤
    Real.sqrt S * Real.sqrt ((F.metric (T - τ)).inner (e.symm y)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
        (E := TangentSpace (𝓡 n)) (x := q₀) v (e.symm y))
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
        (E := TangentSpace (𝓡 n)) (x := q₀) v (e.symm y))) at hraw
  rw [← chartMetricForm_apply (F.metric (T - τ)) q₀ hy v v] at hraw
  have hval : B v v ≤ S * ‖v‖ ^ 2 := calc
    B v v ≤ |B v v| := le_abs_self _
    _ ≤ ‖B‖ * ‖v‖ * ‖v‖ := B.le_opNorm₂ v v
    _ ≤ S * ‖v‖ * ‖v‖ := by gcongr
    _ = S * ‖v‖ ^ 2 := by ring
  have hsqrt : Real.sqrt (B v v) ≤ Real.sqrt S * ‖v‖ := by
    simpa only [Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg v)] using
      Real.sqrt_le_sqrt hval
  change |fderiv ℝ ((fun q ↦ f (q, τ)) ∘ e.symm) y v| ≤ S * ‖v‖
  apply hraw.trans
  calc
    Real.sqrt S * Real.sqrt (B v v) ≤ Real.sqrt S * (Real.sqrt S * ‖v‖) :=
      mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg S)
    _ = S * ‖v‖ := by rw [← mul_assoc, Real.mul_self_sqrt hS]

set_option backward.isDefEq.respectTransparency false in

theorem chart_barrier_second_fderiv_le {f : M × ℝ → ℝ} (q₀ : M)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (extChartAt (𝓡 n) q₀).target)
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 (fun q ↦ f (q, τ))
      ((extChartAt (𝓡 n) q₀).symm y))
    {S : ℝ} (hS : 0 ≤ S)
    (hB : ‖pullbackMetricForm (F.metric (T - τ)) (extChartAt (𝓡 n) q₀).symm y‖ ≤ S)
    (hDB : ‖fderiv ℝ
      (pullbackMetricForm (F.metric (T - τ)) (extChartAt (𝓡 n) q₀).symm) y‖ ≤ S)
    (hI : ‖(pullbackMetricForm (F.metric (T - τ)) (extChartAt (𝓡 n) q₀).symm y).inverse‖ ≤ S)
    (hgrad : reducedLengthGradientNormSq F T f τ ((extChartAt (𝓡 n) q₀).symm y) ≤ S)
    (hH : ∀ v : TangentSpace (𝓡 n) ((extChartAt (𝓡 n) q₀).symm y),
      (F.connection (T - τ)).hessian (fun q ↦ f (q, τ))
        ((extChartAt (𝓡 n) q₀).symm y) v v ≤
          S * (F.metric (T - τ)).inner ((extChartAt (𝓡 n) q₀).symm y) v v)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ ((fun q ↦ f (q, τ)) ∘ (extChartAt (𝓡 n) q₀).symm)) y v v ≤
      (S ^ 2 + 2 * S ^ 3) * ‖v‖ ^ 2 := by
  rw [fixedChart_second_fderiv_eq (F.metric (T - τ)) (F.connection (T - τ)) q₀ hy hf v]
  exact metric_hessian_correction_le _ _ _ v hS hB hDB hI
    (chart_spatial_fderiv_norm_le q₀ hy (hf.mdifferentiableAt two_ne_zero) hS hB hgrad)
    (hH (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q₀).symm y v))

end PoincareConjecture.M10
