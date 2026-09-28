import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Identities
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.CompactSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Norm
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.TraceBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators
open Bundle

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}


theorem integral_laplacian_eq_zero_compact (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) :
    (∫ x, D.laplacian f x ∂g.volumeMeasure) = 0 := by
  simpa only [one_mul, D.inner_gradient, mvfderiv_const, zero_apply, integral_zero, neg_zero]
    using D.integral_mul_laplacian (u := fun _ => 1) contMDiff_const hf
      (HasCompactSupport.of_compactSpace _)


theorem integral_laplacian_sq_eq_hessian_add_scalar_gradient (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) :
    2 * (∫ x, (D.laplacian f x) ^ 2 ∂g.volumeMeasure) =
      2 * (∫ x, ∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2 ∂g.volumeMeasure) +
      ∫ x, D.scalarCurvature x * g.inner x (D.gradient f x) (D.gradient f x)
        ∂g.volumeMeasure := by
  have hn : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (D.gradient f x) (D.gradient f x)) := by
    intro x
    have hgrad := D.contMDiffAt_gradient (hf x)
    simpa using (contMDiffAt_totalSpace.mp
      (((g.contMDiff x).clm_bundle_apply hgrad).clm_bundle_apply hgrad)).2
  have hh := (D.contMDiff_hessian_normSq hf).continuous.integrable_of_hasCompactSupport
    (μ := g.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have hr : Integrable (fun x => D.scalarCurvature x *
      g.inner x (D.gradient f x) (D.gradient f x)) g.volumeMeasure :=
    (D.contMDiff_scalarCurvature.mul hn).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hd := D.integrable_inner_gradient (D.contMDiff_laplacian hf) hf
    (HasCompactSupport.of_compactSpace _)
  have hbochner (x : M) :
      D.laplacian (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x =
        2 * (∑ i, ∑ j, (D.hessian f x
          (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) +
        2 * g.inner x (D.gradient (D.laplacian f) x) (D.gradient f x) +
        D.scalarCurvature x * g.inner x (D.gradient f x) (D.gradient f x) := by
    rw [D.bochner_identity hf, D.ricci_eq_half_scalarCurvature_mul_inner,
      ← D.inner_gradient]
    ring
  have hb := D.integral_laplacian_eq_zero_compact hn
  simp_rw [hbochner] at hb
  have hadd : Integrable (fun x =>
      2 * (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) +
      2 * g.inner x (D.gradient (D.laplacian f) x) (D.gradient f x)) g.volumeMeasure :=
    (hh.const_mul 2).add (hd.const_mul 2)
  rw [integral_add hadd hr,
    integral_add (hh.const_mul 2) (hd.const_mul 2), integral_const_mul, integral_const_mul] at hb
  have hgreen := D.integral_mul_laplacian (D.contMDiff_laplacian hf) hf
    (HasCompactSupport.of_compactSpace _)
  simp only [← pow_two] at hgreen
  linarith


theorem integral_scalar_gradient_le_laplacian_sq (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) :
    (∫ x, D.scalarCurvature x * g.inner x (D.gradient f x) (D.gradient f x)
      ∂g.volumeMeasure) ≤ ∫ x, (D.laplacian f x) ^ 2 ∂g.volumeMeasure := by
  have hl := ((D.contMDiff_laplacian hf).pow 2).continuous.integrable_of_hasCompactSupport
    (μ := g.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have hh := (D.contMDiff_hessian_normSq hf).continuous.integrable_of_hasCompactSupport
    (μ := g.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have hpoint (x : M) := D.laplacian_sq_le_dim_mul_hessian_normSq f x
  norm_num only [Nat.cast_ofNat] at hpoint
  have hi := integral_mono hl (hh.const_mul 2) hpoint
  rw [integral_const_mul] at hi
  have heq := D.integral_laplacian_sq_eq_hessian_add_scalar_gradient hf
  linarith

end PoincareConjecture.LeviCivitaData
