import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Variation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Functional
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Bochner
import Mathlib.Analysis.Calculus.MeanValue



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.RicciFlow

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [CompactSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {J : Set ℝ}

omit [PreconnectedSpace M] in
theorem hasDerivAt_volume_surface (F : RicciFlow 2 M J)
    {t : ℝ} (ht : t ∈ interior J) :
    HasDerivAt (fun s => (F.metric s).volumeMeasure.real univ)
      (-(∫ x, (F.connection t).scalarCurvature x ∂(F.metric t).volumeMeasure)) t := by
  have h := F.hasDerivAt_integral_volumeMeasure_surface_of_hasDerivAt
    (u := fun _ _ => (1 : ℝ)) (v := fun _ => 0) ht
    (fun _ _ _ => contMDiffAt_const) (fun _ => hasDerivAt_const t 1)
  simpa only [integral_const, smul_eq_mul, mul_one, zero_sub, integral_neg] using h

theorem hasDerivAt_totalScalar_surface (F : RicciFlow 2 M J)
    {t : ℝ} (ht : t ∈ interior J) :
    HasDerivAt (fun s => ∫ x, (F.connection s).scalarCurvature x
      ∂(F.metric s).volumeMeasure) 0 t := by
  have h := F.hasDerivAt_integral_volumeMeasure_surface_of_hasDerivAt ht
    (fun s hs x => F.contMDiffAt_scalarCurvature_surface hs x)
    (F.hasDerivAt_scalarCurvature_surface ht)
  have heq : (∫ x, (F.connection t).laplacian (F.connection t).scalarCurvature x +
      ((F.connection t).scalarCurvature x) ^ 2 -
      (F.connection t).scalarCurvature x * (F.connection t).scalarCurvature x
      ∂(F.metric t).volumeMeasure) = 0 := by
    simp only [pow_two, add_sub_cancel_right]
    exact (F.connection t).integral_laplacian_eq_zero_compact
      (F.connection t).contMDiff_scalarCurvature
  exact heq ▸ h

theorem totalScalar_surface_eq (F : RicciFlow 2 M J) (hJ : Convex ℝ J)
    {s t : ℝ} (hs : s ∈ interior J) (ht : t ∈ interior J) :
    (∫ x, (F.connection s).scalarCurvature x ∂(F.metric s).volumeMeasure) =
      ∫ x, (F.connection t).scalarCurvature x ∂(F.metric t).volumeMeasure := by
  apply isOpen_interior.is_const_of_deriv_eq_zero hJ.interior.isPreconnected
    (fun r hr => (F.hasDerivAt_totalScalar_surface hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (F.hasDerivAt_totalScalar_surface hr).deriv) hs ht

theorem hasDerivAt_meanScalar_surface [Nonempty M] (F : RicciFlow 2 M J)
    {t : ℝ} (ht : t ∈ interior J) :
    HasDerivAt (fun s => SurfaceEntropy.meanScalar (F.connection s))
      (SurfaceEntropy.meanScalar (F.connection t) ^ 2) t := by
  have h := (F.hasDerivAt_totalScalar_surface ht).div
    (F.hasDerivAt_volume_surface ht)
    (SurfaceEntropy.volume_pos (g := F.metric t)).ne'
  convert h using 1 <;> first | rfl | simp only
    [zero_mul, zero_sub, mul_neg, neg_neg, SurfaceEntropy.meanScalar, div_pow, ← pow_two]

end PoincareConjecture.RicciFlow
