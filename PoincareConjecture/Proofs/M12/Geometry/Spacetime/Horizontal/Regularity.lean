import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Assembly
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Regularity.Trace
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Regularity.Norm
import PoincareConjecture.Definitions.M12GaugeCover
import PoincareConjecture.Proofs.M12.Analysis.Calculus.SpatialFDerivWithin
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients

















set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

section CoordinateCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]



theorem contDiffOn_spatialCoordinateChristoffel
    {J : Set ℝ} {U : Set E} (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U)
    {B : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ ∞ B (J ×ˢ U))
    (hInv : ∀ p ∈ J ×ˢ U, (B p).IsInvertible) (u v : E) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => coordinateChristoffel (fun x => B (p.1, x)) p.2 u v)
      (J ×ˢ U) := by
  have hD : ContDiffOn ℝ ∞
      (fun p : ℝ × E => fderiv ℝ (fun x => B (p.1, x)) p.2)
      (J ×ˢ U) :=
    SpacetimeBounds.contDiffOn_spatialFDeriv_within hB hJ hU
  intro p hp
  have hBp : ContDiffWithinAt ℝ ∞ B (J ×ˢ U) p := hB p hp
  have hIp : ContDiffWithinAt ℝ ∞ (fun q => (B q).inverse) (J ×ˢ U) p :=
    (hInv p hp).contDiffAt_map_inverse.comp_contDiffWithinAt p hBp
  have hDp := hD p hp
  have hDu : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => (fderiv ℝ (fun x => B (q.1, x)) q.2) u)
      (J ×ˢ U) p :=
    hDp.clm_apply (contDiffWithinAt_const (c := u))
  have hDuv : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => (fderiv ℝ (fun x => B (q.1, x)) q.2) u v)
      (J ×ˢ U) p :=
    hDu.clm_apply (contDiffWithinAt_const (c := v))
  have hDv : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => (fderiv ℝ (fun x => B (q.1, x)) q.2) v)
      (J ×ˢ U) p :=
    hDp.clm_apply (contDiffWithinAt_const (c := v))
  have hflip : ContDiff ℝ ∞
      (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  have hflip' : ContDiff ℝ ∞
      (fun L : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).contDiff
  have hflipDv : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => ((fderiv ℝ (fun x => B (q.1, x)) q.2) v).flip)
      (J ×ˢ U) p :=
    hflip.contDiffAt.comp_contDiffWithinAt p hDv
  have hflipDv_u : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => ((fderiv ℝ (fun x => B (q.1, x)) q.2) v).flip u)
      (J ×ˢ U) p :=
    hflipDv.clm_apply (contDiffWithinAt_const (c := u))
  have hflipD : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => (fderiv ℝ (fun x => B (q.1, x)) q.2).flip)
      (J ×ˢ U) p :=
    hflip'.contDiffAt.comp_contDiffWithinAt p hDp
  have hflipDu : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => ((fderiv ℝ (fun x => B (q.1, x)) q.2).flip u))
      (J ×ˢ U) p :=
    hflipD.clm_apply (contDiffWithinAt_const (c := u))
  have hflipDu_flip : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => ((fderiv ℝ (fun x => B (q.1, x)) q.2).flip u).flip)
      (J ×ˢ U) p :=
    hflip.contDiffAt.comp_contDiffWithinAt p hflipDu
  have hflipDu_v : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => ((fderiv ℝ (fun x => B (q.1, x)) q.2).flip u).flip v)
      (J ×ˢ U) p :=
    hflipDu_flip.clm_apply (contDiffWithinAt_const (c := v))
  have hK : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => metricKoszulCovector
        (fderiv ℝ (fun x => B (q.1, x)) q.2) u v)
      (J ×ˢ U) p := by
    unfold metricKoszulCovector
    exact ((hDuv.add hflipDv_u).sub hflipDu_v).const_smul _
  have hInvApply : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => (B q).inverse
        (metricKoszulCovector (fderiv ℝ (fun x => B (q.1, x)) q.2) u v))
      (J ×ˢ U) p :=
    hIp.clm_apply hK
  simpa only [coordinateChristoffel] using hInvApply

variable [FiniteDimensional ℝ E]



theorem contDiffOn_spatialCoordinateChristoffel_bilinear
    {J : Set ℝ} {U : Set E} (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U)
    {B : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ ∞ B (J ×ˢ U))
    (hInv : ∀ p ∈ J ×ˢ U, (B p).IsInvertible) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E =>
        PoincareConjecture.CoordinateExponential.christoffelBilinear
          (fun x => B (p.1, x)) p.2)
      (J ×ˢ U) := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  simpa only [PoincareConjecture.CoordinateExponential.christoffelBilinear_apply] using
    contDiffOn_spatialCoordinateChristoffel hJ hU hB hInv u v

end CoordinateCoefficients







theorem horizontalRicciCalculus_of_adapted_cover
    (hMetric : M12MetricPredecessors.{u} n)
    (hCoordinates : M12MetricPredecessors.{0} n)
    (D : LeafwiseLeviCivitaFamily F S)
    (T : SpacetimeIntervalSystem)
    (cover : SpacetimeGaugeCover F T) :
    HorizontalRicciCalculus D := by
  have hR := horizontalRiemann_tensor hMetric hCoordinates D cover
  have hRic := horizontalRicci_tensor_of_riemann D hR
  exact horizontalRicciCalculus_of_curvature_regularity hMetric hCoordinates D cover
    hR hRic (horizontalScalarCurvature_smooth_of_ricci D hRic)
    (horizontalCurvatureNormSq_smooth_of_riemann D hR)

end PoincareConjecture
