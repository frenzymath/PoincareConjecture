import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.ConnectionSmooth
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Choice

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Set

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

theorem horizontalRicciCalculus_of_joint_regularity
    (hMetric : M12MetricPredecessors.{u} n) (D : LeafwiseLeviCivitaFamily F S)
    (hRiemann : IsSmoothHorizontalCovariantTensor F (k := 4)
      (fun p v => horizontalRiemann D p (v 0) (v 1) (v 2) (v 3)))
    (hRicci : IsSmoothHorizontalCovariantTensor F (k := 2)
      (fun p v => horizontalRicci D p (v 0) (v 1)))
    (hScalar : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ (horizontalScalarCurvature D))
    (hNormSq : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ (horizontalCurvatureNormSq D))
    (hLeaf : ∀ U : Set F.Point, IsOpen U →
      ∀ V : HorizontalSection F, IsSmoothHorizontalSectionOn F V U →
        ContMDiffOn (spacetimeModel n)
          ((spacetimeModel n).prod
            𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
          (fun p => TotalSpace.mk'
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
            p (rawLeafwiseCovariantDerivative D V p)) U) : HorizontalRicciCalculus D := by
  refine
    { lie_tensor := horizontalMetricLieDerivative_tensor
      lie_symmetric := horizontalMetricLieDerivative_symmetric
      lie_on_fields := ?_
      time_bracket_horizontal := ?_
      riemann_tensor := hRiemann
      ricci_tensor := hRicci
      ricci_symmetric := D.horizontalRicci_symmetric hMetric
      scalar_smooth := hScalar
      normSq_smooth := hNormSq
      norm_continuous := ?_
      slice_calculus := fun t => hMetric.curvature_calculus (S t).Point
        (S t).metricOnPoints (D.sliceConnection t)
      riemann_choice := D.horizontalRiemann_eq
      ricci_choice := D.horizontalRicci_eq
      scalar_choice := D.horizontalScalarCurvature_eq
      norm_choice := D.horizontalCurvatureNorm_eq
      normSq_choice := D.horizontalCurvatureNormSq_eq
      equation_choice := D.intrinsicGeneralizedRicciEquation_iff
      leafwise_smooth := hLeaf
      leafwise_apply_smooth := ?_
      leafwise_choice := ?_
      horizontal_choice := ?_
      horizontal_connection := ⟨spacetimeHorizontalConnection_of_leafwise_smooth D hLeaf⟩ }
  · intro U hU V W hV hW p hp
    exact horizontalMetricLieDerivative_on_fields hU hV hW hp
  · intro U hU V hV p hp
    exact horizontalTimeBracket_is_horizontal hU hV hp
  · have heq : horizontalCurvatureNorm D =
        fun p => Real.sqrt (horizontalCurvatureNormSq D p) := by
      funext p
      exact (Real.sqrt_sq (show 0 ≤ horizontalCurvatureNorm D p from
        Real.sqrt_nonneg _)).symm
    rw [heq]
    exact Real.continuous_sqrt.comp hNormSq.continuous
  · intro U hU V W hV hW
    exact (hLeaf U hU W hW).clm_bundle_apply hV
  · intro D' U hU V hV p hp
    exact D.rawLeafwiseCovariantDerivative_eq D'
      ((hV.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))
  · intro D' U hU V hV p hp
    exact D.rawHorizontalCovariantDerivative_eq D'
      ((hV.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))

theorem horizontalRicciCalculus_of_curvature_regularity
    (hMetric : M12MetricPredecessors.{u} n)
    (hCoordinates : M12MetricPredecessors.{0} n)
    (D : LeafwiseLeviCivitaFamily F S) {T : SpacetimeIntervalSystem}
    (cover : SpacetimeGaugeCover F T)
    (hRiemann : IsSmoothHorizontalCovariantTensor F (k := 4)
      (fun p v => horizontalRiemann D p (v 0) (v 1) (v 2) (v 3)))
    (hRicci : IsSmoothHorizontalCovariantTensor F (k := 2)
      (fun p v => horizontalRicci D p (v 0) (v 1)))
    (hScalar : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ (horizontalScalarCurvature D))
    (hNormSq : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ (horizontalCurvatureNormSq D)) :
    HorizontalRicciCalculus D :=
  horizontalRicciCalculus_of_joint_regularity hMetric D hRiemann hRicci hScalar hNormSq
    (fun _ hO _ hV => rawLeafwiseCovariantDerivative_smooth hCoordinates D cover hO hV)

end PoincareConjecture
