import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.ReducedGeometry.OrdinaryProductLift








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.OrdinaryProductRicciGeometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  {I : SpacetimeInterval} (F : RicciFlow n M I.domain)
  (P : OrdinaryProductRicciGeometry F.metric I)


noncomputable def ordinaryCapture
    (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection)
    (T τmax : ℝ) (hT : T ∈ I.domain) :
    M14OrdinaryCaptureData (P.toLGeometry h) M I
      P.product.productCylinder P.product.productMetric F T τmax where
  metric_eq := by
    intro t _
    exact congrFun P.product.productMetric_eq.symm t
  point_map := P.pointMap
  point_map_on_cylinder := P.pointMap_productCylinder
  point_map_continuous := P.pointMap_continuous.continuousOn
  path_map := fun _ _ _ _ p _ => P.projectBackwardPath F h hT p
  path_start_eq := by
    intro τ₁ τ₂ x y p _
    change P.pointMap (p.curve τ₁) = P.pointMap x
    rw [p.curve_start]
  path_end_eq := by
    intro τ₁ τ₂ x y p _
    change P.pointMap (p.curve τ₂) = P.pointMap y
    rw [p.curve_end]
  path_curve_eq := fun _ _ _ _ _ _ _ _ => rfl
  path_capture_eq := by
    intro τ₁ τ₂ x y p _ s hs
    exact P.productCylinder_pointMap (p.curve s) (T - s)
      ((P.projectBackwardPath F h hT p).time_mem s hs) (p.curve_time s hs)
  path_lift := by
    intro τ₁ τ₂ q
    refine ⟨P.liftBackwardPath F q h, ?_⟩
    intro s hs
    change P.product.productCylinder.toSpacetime (⟨T - s, q.time_mem s hs⟩, q.curve s) =
      P.liftCurve F q s
    unfold liftCurve
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      exact ((P.product.timeIntervals.interval I).realParam_val (q.time_mem s hs)).symm
    · rfl
  capture_from_start := fun _ _ _ _ _ _ p s _ => P.path_captured h p s

@[simp] theorem ordinaryCapture_pointMap
    (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection)
    (T τmax : ℝ) (hT : T ∈ I.domain) :
    (P.ordinaryCapture F h T τmax hT).point_map = P.pointMap := rfl

end PoincareConjecture.OrdinaryProductRicciGeometry
