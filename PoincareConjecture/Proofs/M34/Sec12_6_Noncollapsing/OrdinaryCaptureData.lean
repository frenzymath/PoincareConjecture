import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryLiftedPath

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  {I : SpacetimeInterval} {F : RicciFlow n M I.domain}

noncomputable def ordinaryProductCaptureData
    (R : OrdinaryProductRicciGeometry F.metric I)
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
    {T : ℝ} (hT : T ∈ I.domain) (taumax : ℝ) :
    M14OrdinaryCaptureData (ordinaryProductLGeometry R hRicci) M I
      R.product.productCylinder R.product.productMetric F T taumax where
  metric_eq := by rw [R.product.productMetric_eq]; exact fun _ _ => rfl
  point_map := ordinaryProductProjection R.product
  point_map_on_cylinder := ordinaryProductProjection_cylinder R.product
  point_map_continuous := (ordinaryProductProjection_contMDiff R.product).continuous.continuousOn
  path_map := fun _ _ _ _ p _ => ordinaryProjectedPath R hRicci hT p
  path_start_eq := fun _ _ _ _ p _ => congrArg (ordinaryProductProjection R.product) p.curve_start
  path_end_eq := fun _ _ _ _ p _ => congrArg (ordinaryProductProjection R.product) p.curve_end
  path_curve_eq := fun _ _ _ _ _ _ _ _ => rfl
  path_capture_eq := by
    intro a b x y p _ s hs
    rw [R.product.productCylinder_eq]
    apply Prod.ext
    · exact Subtype.ext (p.curve_time s hs).symm
    · exact ordinaryProductProjection_eq R.product (p.curve s)
  path_lift := by
    intro a b q
    refine ⟨ordinaryLiftedPath R hRicci q, ?_⟩
    intro s hs
    apply congrArg R.product.productCylinder.toSpacetime
    apply Prod.ext
    · exact Subtype.ext ((R.product.timeIntervals.interval I).realParam_val
        (q.time_mem s hs)).symm
    · rfl
  capture_from_start := by
    intro a b x y _ _ p s _
    rw [ordinaryProductCylinder_range]
    exact mem_univ (p.curve s)

end PoincareConjecture.M34
