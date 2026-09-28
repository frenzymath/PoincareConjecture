import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.ReducedGeometry.OrdinaryProductCapture
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Balls












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Set MeasureTheory

universe u

namespace PoincareConjecture

namespace M14StableSet

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} (G : GeneralizedLGeometryTransport n X time I)
  {T τ : ℝ} {x : G.Point}


noncomputable def empty_of_no_survivor
    (E : M14ExponentialFamily G T x) (hτ : 0 < τ)
    (q : (G.slices (T - τ)).Point)
    (hnone : ¬∃ Z : G.Horizontal x, (Z, Real.sqrt τ) ∈ E.domain) :
    M14StableSet G T τ x E where
  tau_pos := hτ
  carrier := ∅
  carrier_open := isOpen_empty
  survivor := fun _ h => h.elim
  endpoint_map := fun _ => q.val
  endpoint_map_eq := fun _ h => h.elim
  endpoint_time := fun _ h => h.elim
  endpoint_slice_map := fun _ => q
  endpoint_slice_map_val := fun _ h => h.elim
  endpoint_differential := fun _ h => h.elim
  endpoint_differential_eq := fun _ h => h.elim
  endpoint_differential_bijective := fun _ h => h.elim
  endpoint_continuous := continuousOn_empty _
  endpoint_slice_continuous := continuousOn_empty _
  endpoint_slice_smooth := by
    unfold M14EndpointSliceSmooth
    intro Z hZ
    exact hZ.elim
  local_inverse := fun _ h => h.elim
  endpoint_slice_differential := fun _ h _ => h.elim
  minimizing_path := fun _ h => h.elim
  nonconjugate := fun _ h => h.elim
  carrier_exact := by
    intro Z
    constructor
    · exact fun h => h.elim
    · rintro ⟨hZ, _⟩
      exact (hnone ⟨Z, hZ⟩).elim
  local_stable_neighborhood := fun _ h => h.elim

end M14StableSet

namespace OrdinaryProductRicciGeometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  {I : SpacetimeInterval} (F : RicciFlow n M I.domain)
  (P : OrdinaryProductRicciGeometry F.metric I)
  (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection)

theorem exists_survivor_of_capture
    (O : M14OrdinaryProviders.{u} n)
    (hCapture : M14OrdinaryCaptureStatement (P.toLGeometry h) O)
    {T τmax τ : ℝ} (hT : T ∈ I.domain) (hmax : 0 < τmax)
    (hI : Icc (T - τmax) T ⊆ I.domain)
    (hcurv : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {x : (P.toLGeometry h).Point}
    (E : M14ExponentialFamily (P.toLGeometry h) T x)
    (hτ : 0 < τ) (hτmax : τ < τmax) :
    ∃ Z : (P.toLGeometry h).Horizontal x, (Z, Real.sqrt τ) ∈ E.domain := by
  classical
  by_contra hnone
  have htime : T - τ ∈ I.domain := hI ⟨by linarith, by linarith⟩
  let q : (P.product.slices (T - τ)).Point :=
    P.product.sliceIdentification ⟨T - τ, htime⟩ (P.pointMap x)
  let H := M14StableSet.empty_of_no_survivor (P.toLGeometry h) E hτ q hnone
  obtain ⟨out, _⟩ := hCapture M I P.product.productCylinder P.product.productMetric
    F T τmax hT hmax hI hcurv (P.ordinaryCapture F h T τmax hT)
  have hx : x ∈ range P.product.productCylinder.toSpacetime := by
    rw [P.productCylinder_range]
    trivial
  have hnull := out.captured_stable_image_full_measure τ x E H hτmax hx
  have hnull' : calibratedMetricVolume (P.product.slices (T - τ)).metricOnPoints univ = 0 := by
    simpa only [H, M14StableSet.empty_of_no_survivor, image_empty,
      P.productCylinder_range, mem_univ, ofPred_true, sdiff_empty, toLGeometry] using hnull
  have hpositive := (P.product.slices (T - τ)).metricOnPoints.volumeMeasure_ball_pos
    q (show (0 : ℝ) < 1 by norm_num)
  rw [← calibratedMetricVolume_eq_volumeMeasure] at hpositive
  exact (ne_of_gt hpositive) (measure_mono_null (subset_univ _) hnull')


theorem exists_stable_of_capture
    (O : M14OrdinaryProviders.{u} n)
    (hCapture : M14OrdinaryCaptureStatement (P.toLGeometry h) O)
    (hExponential : M14ExponentialConclusion (P.toLGeometry h))
    {T τmax τ : ℝ} (hT : T ∈ I.domain) (hmax : 0 < τmax)
    (hI : Icc (T - τmax) T ⊆ I.domain)
    (hcurv : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {x : (P.toLGeometry h).Point}
    (E : M14ExponentialFamily (P.toLGeometry h) T x)
    (hτ : 0 < τ) (hτmax : τ < τmax) :
    Nonempty (M14StableSet (P.toLGeometry h) T τ x E) :=
  hExponential.stable T τ x E.base_time hτ E
    (P.exists_survivor_of_capture F h O hCapture hT hmax hI hcurv E hτ hτmax)

end OrdinaryProductRicciGeometry

end PoincareConjecture
