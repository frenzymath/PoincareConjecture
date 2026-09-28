import PoincareConjecture.Proofs.M14.OrdinaryCaptureRegularImage
import PoincareConjecture.Proofs.M14.OrdinaryCaptureVolume
import PoincareConjecture.Proofs.M10.RegularImage

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T3Space C] [ConnectedSpace C] [SecondCountableTopology C]
  [MeasurableSpace C] [BorelSpace C] {K : SpacetimeInterval}
  {e : CompatibleSpacetimeCylinder G.spacetime (G.timeIntervals.interval K) C}
  {g : SpacetimeCylinderMetric e} {F : RicciFlow n C K.domain} {τmax : ℝ}
  (t₀ : (G.timeIntervals.interval K).Point) (c₀ : C)
  (D : M14OrdinaryCaptureData G C K e g F t₀.val τmax)
  (hCoordinates : SpacetimeGaugeTheory.{u, u} G.leafwise G.timeIntervals)
  (hPath : M14PathCalculusConclusion G)

include D hCoordinates hPath

theorem ordinaryCapture_full_measure_at_cylinder
    (hL : LGeodesicTheory F t₀.val τmax)
    (hDifferential : ReducedLengthDifferentialTheory F t₀.val τmax)
    (hwindow : Icc (t₀.val - τmax) t₀.val ⊆ K.domain)
    (E : M14ExponentialFamily G t₀.val (e.toSpacetime (t₀, c₀)))
    {τ : ℝ} (H : M14StableSet G t₀.val τ (e.toSpacetime (t₀, c₀)) E)
    (hmax : τ < τmax) :
    calibratedMetricVolume (G.slices (t₀.val - τ)).metricOnPoints
      ({q | q.val ∈ range e.toSpacetime} \ (H.endpoint_slice_map '' H.carrier)) = 0 := by
  obtain ⟨A⟩ := hDifferential.exponential_geometry c₀
  have hvalid : t₀.val - τ ∈ K.domain :=
    hwindow ⟨sub_le_sub_left hmax.le t₀.val, sub_le_self t₀.val H.tau_pos.le⟩
  let t : (G.timeIntervals.interval K).Point := ⟨t₀.val - τ, hvalid⟩
  let S : Set (G.slices (t₀.val - τ)).Point :=
    {q | q.val ∈ range e.toSpacetime} \ (H.endpoint_slice_map '' H.carrier)
  have hS : MeasurableSet S :=
    (ordinaryCaptureSliceChart D hCoordinates t).open_target.measurableSet.diff
      (stableSliceChart H).open_target.measurableSet
  have hcaptured : (fun q => q.val) '' S ⊆ range e.toSpacetime := by
    rintro q ⟨r, hr, rfl⟩
    exact hr.1
  change calibratedMetricVolume (G.slices (t₀.val - τ)).metricOnPoints S = 0
  rw [ordinaryCapture_slice_measure D hCoordinates t hS hcaptured]
  apply measure_mono_null (t := {q | (q, τ) ∉ A.regularImage}) ?_
    (M10.regularImage_slice_complement_eq_zero hL hDifferential hwindow A H.tau_pos hmax)
  rintro c ⟨q, ⟨r, hr, rfl⟩, rfl⟩ hreg
  exact hr.2 (ordinaryCapture_regularImage_mem_stableImage t₀ c₀ D hCoordinates hPath
    E H A r hr.1 hreg)

end PoincareConjecture.M14
