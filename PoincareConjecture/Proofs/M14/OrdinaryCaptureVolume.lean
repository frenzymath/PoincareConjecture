import PoincareConjecture.Proofs.M14.OrdinaryCaptureSlice
import PoincareConjecture.Proofs.M14.OrdinaryCaptureVolumeChart
import PoincareConjecture.Proofs.M14.OrdinaryCaptureValues
import PoincareConjecture.Proofs.M14.Sec6_3_StableSliceChart

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
  {g : SpacetimeCylinderMetric e} {F : RicciFlow n C K.domain} {T τmax : ℝ}
  (D : M14OrdinaryCaptureData G C K e g F T τmax)
  (hCoordinates : SpacetimeGaugeTheory.{u, u} G.leafwise G.timeIntervals)

include hCoordinates

theorem ordinaryCapture_slice_preimage (t : (G.timeIntervals.interval K).Point)
    {A : Set (G.slices t.val).Point}
    (hcaptured : (fun q => q.val) '' A ⊆ range e.toSpacetime) :
    (ordinaryCaptureSliceChart D hCoordinates t) ⁻¹' A =
      D.point_map '' ((fun q => q.val) '' A) := by
  let f := ordinaryCaptureSliceChart D hCoordinates t
  ext c
  constructor
  · intro hc
    refine ⟨(f c).val, ⟨f c, hc, rfl⟩, ?_⟩
    exact D.point_map_on_cylinder t c
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    change f (f.symm r) ∈ A
    rw [f.right_inv (hcaptured ⟨r, hr, rfl⟩)]
    exact hr

theorem ordinaryCapture_slice_measure (t : (G.timeIntervals.interval K).Point)
    {A : Set (G.slices t.val).Point} (hA : MeasurableSet A)
    (hcaptured : (fun q => q.val) '' A ⊆ range e.toSpacetime) :
    calibratedMetricVolume (G.slices t.val).metricOnPoints A =
      calibratedMetricVolume (F.metric t.val) (D.point_map '' ((fun q => q.val) '' A)) := by
  let f := ordinaryCaptureSliceChart D hCoordinates t
  have hAtarget : A ⊆ f.target := fun q hq => hcaptured ⟨q, hq, rfl⟩
  have hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f := ordinaryCaptureSliceChart_smooth D hCoordinates t
  have hmap := ordinaryCaptureChart_measure_map (F.metric t.val)
    (G.slices t.val).metricOnPoints f rfl hf
    (ordinaryCaptureSliceChart_symm_smooth D hCoordinates t)
    (ordinaryCaptureSliceChart_metric D hCoordinates t)
  have h := congrArg (fun μ : Measure (G.slices t.val).Point => μ A) hmap
  rw [Measure.map_apply hf.continuous.measurable hA, Measure.restrict_apply hA,
    inter_eq_left.mpr hAtarget] at h
  rw [← h, ordinaryCapture_slice_preimage D hCoordinates t hcaptured]

theorem ordinaryCapture_stable_slice_measure
    (hwindow : Icc (T - τmax) T ⊆ K.domain)
    {τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
    (H : M14StableSet G T τ x E) (hmax : τ ≤ τmax)
    (hx : x ∈ range e.toSpacetime) :
    calibratedMetricVolume (G.slices (T - τ)).metricOnPoints
        (H.endpoint_slice_map '' H.carrier) =
      calibratedMetricVolume (F.metric (T - τ))
        (D.point_map '' ((fun q => q.val) '' (H.endpoint_slice_map '' H.carrier))) := by
  have ht : T - τ ∈ K.domain :=
    hwindow ⟨sub_le_sub_left hmax T, sub_le_self T H.tau_pos.le⟩
  exact ordinaryCapture_slice_measure D hCoordinates ⟨T - τ, ht⟩
    (stableSliceChart H).open_target.measurableSet
    (ordinaryCapture_endpoint_image D H hmax hx)

theorem ordinaryCapture_volume_transport
    (hwindow : Icc (T - τmax) T ⊆ K.domain)
    {τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
    (H : M14StableSet G T τ x E) (hmax : τ ≤ τmax)
    (hx : x ∈ range e.toSpacetime) :
    M14ReducedVolumeOnStable G T x τ H =
      reducedVolumeOn F T (D.point_map x) τ
        (D.point_map '' ((fun q => q.val) '' (H.endpoint_slice_map '' H.carrier))) := by
  have ht : T - τ ∈ K.domain :=
    hwindow ⟨sub_le_sub_left hmax T, sub_le_self T H.tau_pos.le⟩
  let t : (G.timeIntervals.interval K).Point := ⟨T - τ, ht⟩
  let f := ordinaryCaptureSliceChart D hCoordinates t
  let A := H.endpoint_slice_map '' H.carrier
  have hA : MeasurableSet A := (stableSliceChart H).open_target.measurableSet
  have hcaptured := ordinaryCapture_endpoint_image D H hmax hx
  have hAtarget : A ⊆ f.target := fun q hq => hcaptured ⟨q, hq, rfl⟩
  let φ : (G.slices (T - τ)).Point → ℝ := fun q =>
    Real.rpow τ (-(n : ℝ) / 2) * Real.exp (-M14ReducedLengthValue G T 0 τ x q.val)
  have htransport := ordinaryCaptureChart_integral (F.metric t.val)
    (G.slices t.val).metricOnPoints f rfl (ordinaryCaptureSliceChart_smooth D hCoordinates t)
    (ordinaryCaptureSliceChart_symm_smooth D hCoordinates t)
    (ordinaryCaptureSliceChart_metric D hCoordinates t) hA hAtarget φ
  change (∫ q in A, φ q ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints) = _
  rw [htransport]
  unfold reducedVolumeOn
  rw [← ordinaryCapture_slice_preimage D hCoordinates t hcaptured]
  apply setIntegral_congr_fun (hA.preimage
    (ordinaryCaptureSliceChart_smooth D hCoordinates t).continuous.measurable)
  intro c hc
  have hpoint : D.point_map (f c).val = c := D.point_map_on_cylinder t c
  have hlength := ordinaryCapture_reducedLength_transport D hCoordinates H.tau_pos hmax
    E.base_time (f c).property hx (hcaptured ⟨f c, hc, rfl⟩)
  change φ (f c) = reducedVolumeDensity F T (D.point_map x) τ c
  simp only [φ, reducedVolumeDensity, if_pos H.tau_pos, hlength, hpoint]

end PoincareConjecture.M14
