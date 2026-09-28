import PoincareConjecture.Proofs.M14.OrdinaryCaptureAction

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

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

include D in

theorem ordinaryCapture_slice_range (t : (G.timeIntervals.interval K).Point) :
    range (movingGaugeSliceMap e.toMovingSpacetimeGauge G.slices t) =
      {q : (G.slices t.val).Point | q.val ∈ range e.toSpacetime} := by
  ext q
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨(t, c), rfl⟩
  · intro hq
    refine ⟨D.point_map q.val, Subtype.ext ?_⟩
    exact ordinaryCapture_point_reconstruct D hq t q.property

def ordinaryCaptureSliceChart (t : (G.timeIntervals.interval K).Point) :
    OpenPartialHomeomorph C (G.slices t.val).Point where
  toFun := movingGaugeSliceMap e.toMovingSpacetimeGauge G.slices t
  invFun := fun q => D.point_map q.val
  source := univ
  target := {q | q.val ∈ range e.toSpacetime}
  map_source' := fun c _ => ⟨(t, c), rfl⟩
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun c _ => D.point_map_on_cylinder t c
  right_inv' := fun q hq => Subtype.ext (ordinaryCapture_point_reconstruct D hq t q.property)
  open_source := isOpen_univ
  open_target := by
    rw [← ordinaryCapture_slice_range D t]
    exact ((ordinaryCapture_movingCalculus D hCoordinates).slice_localDiffeomorph t).isOpen_range
  continuousOn_toFun :=
    ((ordinaryCapture_movingCalculus D hCoordinates).slice_localDiffeomorph t).contMDiff.continuous
      |>.continuousOn
  continuousOn_invFun :=
    D.point_map_continuous.comp continuous_subtype_val.continuousOn (fun _ hq => hq)

theorem ordinaryCaptureSliceChart_source (t : (G.timeIntervals.interval K).Point) :
    (ordinaryCaptureSliceChart D hCoordinates t).source = univ := rfl

theorem ordinaryCaptureSliceChart_smooth (t : (G.timeIntervals.interval K).Point) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (ordinaryCaptureSliceChart D hCoordinates t) :=
  ((ordinaryCapture_movingCalculus D hCoordinates).slice_localDiffeomorph t).contMDiff

theorem ordinaryCaptureSliceChart_symm_smooth (t : (G.timeIntervals.interval K).Point) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (ordinaryCaptureSliceChart D hCoordinates t).symm
      (ordinaryCaptureSliceChart D hCoordinates t).target := by
  let f := ordinaryCaptureSliceChart D hCoordinates t
  intro q hq
  let c := f.symm q
  have hf : f c = q := f.right_inv hq
  have hl := (ordinaryCapture_movingCalculus D hCoordinates).slice_localDiffeomorph t c
  have hq' : q ∈ hl.localInverse.source := by
    rw [← hf]
    exact hl.localInverse_mem_source
  have hagree : (f.symm : (G.slices t.val).Point → C) =ᶠ[𝓝 q] hl.localInverse := by
    filter_upwards [hl.localInverse_open_source.mem_nhds hq'] with r hr
    have h := hl.localInverse_right_inv hr
    change f (hl.localInverse r) = r at h
    exact (congrArg f.symm h).symm.trans (f.left_inv (mem_univ _))
  exact ((hl.localInverse_contMDiffOn.contMDiffAt
    (hl.localInverse_open_source.mem_nhds hq')).congr_of_eventuallyEq hagree).contMDiffWithinAt

theorem ordinaryCaptureSliceChart_metric (t : (G.timeIntervals.interval K).Point)
    (c : C) (v w : TangentSpace (𝓡 n) c) :
    (G.slices t.val).metricOnPoints.inner (ordinaryCaptureSliceChart D hCoordinates t c)
      (mfderiv (𝓡 n) (𝓡 n) (ordinaryCaptureSliceChart D hCoordinates t) c v)
      (mfderiv (𝓡 n) (𝓡 n) (ordinaryCaptureSliceChart D hCoordinates t) c w) =
      (F.metric t.val).inner c v w :=
  (ordinaryCapture_movingCalculus D hCoordinates).slice_metric_eq t c v w

end PoincareConjecture.M14
