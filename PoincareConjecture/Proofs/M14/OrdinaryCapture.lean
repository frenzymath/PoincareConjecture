import PoincareConjecture.Proofs.M14.OrdinaryCaptureFullMeasure











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

section Capture

variable {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T3Space C] [ConnectedSpace C] [SecondCountableTopology C]
  [MeasurableSpace C] [BorelSpace C] {K : SpacetimeInterval}
  {e : CompatibleSpacetimeCylinder G.spacetime (G.timeIntervals.interval K) C}
  {g : SpacetimeCylinderMetric e} {F : RicciFlow n C K.domain} {T τmax : ℝ}
  (D : M14OrdinaryCaptureData G C K e g F T τmax)
  (hCoordinates : SpacetimeGaugeTheory.{u, u} G.leafwise G.timeIntervals)
  (hPath : M14PathCalculusConclusion G)

omit [T3Space C] [ConnectedSpace C] [SecondCountableTopology C]
  [MeasurableSpace C] [BorelSpace C] in
private theorem capture_regular_base_cast {a b q : C} {τ : ℝ} (h : a = b)
    (r : ReducedLengthRegularPoint F T τmax a q τ) :
    (h ▸ r : ReducedLengthRegularPoint F T τmax b q τ).path.curve = r.path.curve := by
  cases h
  rfl

include D hCoordinates hPath




theorem ordinaryCapture_regular_locus
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    {τ : ℝ} {x : G.Point} (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E) (hmax : τ < τmax) (hx : x ∈ range e.toSpacetime)
    (Z : G.Horizontal x) (hZ : Z ∈ H.carrier)
    (p : M14BackwardPath G T 0 τ x (H.endpoint_map Z)) (hp : M14IsMinimizing p)
    (hc : ∀ s ∈ Icc 0 τ, p.curve s ∈ range e.toSpacetime) :
    ∃ r : ReducedLengthRegularPoint F T τmax
        (D.point_map x) (D.point_map (H.endpoint_map Z)) τ,
      r.path.curve = (D.path_map 0 τ x (H.endpoint_map Z) p hc).curve := by
  rcases hx with ⟨⟨t₀, c₀⟩, rfl⟩
  have hT : T = t₀.val := E.base_time.symm.trans (e.time_eq (t₀, c₀))
  subst T
  obtain ⟨r, hr⟩ :=
    ordinaryCapture_regular_point_at_cylinder t₀ c₀ D hCoordinates hPath hDifferential E H
      hmax Z hZ p hp hc
  let hbase := (D.point_map_on_cylinder t₀ c₀).symm
  exact ⟨hbase ▸ r, (capture_regular_base_cast hbase r).trans hr⟩




theorem ordinaryCapture_stable_full_measure
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ K.domain)
    {τ : ℝ} {x : G.Point} (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E) (hmax : τ < τmax) (hx : x ∈ range e.toSpacetime) :
    calibratedMetricVolume (G.slices (T - τ)).metricOnPoints
      ({q | q.val ∈ range e.toSpacetime} \ (H.endpoint_slice_map '' H.carrier)) = 0 := by
  rcases hx with ⟨⟨t₀, c₀⟩, rfl⟩
  have hT : T = t₀.val := E.base_time.symm.trans (e.time_eq (t₀, c₀))
  subst T
  exact ordinaryCapture_full_measure_at_cylinder t₀ c₀ D hCoordinates hPath
    hL hDifferential hwindow E H hmax

end Capture





theorem ordinaryCaptureStatement
    (hCoordinates : SpacetimeGaugeTheory.{u, u} G.leafwise G.timeIntervals)
    (hPath : M14PathCalculusConclusion G) (O : M14OrdinaryProviders.{u} n) :
    M14OrdinaryCaptureStatement G O := by
  intro C _ _ _ _ _ _ _ _ K e g F T τmax hT hτmax hwindow hcurvature D
  let L := Classical.choice (O.m08 C K.domain F T τmax hT hτmax hwindow hcurvature)
  let Dlength := Classical.choice (O.m09 C K.domain F T τmax hT hτmax hwindow hcurvature L)
  let V := Classical.choice (O.m10 C K.domain F T τmax hT hτmax hwindow hcurvature L Dlength)
  refine ⟨{
    L := L
    Dlength := Dlength
    V := V
    action_transport := fun _ _ _ _ p hc => ordinaryCapture_action_transport D hCoordinates p hc
    captured_action_value_eq := fun _ _ _ _ _ _ hmax hx _ =>
      ordinaryCapture_actionValue_eq D hmax hx
    reduced_length_transport := fun _ _ _ hτ hmax htx hty hx hy =>
      ordinaryCapture_reducedLength_transport D hCoordinates hτ hmax htx hty hx hy
    minimizing_transport := fun _ _ _ _ hmax hx p hc =>
      ordinaryCapture_minimizing_transport D hCoordinates hmax hx p hc
    regular_locus_transport := fun _ _ _ hmax hx E H Z hZ _ p hp _ hc =>
      ordinaryCapture_regular_locus D hCoordinates hPath Dlength E H hmax hx Z hZ p hp hc
    volume_transport := fun _ _ _ H hmax hx =>
      ordinaryCapture_volume_transport D hCoordinates hwindow H hmax hx
    endpoint_image_captured := fun _ _ _ H hmax hx => ordinaryCapture_endpoint_image D H hmax hx
    slice_measure_transport := fun _ _ _ H hmax hx =>
      ordinaryCapture_stable_slice_measure D hCoordinates hwindow H hmax hx
    captured_stable_image_full_measure := fun _ _ E H hmax hx =>
      ordinaryCapture_stable_full_measure D hCoordinates hPath L Dlength hwindow E H hmax hx
    captured_slice_measure_transport := ?_ }, rfl, rfl, rfl⟩
  intro τ hτ hmax A hA hc
  have ht : T - τ ∈ K.domain :=
    hwindow ⟨sub_le_sub_left hmax.le T, sub_le_self T hτ.le⟩
  exact ordinaryCapture_slice_measure D hCoordinates ⟨T - τ, ht⟩ hA hc

end PoincareConjecture.M14
