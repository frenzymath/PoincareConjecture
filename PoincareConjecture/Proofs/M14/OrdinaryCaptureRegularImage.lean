import PoincareConjecture.Proofs.M14.OrdinaryCaptureRegularDomain
import PoincareConjecture.Proofs.M14.OrdinaryCaptureRegularPoint
import PoincareConjecture.Proofs.M14.Sec6_3_StableOpenness











set_option autoImplicit false

open Set
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




theorem ordinaryCapture_regularImage_mem_stableImage
    (E : M14ExponentialFamily G t₀.val (e.toSpacetime (t₀, c₀)))
    {τ : ℝ} (H : M14StableSet G t₀.val τ (e.toSpacetime (t₀, c₀)) E)
    (A : LExponentialGeometry F t₀.val τmax c₀)
    (q : (G.slices (t₀.val - τ)).Point) (hq : q.val ∈ range e.toSpacetime)
    (hreg : (D.point_map q.val, τ) ∈ A.regularImage) :
    q ∈ H.endpoint_slice_map '' H.carrier := by
  let W := (A.regular_chart.symm (D.point_map q.val, τ)).1
  have htime := A.regular_inverse_time (D.point_map q.val, τ) hreg
  have hsource := A.regular_chart.map_target hreg
  have hWreg : (W, τ) ∈ A.toLExponentialFamily.regularDomain := by
    rw [A.regular_source] at hsource
    change ((A.regular_chart.symm (D.point_map q.val, τ)).1,
      (A.regular_chart.symm (D.point_map q.val, τ)).2) ∈
        A.toLExponentialFamily.regularDomain at hsource
    simpa only [W, htime] using hsource
  have hendpoint : A.gamma W τ = D.point_map q.val := by
    have h := congrArg Prod.fst ((A.regular_forward
      (A.regular_chart.symm (D.point_map q.val, τ))).symm.trans
        (A.regular_chart.right_inv hreg))
    simpa only [W, htime] using h
  have hstable := ordinaryCapture_stable_of_regular t₀ c₀ D hCoordinates hPath E A W hWreg
  have hZH := (H.carrier_exact (g.spatialTangentEquiv t₀ c₀ W)).mpr hstable
  have htransport := ordinaryCapture_unique_family_transport t₀ c₀ D hCoordinates hPath E
    A.toLExponentialFamily W hWreg.1
  refine ⟨g.spatialTangentEquiv t₀ c₀ W, hZH, ?_⟩
  apply Subtype.ext
  rw [H.endpoint_slice_map_val _ hZH, H.endpoint_map_eq _ hZH]
  apply ordinaryCapture_point_injective D htransport.2.1 hq
  · have hclock : G.spacetime.timeFunction
        (E.gamma (g.spatialTangentEquiv t₀ c₀ W) (Real.sqrt τ)) = t₀.val - τ := by
      simpa only [Real.sq_sqrt H.tau_pos.le] using E.clock _ _ htransport.1.1
    exact hclock.trans q.property.symm
  · exact htransport.2.2.trans hendpoint




theorem ordinaryCapture_regular_point_at_cylinder
    (hDifferential : ReducedLengthDifferentialTheory F t₀.val τmax)
    (E : M14ExponentialFamily G t₀.val (e.toSpacetime (t₀, c₀)))
    {τ : ℝ} (H : M14StableSet G t₀.val τ (e.toSpacetime (t₀, c₀)) E)
    (hmax : τ < τmax) (Z : G.Horizontal (e.toSpacetime (t₀, c₀))) (hZ : Z ∈ H.carrier)
    (p : M14BackwardPath G t₀.val 0 τ (e.toSpacetime (t₀, c₀)) (H.endpoint_map Z))
    (hp : M14IsMinimizing p)
    (hc : ∀ s ∈ Icc 0 τ, p.curve s ∈ range e.toSpacetime) :
    ∃ r : ReducedLengthRegularPoint F t₀.val τmax c₀ (D.point_map (H.endpoint_map Z)) τ,
      r.path.curve = (D.path_map 0 τ _ _ p hc).curve := by
  obtain ⟨A⟩ := hDifferential.exponential_geometry c₀
  have hstable := (H.carrier_exact Z).mp hZ
  have hreg := ordinaryCapture_regular_of_stable t₀ c₀ D hCoordinates hPath E A
    H.tau_pos hmax Z hstable
  let W := (g.spatialTangentEquiv t₀ c₀).symm Z
  have hsource : (W, τ) ∈ A.regular_chart.source := by rw [A.regular_source]; exact hreg
  have htarget := A.regular_chart.map_source hsource
  have htransport := ordinaryCapture_unique_branch_transport t₀ c₀ D hCoordinates hPath E A
    H.tau_pos hmax Z (stableInitialVector_unique_branch E hstable)
  have hpoint : A.gamma W τ = D.point_map (H.endpoint_map Z) := by
    rw [H.endpoint_map_eq Z hZ]
    exact htransport.2.2.symm
  rw [A.regular_forward, hpoint] at htarget
  let r := A.regular_point (D.point_map (H.endpoint_map Z), τ) htarget
  let q := D.path_map 0 τ _ _ p hc
  have hqmin := (ordinaryCapture_minimizing_transport D hCoordinates hmax.le
    (mem_range_self _) p hc).mp hp
  have hqstart : q.curve 0 = c₀ :=
    (D.path_start_eq 0 τ _ _ p hc).trans (D.point_map_on_cylinder t₀ c₀)
  have hqend : q.curve τ = D.point_map (H.endpoint_map Z) := D.path_end_eq 0 τ _ _ p hc
  have heq := (r.unique_minimizing_path q hqstart hqend hqmin).symm
  exact ⟨ordinaryCaptureReplaceRegularPath r q heq, rfl⟩

end PoincareConjecture.M14
