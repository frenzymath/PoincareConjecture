import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.UnitNeighborhood
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.MetricConvergence









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open Set Filter Poincare.Gluing Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric



theorem exists_source_embeddings_near_realized_unit_slice
    {n : ℕ} {X : Type*} [MetricSpace X] [ProperSpace X] {p : X}
    (hc : RayComparison p)
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, T3Space (M k)]
    [∀ k, PreconnectedSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)] [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k)) (q : ∀ k, ℕ → M k)
    (Φ : ∀ k, ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (M k) ∞)
    (h : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {S r : ℝ} (hr : 0 < r) (hrS : 3 * (r / 4) ≤ S)
    (hsource : ∀ k j, (Φ k j).source = Metric.ball 0 S)
    (htarget : ∀ k j, (Φ k j).target = (g k).ball (q k j) S)
    (hradial : ∀ k j x, x ∈ Metric.ball 0 S →
      (g k).edist (q k j) (Φ k j x) = ENNReal.ofReal ‖x‖)
    (helliptic : ∀ k j, ∀ x ∈ Metric.ball 0 (3 * (r / 4)), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ (g k).pullbackCoefficients (Φ k j) x v v ∧
      (g k).pullbackCoefficients (Φ k j) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2)
    (hjets : ∀ j m C, IsCompact C → C ⊆ Metric.ball 0 (r / 4) → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients (Φ k j)))
      (iteratedFDeriv ℝ m (h j).euclideanCoefficients) atTop C)
    (hbound : ∀ j (x v : EuclideanSpace ℝ (Fin n)),
      ‖v‖ / 2 ≤ (h j).tangentNorm x v ∧ (h j).tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (η : ℕ → basedMinimizingRays p)
    (hdense : DenseRange (fun j => asymptoticConeUnitProjection hc (asymptoticLinkProjection hc (η j))))
    (e : ∀ j, MetricCoordinateBall (h j) r → AsymptoticCone p hc)
    (he : ∀ j, Isometry (e j))
    (hecenter : ∀ j, e j ⟨0, Metric.mem_closedBall_self hr.le⟩ = asymptoticConeRayProjection hc (1, η j))
    (hecover : ∀ j, Metric.ball (e j ⟨0, Metric.mem_closedBall_self hr.le⟩) r ⊆ range (e j)) :
    letI : ∀ k, MetricSpace (M k) := fun k => (g k).toMetricSpace
    let U := fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)
    let hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
    letI : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
    let source : ∀ k i, Piece U i → M k := fun k i x => Φ k i x
    let hgeom := normal_chart_restriction_geometry g q Φ (by positivity : 0 < r / 4)
      hrS hsource htarget hradial helliptic
    ∀ (d : ∀ i j, C(Piece U i × Piece U j, ℝ))
      (hd : ∀ i j, TendstoLocallyUniformly
        (fun k (z : Piece U i × Piece U j) => dist (source k i z.1) (source k j z.2)) (d i j) atTop),
      (∀ i j x y, dist ((h i).uniformBallRestriction hr (e i) x)
        ((h j).uniformBallRestriction hr (e j) y) = d i j (x, y)) →
    letI : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
    let O := ChartDistance.overlapSystem
      (fun i j x y => (hd i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y)))
      (fun _ => 3 / 2) hgeom.1 (fun _ => 1 / 2) (fun _ => by norm_num)
      hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1
    letI := quotientChartedSpace U hU O
    (by exact IsManifold (𝓡 n) ∞ (Quotient O.setoid) ∧
    ∃ f : Quotient O.setoid → AsymptoticCone p hc,
      Topology.IsOpenEmbedding f ∧
      (∀ j x, f (O.include j x) = (h j).uniformBallRestriction hr (e j) x) ∧
      {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1} ⊆ range f ∧
      IsCompact (f ⁻¹' {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1}) ∧
      ∃ V : Set (Quotient O.setoid), IsOpen V ∧ IsCompact (closure V) ∧
        f ⁻¹' {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1} ⊆ V ∧
      ∃ F : ∀ k, Quotient O.setoid → M k,
        ChartDistance.HasLocalSourceModels U hU O source F V ∧
        (∀ᶠ k in atTop, Topology.IsOpenEmbedding (fun x : V => F k x) ∧
          IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k) V) ∧
        ∀ z ∈ V, ∃ i, ∃ W : Set (Piece U i), IsOpen W ∧
          z ∈ O.include i '' W ∧ O.include i '' W ⊆ V ∧
          ∀ m C, IsCompact C → C ⊆ Subtype.val '' W → TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients
              (ChartDistance.chartParametrization U hU (F k ∘ O.include i))))
            (iteratedFDeriv ℝ m (h i).euclideanCoefficients) atTop C) := by
  let : ∀ k, MetricSpace (M k) := fun k => (g k).toMetricSpace
  let U := fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)
  let hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
  let : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
  let source : ∀ k i, Piece U i → M k := fun k i x => Φ k i x
  have hgeom := normal_chart_restriction_geometry g q Φ (by positivity : 0 < r / 4)
    hrS hsource htarget hradial helliptic
  dsimp only
  intro d hd hcross
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let hp := fun i j x y => (hd i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := ChartDistance.overlapSystem hp (fun _ => 3 / 2) hgeom.1
    (fun _ => 1 / 2) (fun _ => by norm_num) hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1
  let := quotientChartedSpace U hU O
  have htrans := locallyEventuallyBoundedDerivatives_normal_chart_transition g q Φ h
    (by positivity : 0 < r / 4) hrS hsource htarget hradial helliptic hjets d hp
  have hsmooth := ChartDistance.overlapSystem_smooth U hU hp (fun _ => 3 / 2) hgeom.1
    (fun _ => 1 / 2) (fun _ => by norm_num) hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1
    hgeom.2.2.2.2 htrans
  refine ⟨quotient_isManifold U hU O hsmooth, ?_⟩
  have hrel := ChartDistance.overlapSystem_rel_iff hp (fun _ => 3 / 2) hgeom.1
    (fun _ => 1 / 2) (fun _ => by norm_num) hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1
  obtain ⟨f, hfopen, hfinclude, _, hfunit, hfcompact⟩ :=
    exists_open_unitNeighborhood_of_normal_chart_family hc h hr hbound η hdense e he
      hecenter hecover d O hrel hcross
  obtain ⟨V, hV, hVcompact, hKV, F, hmodels, hF⟩ :=
    exists_local_source_models_of_normal_chart_limits g q Φ h (by positivity : 0 < r / 4)
      hrS hsource htarget hradial helliptic hjets d hd 0 ∅ isCompact_empty
      (f ⁻¹' {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1}) hfcompact
  refine ⟨f, hfopen, hfinclude, hfunit, hfcompact, V, hV, hVcompact,
    fun x hx => hKV (Or.inl hx), F, hmodels, hF.mono (fun _ hk => ⟨hk.1, hk.2.1⟩), ?_⟩
  exact exists_local_source_metric_convergence_of_normal_charts U hU O g Φ
    (fun k i => by rw [hsource]; exact Metric.ball_subset_ball (by linarith)) h hjets hmodels

end PoincareConjecture.RiemannianMetric
