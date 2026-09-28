import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Infinity.RayWindows
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Infinity.Scale
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Escaping.Contradiction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.Based
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.StrongNeck












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space



theorem AncientKappaSolution.exists_strongNeck_far_on_ray_of_services
    (P : NoncompactKappaServices.{u})
    {M : Type u} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    (K : AncientKappaSolution 3 M) (p : M)
    (hno : NoEmbeddedTrivialNormalProjectivePlane K)
    (hdist : ∀ x y : M, dist x y = ((K.flow.metric 0).edist x y).toReal)
    (ray : ℝ → M) (hray : Poincare.Riemannian.Soul.IsRay ray) (hzero : ray 0 = p)
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4) (L : ℝ) :
    ∃ q : M, L < ((K.flow.metric 0).edist p q).toReal ∧
      ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = q := by
  let A (k : ℕ) := Classical.choice (P.normalization M K (ray k) 0 le_rfl)
  let scale (k : ℕ) := Real.sqrt ((K.flow.connection 0).scalarCurvature (ray k))
  have hscale (k : ℕ) : 0 < scale k := by
    have h := (A k).scale_pos
    rw [(A k).scale_eq] at h
    exact Real.sqrt_pos.mpr h
  have hdistance (k : ℕ) : ((K.flow.metric 0).edist (ray k) p).toReal = k := by
    rw [← hdist, ← hzero, hray (Nat.cast_nonneg k) le_rfl]
    simp only [sub_zero, abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)]
  have hescape := K.ray_curvature_scale_tendsto_atTop_of_services P p ray hdistance
  have htarget (k : ℕ) : AncientKappaNoncollapsed (A k).target.flow K.kappa := by
    rw [← (A k).target_kappa]
    exact (A k).target.noncollapsed
  let B (k : ℕ) := (A k).target.toSmallBased (ray k) K.kappa_pos
    (htarget k) (A k).normalized_scalar
  let S : NormalizedKappaSolutionSequence K.kappa := ⟨K.kappa_pos, B⟩
  have hBdist (k : ℕ) (x y : M) :
      (((B k).flow.flow.metric 0).edist (equivShrink M x) (equivShrink M y)).toReal =
        scale k * dist x y := by
    change (((A k).target.flow.shrink.metric 0).edist
      (equivShrink M x) (equivShrink M y)).toReal = _
    rw [RicciFlow.shrink_edist, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      (A k).toReal_edist_zero, (A k).scale_eq, hdist]
  let arc (k : ℕ) (t : ℝ) : (B k).carrier.carrier :=
    equivShrink M (ray ((k : ℝ) + t / scale k))
  have hwindow (s t : ℝ) : ∀ᶠ k in atTop,
      (((B k).flow.flow.metric 0).edist (arc k s) (arc k t)).toReal = |s - t| := by
    simpa only [arc, hBdist] using hray.eventually_rescaled_window_distance hscale hescape s t
  have hbase (k : ℕ) : arc k 0 = (B k).base := by
    change equivShrink M (ray ((k : ℝ) + 0 / scale k)) = equivShrink M (ray k)
    rw [zero_div, add_zero]
  have hbound (t : ℝ) : ∀ᶠ k in atTop,
      arc k t ∈ ((B k).flow.flow.metric 0).ball (B k).base (|t| + 1) := by
    filter_upwards [hwindow 0 t] with k hk
    rw [hbase] at hk
    apply (ENNReal.lt_ofReal_iff_toReal_lt
      (((B k).flow.flow.metric 0).edist_ne_top _ _)).mpr
    rw [hk, zero_sub, abs_neg]
    linarith
  obtain ⟨C⟩ := P.normalized_compactness ⟨K.kappa, K.kappa_pos, S⟩
  let G := C.convergence
  obtain ⟨line, hline⟩ := C.terminal_extension.exists_minimizing_line_of_source_arcs
    (fun k => arc (G.subsequence k))
    (fun t => ⟨|t| + 1, by positivity,
      G.subsequence_strictMono.tendsto_atTop.eventually (hbound t)⟩)
    (fun s t => tendsto_const_nhds.congr'
      ((G.subsequence_strictMono.tendsto_atTop.eventually (hwindow s t)).mono
        fun _ hk => hk.symm))
  have hplanes (k : ℕ) : NoEmbeddedTrivialNormalProjectivePlane (S.term k).flow :=
    (A k).target.toSmallBased_noEmbeddedTrivialNormalProjectivePlane
      (ray k) K.kappa_pos (htarget k) (A k).normalized_scalar hno
  have hnecks := C.terminal_extension.eventually_strongEvolvingNeck_of_line_of_services
    P hplanes line hline hε hεsmall
  have hfar : ∀ᶠ k in atTop, L < (G.subsequence k : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp G.subsequence_strictMono.tendsto_atTop).eventually
      (eventually_gt_atTop L)
  obtain ⟨k, hfar, Nk, hNk⟩ := (hfar.and hnecks).exists
  refine ⟨ray (G.subsequence k), ?_, ?_⟩
  · rw [← hdist, dist_comm, hdist, hdistance]
    exact hfar
  · obtain ⟨N, hN⟩ := (A (G.subsequence k)).target.strongNeck_of_toSmallBased
      (ray (G.subsequence k)) K.kappa_pos (htarget (G.subsequence k))
      (A (G.subsequence k)).normalized_scalar ⟨Nk, hNk⟩
    exact ⟨(A (G.subsequence k)).strongNeckFromNormalization le_rfl N hN, rfl⟩

theorem AncientKappaSolution.exists_strongNeck_far_on_ray
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {M : Type u} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    (K : AncientKappaSolution 3 M) (p : M)
    (hno : NoEmbeddedTrivialNormalProjectivePlane K)
    (hdist : ∀ x y : M, dist x y = ((K.flow.metric 0).edist x y).toReal)
    (ray : ℝ → M) (hray : Poincare.Riemannian.Soul.IsRay ray) (hzero : ray 0 = p)
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4) (L : ℝ) :
    ∃ q : M, L < ((K.flow.metric 0).edist p q).toReal ∧
      ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = q := by
  exact AncientKappaSolution.exists_strongNeck_far_on_ray_of_services P.noncompactServices K p hno hdist ray hray hzero hε hεsmall L



theorem AncientKappaSolution.exists_strongNeck_arbitrarily_far_of_services
    (P : NoncompactKappaServices.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    (K : AncientKappaSolution 3 M) (p : M)
    (hno : NoEmbeddedTrivialNormalProjectivePlane K)
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4) (L : ℝ) :
    ∃ q : M, L < ((K.flow.metric 0).edist p q).toReal ∧
      ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = q := by
  let g := K.flow.metric 0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let : MetricSpace M := EMetricSpace.toMetricSpace g.edist_ne_top
  let : ProperSpace M := g.properSpace_of_complete (K.complete 0 le_rfl) (fun _ _ => rfl)
  obtain ⟨ray, hray, hzero, _⟩ := Poincare.Riemannian.Soul.exists_ray_in_closed_set
    (p := p) isClosed_univ (noncompact_univ M) (fun q _ => by
      obtain ⟨curve, h0, h1, hmin⟩ := g.hasMinimizingSegments_of_complete
        (K.complete 0 le_rfl) (fun _ _ => rfl) p q
      exact ⟨curve, h0, h1, hmin, fun _ _ => mem_univ _⟩)
  exact K.exists_strongNeck_far_on_ray_of_services P p hno (fun _ _ => rfl) ray hray hzero hε hεsmall L

theorem AncientKappaSolution.exists_strongNeck_arbitrarily_far
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    (K : AncientKappaSolution 3 M) (p : M)
    (hno : NoEmbeddedTrivialNormalProjectivePlane K)
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4) (L : ℝ) :
    ∃ q : M, L < ((K.flow.metric 0).edist p q).toReal ∧
      ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = q := by
  exact AncientKappaSolution.exists_strongNeck_arbitrarily_far_of_services P.noncompactServices K p hno hε hεsmall L



theorem AncientKappaSolution.exists_strongNeck_far_from_soul_of_services
    (P : NoncompactKappaServices.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    (K : AncientKappaSolution 3 M)
    (soul : RiemannianMetric.PointSoulData (K.flow.metric 0))
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4) (L : ℝ) :
    ∃ q : M, L < ((K.flow.metric 0).edist soul.center q).toReal ∧
      ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = q :=
  K.exists_strongNeck_arbitrarily_far_of_services P soul.center
    (soul.noEmbeddedTrivialNormalProjectivePlane K) hε hεsmall L

theorem AncientKappaSolution.exists_strongNeck_far_from_soul
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    (K : AncientKappaSolution 3 M)
    (soul : RiemannianMetric.PointSoulData (K.flow.metric 0))
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4) (L : ℝ) :
    ∃ q : M, L < ((K.flow.metric 0).edist soul.center q).toReal ∧
      ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = q := by
  exact AncientKappaSolution.exists_strongNeck_far_from_soul_of_services P.noncompactServices K soul hε hεsmall L

end PoincareConjecture
