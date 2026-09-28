import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Nonflatness










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RawAncientSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance solutionCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

variable (C : ℕ → FlowCarrier.{0} 3)
  (F : ∀ k, RicciFlow 3 (C k).carrier (Iic 0)) (p : ∀ k, (C k).carrier)



theorem exists_ancientKappaSolution_on_closedPast
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ)
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (hnc : ∀ k, AncientKappaNoncollapsed (F k) κ)
    (hmono : ∀ k s t, s ≤ t → t ≤ 0 → ∀ x,
      ((F k).connection s).scalarCurvature x ≤ ((F k).connection t).scalarCurvature x)
    (G : AncientPointedGeometricConvergence C
      (fun k t => (F k).metric (t - δ)) p δ)
    (hcomplete : ∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t))
    (hbound : ∀ t ∈ Iio δ, ∀ x, (G.limitFlow.connection t).curvatureTensorNorm x ≤ 4)
    (hoperator : ∀ t ∈ Iio δ, ∀ x,
      (G.limitFlow.connection t).NonnegativeCurvatureOperator x)
    (hpositive : 0 < (G.limitFlow.connection 0).scalarCurvature G.base) :
    ∃ K : AncientKappaSolution 3 G.limitCarrier.carrier,
      K.kappa = κ / 27 ∧ K.flow.metric = G.limitFlow.metric := by
  have hstatic := interiorLimit_metricKappaNoncollapsed C F p P hκ hδ
    hop hnc hmono G hcomplete
  let Gclosed : RicciFlow 3 G.limitCarrier.carrier (Iic 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow G.limitFlow
      (fun t ht => (show t ≤ 0 from ht).trans_lt hδ) ordConnected_Iic
      closedAncientInterval.nontrivial
  have hcompleteClosed : ∀ t ≤ 0, MetricComplete (Gclosed.metric t) :=
    fun t ht => hcomplete t (ht.trans_lt hδ)
  have hoperatorClosed : ∀ t ≤ 0, ∀ x,
      (Gclosed.connection t).NonnegativeCurvatureOperator x :=
    fun t ht x => hoperator t (ht.trans_lt hδ) x
  have hboundClosed : ∀ t ≤ 0, ∀ x, (Gclosed.connection t).curvatureTensorNorm x ≤ 4 :=
    fun t ht x => hbound t (ht.trans_lt hδ) x
  have hnonflat :=
    Gclosed.scalarCurvature_positive_somewhere_of_bounded_ancient_of_m23_predecessors P
      hcompleteClosed hoperatorClosed (by norm_num) hboundClosed ⟨G.base, hpositive⟩
  let K : AncientKappaSolution 3 G.limitCarrier.carrier := {
    flow := Gclosed
    kappa := κ / 27
    kappa_pos := div_pos hκ (by norm_num)
    complete := hcompleteClosed
    nonnegative_curvature_operator := hoperatorClosed
    bounded_curvature := fun t ht => ⟨4, by norm_num, fun x => by
      rw [abs_of_nonneg (show 0 ≤ (Gclosed.connection t).curvatureTensorNorm x from
        Real.sqrt_nonneg _)]
      exact hboundClosed t ht x⟩
    nonflat := fun t ht => by
      obtain ⟨x, hx⟩ := hnonflat t ht
      refine ⟨x, ?_⟩
      have h := (Gclosed.connection t).scalarCurvature_le_curvatureTensorNorm_sharp x
      norm_num at h
      intro hz
      rw [hz, mul_zero] at h
      exact hx.not_ge h
    noncollapsed := by
      intro r₀ hr₀ t ht x r hr hrr₀ hcurv
      apply (hstatic t (ht.trans_lt hδ)).2 x r hr
      intro y hy
      exact hcurv t ⟨by nlinarith [sq_pos_of_pos hr], le_rfl⟩ y hy
  }
  exact ⟨K, rfl, rfl⟩



theorem exists_bounded_ancientKappaSolution_limit
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ : ℝ} (hκ : 0 < κ)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (hnc : ∀ k, AncientKappaNoncollapsed (F k) κ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (hnormalized : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    (hmono : ∀ k s t, s ≤ t → t ≤ 0 → ∀ x,
      ((F k).connection s).scalarCurvature x ≤ ((F k).connection t).scalarCurvature x) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ G : AncientPointedGeometricConvergence C
          (fun k t => (F k).metric (t - δ)) p δ,
        ∃ K : AncientKappaSolution 3 G.limitCarrier.carrier,
          K.kappa = κ / 27 ∧ K.flow.metric = G.limitFlow.metric ∧
          (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
          (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
            (G.limitFlow.connection t).curvatureTensorNorm x ≤ 4) ∧
          (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
            (G.limitFlow.connection t).NonnegativeCurvatureOperator x) ∧
          (1 : ℝ) / 2 ≤ (G.limitFlow.connection 0).scalarCurvature G.base := by
  have hbase (k : ℕ) (t : ℝ) (ht : t ≤ 0) :
      ((F k).connection t).scalarCurvature (p k) ≤ 1 := by
    simpa only [hnormalized] using hmono k t 0 ht le_rfl (p k)
  obtain ⟨δ, hδ, hδone, G, hcomplete, hnorm, hoperator, hscalar⟩ :=
    exists_complete_bounded_nonflat_interior_geometric_limit C F p P hκ
      hc hop hnc L hL hbound hnormalized hbase
  obtain ⟨K, hKκ, hKmetric⟩ := exists_ancientKappaSolution_on_closedPast C F p P hκ hδ
    hop hnc hmono G hcomplete hnorm hoperator (lt_of_lt_of_le (by norm_num) hscalar)
  exact ⟨δ, hδ, hδone, G, K, hKκ, hKmetric, hcomplete, hnorm, hoperator, hscalar⟩

end PoincareConjecture.RawAncientSequence
