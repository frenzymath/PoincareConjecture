import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.ScalarJets







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem nonempty_ancientCompactTimeConvergence (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) :
    Nonempty (AncientCompactTimeConvergence S) := by
  obtain ⟨σ, hσ, hside, hjets⟩ := S.exists_nested_spatial_diagonal_all_charts P
  have hstage : ∀ j, S.initialWindowIdentification P j ''
      ((S.nestedWindowLimit P 0).geometric_limit.exhaustion j) ⊆
        (S.nestedWindowLimit P j).geometric_limit.exhaustion (σ j) :=
    fun j => (image_mono subset_closure).trans (hside j)
  let E := fun j => S.nestedAncientEmbedding P j (σ j) (hstage j)
  refine ⟨{
    limit := S.ancientWindowLimit P
    subsequence := fun j => (S.nestedWindowLimit P j).geometric_limit.subsequence (σ j)
    subsequence_strictMono := S.nestedWindowLimit_diagonal_strictMono P hσ
    exhaustion := (S.nestedWindowLimit P 0).geometric_limit.exhaustion
    exhaustion_open := (S.nestedWindowLimit P 0).geometric_limit.exhaustion_open
    exhaustion_connected := (S.nestedWindowLimit P 0).geometric_limit.exhaustion_connected
    exhaustion_compactClosure := (S.nestedWindowLimit P 0).geometric_limit.exhaustion_compactClosure
    base_in_exhaustion := (S.nestedWindowLimit P 0).geometric_limit.base_in_exhaustion
    exhaustion_increasing := (S.nestedWindowLimit P 0).geometric_limit.exhaustion_increasing
    exhaustion_covers := (S.nestedWindowLimit P 0).geometric_limit.exhaustion_covers
    time_window_subset := ancientM18TimeWindow_subset
    time_window_increasing := ancientM18TimeWindow_increasing
    time_window_base := ancientM18TimeWindow_base
    time_window_covers := ancientM18TimeWindow_covers
    embedding := E
    spatial_time_independent := fun _ _ _ _ _ _ _ => rfl
    base_preserving := fun j => S.nestedAncientEmbedding_base P j (σ j) (hstage j)
    pullback_metric_CInfinity := ?_ }⟩
  intro q j r A hA hAU ε hε
  have hAneg : A ⊆ Iio 0 ×ˢ (extChartAt (𝓡 n) q).target :=
    fun p hp => ⟨ancientM18TimeWindow_subset j (hAU hp).1, (hAU hp).2.1⟩
  have hscalar (a b : Fin n) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r (ancientPullbackCoefficient (E k) q a b))
      (iteratedFDeriv ℝ r ((S.ancientWindowLimit P).carrier.coordinateCoefficient q
        (fun t x v w => ((S.ancientWindowLimit P).flow.metric t).inner x v w) a b))
      atTop A := by
    have h := S.tendstoUniformlyOn_originalNestedCoefficients_basis_jets P hside q
      (fun m B hB hBU => S.tendstoUniformlyOn_originalNestedCoefficients_jets P
        hside hjets q m hB hBU) r a b hA hAneg
    apply h.congr
    filter_upwards [eventually_ge_atTop j] with k hk p hp
    let V := (extChartAt (𝓡 n) q).target ∩ (extChartAt (𝓡 n) q).symm ⁻¹'
      (S.nestedWindowLimit P 0).geometric_limit.exhaustion k
    have hV : IsOpen V :=
      (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
        (isOpen_extChartAt_target (I := 𝓡 n) q)
        ((S.nestedWindowLimit P 0).geometric_limit.exhaustion_open k)
    have heq : EqOn (ancientPullbackCoefficient (E k) q a b)
        (fun z => S.originalNestedCoefficients P q k (σ k) z
          (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b))
        ((univ : Set ℝ) ×ˢ V) :=
      fun z hz => S.nestedAncientEmbedding_coefficient_eq P k (σ k) (hstage k) q a b hz.2
    exact ((eqOn_iteratedFDeriv_of_isOpen (isOpen_univ.prod hV) heq r)
      ⟨mem_univ _, (hAU hp).2.1,
        (S.nestedWindowLimit P 0).geometric_limit.exhaustion_monotone hk (hAU hp).2.2⟩).symm
  have hεall : ∀ᶠ k in atTop, ∀ a b : Fin n, ∀ p ∈ A,
      ‖MetricJet r (ancientPullbackCoefficient (E k) q a b) A p -
        MetricJet r ((S.ancientWindowLimit P).carrier.coordinateCoefficient q
          (fun t x v w => ((S.ancientWindowLimit P).flow.metric t).inner x v w) a b) A p‖ < ε := by
    apply eventually_all.mpr
    intro a
    apply eventually_all.mpr
    intro b
    simpa only [MetricJet, dist_eq_norm, norm_sub_rev] using
      Metric.tendstoUniformlyOn_iff.mp (hscalar a b) ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hεall
  exact ⟨max j N, le_max_left _ _, fun k hk => hN k ((le_max_right _ _).trans hk)⟩

noncomputable def ancientCompactTimeConvergence (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) : AncientCompactTimeConvergence S :=
  Classical.choice (S.nonempty_ancientCompactTimeConvergence P)

end PoincareConjecture.AncientRescalingSequence
