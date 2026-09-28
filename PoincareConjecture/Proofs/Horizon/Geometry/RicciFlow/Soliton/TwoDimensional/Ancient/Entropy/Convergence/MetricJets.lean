import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Convergence.Diffeomorphisms
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Coordinates
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SpatialJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem tendstoUniformlyOn_coordinate_metricJet (G : AncientCompactTimeConvergence S)
    (q : G.limit.carrier.carrier) (j r : ℕ) (a b : Fin n)
    {A : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hsub : A ⊆ {p | p.1 ∈ ancientM18TimeWindow j ∧
      p.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm p.2 ∈ G.exhaustion j}) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r (ancientPullbackCoefficient (G.embedding k) q a b))
      (iteratedFDeriv ℝ r (G.limit.carrier.coordinateCoefficient q
        (fun t x v w => (G.limit.flow.metric t).inner x v w) a b)) atTop A := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q j r A hA hsub ε hε
  filter_upwards [eventually_ge_atTop N] with k hk p hp
  simpa only [dist_eq_norm, MetricJet, norm_sub_rev] using hN k hk a b p hp

theorem timeWindow_mem_nhds_neg_one {k : ℕ} (hk : 1 ≤ k) :
    ancientM18TimeWindow k ∈ 𝓝 (-1 : ℝ) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  apply Icc_mem_nhds
  · linarith
  · have hpos : 0 < (k : ℝ) + 1 := by positivity
    have hi : ((k : ℝ) + 1)⁻¹ < 1 := (inv_lt_one₀ hpos).mpr (by linarith)
    linarith

theorem tendstoUniformlyOn_coordinate_spatial_metricJet_neg_one
    (G : AncientCompactTimeConvergence S) (q : G.limit.carrier.carrier)
    (j r : ℕ) (a b : Fin n) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsCompact A)
    (hsub : A ⊆ {y | y ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm y ∈ G.exhaustion j}) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r (fun y =>
        ancientPullbackCoefficient (G.embedding k) q a b (-1, y)))
      (iteratedFDeriv ℝ r (fun y => G.limit.carrier.coordinateCoefficient q
        (fun t x v w => (G.limit.flow.metric t).inner x v w) a b (-1, y))) atTop A := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ) (fun _ : Fin r =>
      ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n)))
  let A' : Set (ℝ × EuclideanSpace ℝ (Fin n)) := (fun y => (-1, y)) '' A
  have hA' : IsCompact A' := hA.image (continuous_const.prodMk continuous_id)
  have hsub' : A' ⊆ {p | p.1 ∈ ancientM18TimeWindow j ∧
      p.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm p.2 ∈ G.exhaustion j} := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨G.time_window_base j, hsub hy⟩
  have ht := (G.tendstoUniformlyOn_coordinate_metricJet q j r a b hA' hsub').comp
    (fun y : EuclideanSpace ℝ (Fin n) => (-1, y))
  have hs := P.uniformContinuous.comp_tendstoUniformlyOn (ht.mono (fun y hy => ⟨y, hy, rfl⟩))
  have hlim : ∀ y ∈ A,
      iteratedFDeriv ℝ r (fun z => G.limit.carrier.coordinateCoefficient q
        (fun t x v w => (G.limit.flow.metric t).inner x v w) a b (-1, z)) y =
      P (iteratedFDeriv ℝ r (G.limit.carrier.coordinateCoefficient q
        (fun t x v w => (G.limit.flow.metric t).inner x v w) a b) (-1, y)) := by
    intro y hy
    ext v
    exact Poincare.Analysis.iteratedFDeriv_spatial_slice _
      (G.contDiffAt_limit_coordinateCoefficient q a b (-1, y) (by norm_num)
        (hsub hy).1) r v
  have hsource : ∀ᶠ k in atTop, ∀ y ∈ A,
      iteratedFDeriv ℝ r (fun z => ancientPullbackCoefficient (G.embedding k) q a b (-1, z)) y =
      P (iteratedFDeriv ℝ r (ancientPullbackCoefficient (G.embedding k) q a b) (-1, y)) := by
    have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
    filter_upwards [eventually_ge_atTop (max j 1)] with k hk y hy
    ext v
    exact Poincare.Analysis.iteratedFDeriv_spatial_slice _
      ((G.embedding k).contDiffAt_coordinateCoefficient (G.exhaustion_open k)
        q a b (-1, y) (timeWindow_mem_nhds_neg_one ((le_max_right _ _).trans hk)) (by norm_num)
        ⟨(hsub hy).1, hmono ((le_max_left _ _).trans hk) (hsub hy).2⟩) r v
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hs ε hε, hsource] with k hk heq y hy
  rw [heq y hy, hlim y hy]
  exact hk y hy

end PoincareConjecture.AncientCompactTimeConvergence
