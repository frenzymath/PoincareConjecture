import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Coordinates
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}
  (G : AncientCompactTimeConvergence S)

theorem exists_coordinate_neighborhood (q : G.limit.carrier.carrier)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 < 0)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    ∃ j, ∃ U : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsOpen U ∧ p ∈ U ∧
      ∀ z ∈ U, ancientM18TimeWindow j ∈ 𝓝 z.1 ∧
        z.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion j := by
  let c := extChartAt (𝓡 n) q
  obtain ⟨j, hjt, hjx⟩ := ((eventually_timeWindow_mem_nhds ht).and
    (G.eventually_mem_exhaustion (c.symm p.2))).exists
  have hc : ContinuousAt c.symm p.2 :=
    ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hp).contMDiffAt
      (extChartAt_target_mem_nhds' hp)).continuousAt
  have hU : ∀ᶠ z : ℝ × EuclideanSpace ℝ (Fin n) in 𝓝 p,
      ancientM18TimeWindow j ∈ 𝓝 z.1 ∧ z.2 ∈ c.target ∧ c.symm z.2 ∈ G.exhaustion j :=
    inter_mem
      (continuousAt_fst.preimage_mem_nhds (eventually_mem_nhds_iff.mpr hjt))
      (inter_mem (continuousAt_snd.preimage_mem_nhds (extChartAt_target_mem_nhds' hp))
        ((hc.comp continuousAt_snd).preimage_mem_nhds ((G.exhaustion_open j).mem_nhds hjx)))
  obtain ⟨U, hUsub, hUo, hpU⟩ := mem_nhds_iff.mp hU
  exact ⟨j, U, hUo, hpU, hUsub⟩

theorem eventually_coordinate_domain (q : G.limit.carrier.carrier)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 < 0)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    ∀ᶠ z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) in atTop ×ˢ 𝓝 p,
      ancientM18TimeWindow z.1 ∈ 𝓝 z.2.1 ∧
        z.2.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm z.2.2 ∈ G.exhaustion z.1 := by
  obtain ⟨j, U, hUo, hpU, hU⟩ := G.exists_coordinate_neighborhood q p ht hp
  filter_upwards [(eventually_ge_atTop j).prod_mk (hUo.mem_nhds hpU)] with z hz
  exact ⟨mem_of_superset (hU z.2 hz.2).1 (ancientM18TimeWindow_mono hz.1),
    (hU z.2 hz.2).2.1, G.exhaustion_monotone hz.1 (hU z.2 hz.2).2.2⟩

theorem tendsto_coordinate_metricJet_prod (q : G.limit.carrier.carrier) (r : ℕ)
    (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 < 0)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦
      iteratedFDeriv ℝ r (ancientPullbackCoefficient (G.embedding z.1) q a b) z.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (iteratedFDeriv ℝ r (G.limit.carrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limit.flow.metric t).inner x v w) a b) p)) := by
  obtain ⟨j, U, hUo, hpU, hU⟩ := G.exists_coordinate_neighborhood q p ht hp
  obtain ⟨C, hC, hpC, hCU⟩ := exists_compact_between isCompact_singleton hUo
    (singleton_subset_iff.mpr hpU)
  have hCn : C ∈ 𝓝 p := mem_of_superset
    (isOpen_interior.mem_nhds (hpC (mem_singleton p))) interior_subset
  have hdom : C ⊆ {z | z.1 ∈ ancientM18TimeWindow j ∧
      z.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion j} := fun z hz ↦
    ⟨mem_of_mem_nhds (hU z (hCU hz)).1, (hU z (hCU hz)).2⟩
  have hunif : TendstoUniformlyOn
      (fun k ↦ iteratedFDeriv ℝ r (ancientPullbackCoefficient (G.embedding k) q a b))
      (iteratedFDeriv ℝ r (G.limit.carrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limit.flow.metric t).inner x v w) a b)) atTop C := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q j r C hC hdom ε hε
    exact (eventually_ge_atTop N).mono (fun k hk z hz ↦ by
      simpa only [dist_eq_norm, norm_sub_rev, MetricJet] using hN k hk a b z hz)
  have hunif' : TendstoUniformlyOn
      (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ r (ancientPullbackCoefficient (G.embedding z.1) q a b))
      (iteratedFDeriv ℝ r (G.limit.carrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limit.flow.metric t).inner x v w) a b)) (atTop ×ˢ 𝓝 p) C :=
    fun V hV ↦ tendsto_fst.eventually (hunif V hV)
  apply hunif'.tendsto_comp
    ((G.contDiffAt_limit_coordinateCoefficient q a b p ht hp).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top : (r : ℕ∞ω) ≤ ∞)).continuousWithinAt
  rw [nhdsWithin_eq_nhds.mpr hCn]
  exact tendsto_snd

theorem tendsto_coordinate_spatial_metricJet_prod (q : G.limit.carrier.carrier) (r : ℕ)
    (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 < 0)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦ iteratedFDeriv ℝ r
      (fun y ↦ ancientPullbackCoefficient (G.embedding z.1) q a b (z.2.1, y)) z.2.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (iteratedFDeriv ℝ r (fun y ↦ G.limit.carrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limit.flow.metric t).inner x v w) a b (p.1, y)) p.2)) := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ) (fun _ : Fin r ↦
      ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n)))
  have h := P.continuous.continuousAt.tendsto.comp
    (G.tendsto_coordinate_metricJet_prod q r a b p ht hp)
  have hlim : iteratedFDeriv ℝ r (fun y ↦ G.limit.carrier.coordinateCoefficient q
      (fun t x v w ↦ (G.limit.flow.metric t).inner x v w) a b (p.1, y)) p.2 =
      P (iteratedFDeriv ℝ r (G.limit.carrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limit.flow.metric t).inner x v w) a b) p) := by
    ext v
    exact Poincare.Analysis.iteratedFDeriv_spatial_slice _
      (G.contDiffAt_limit_coordinateCoefficient q a b p ht hp) r v
  rw [← hlim] at h
  apply h.congr'
  filter_upwards [G.eventually_coordinate_domain q p ht hp] with z hz
  ext v
  exact (Poincare.Analysis.iteratedFDeriv_spatial_slice _
    ((G.embedding z.1).contDiffAt_coordinateCoefficient (G.exhaustion_open z.1)
      q a b z.2 hz.1 (ancientM18TimeWindow_subset z.1 (mem_of_mem_nhds hz.1)) hz.2) r v).symm

end PoincareConjecture.AncientCompactTimeConvergence
