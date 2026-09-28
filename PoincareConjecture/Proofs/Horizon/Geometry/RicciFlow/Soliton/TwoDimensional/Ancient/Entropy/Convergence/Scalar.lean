import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Convergence.MetricJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Convergence.CurvatureJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Scalar
import Mathlib.Topology.UniformSpace.UniformApproximation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 2 M} {S : AncientRescalingSequence K}


theorem tendsto_scalarCurvature_at_coordinate_points_neg_one
    (G : AncientCompactTimeConvergence S)
    (q : G.limit.carrier.carrier) (j : ℕ)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : IsCompact A)
    (hsub : A ⊆ {y | y ∈ (extChartAt (𝓡 2) q).target ∧
      (extChartAt (𝓡 2) q).symm y ∈ G.exhaustion j})
    {p : EuclideanSpace ℝ (Fin 2)} (hpA : A ∈ 𝓝 p)
    {α : Type*} {l : Filter α} [l.NeBot] (k : α → ℕ) (hk : Tendsto k l atTop)
    (y : α → EuclideanSpace ℝ (Fin 2)) (hy : Tendsto y l (𝓝 p)) :
    Tendsto (fun i => ((S.rescaling (G.subsequence (k i))).flow.connection (-1)).scalarCurvature
      ((G.embedding (k i)).toFun (-1, (extChartAt (𝓡 2) q).symm (y i))).2) l
      (𝓝 ((G.limit.flow.connection (-1)).scalarCurvature ((extChartAt (𝓡 2) q).symm p))) := by
  classical
  have hp := hsub (mem_of_mem_nhds hpA)
  obtain ⟨g, D, V, hVo, hpV, _, heq⟩ := G.limit.carrier.exists_local_coordinate_realization
    (G.limit.flow.metric (-1)) q (-1) p hp.1
  have hg : ∀ᶠ z in 𝓝 p, ∀ a b : Fin 2,
      g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin 2) ℝ a)
        (EuclideanSpace.basisFun (Fin 2) ℝ b) =
      G.limit.carrier.coordinateCoefficient q
        (fun _ x v w => (G.limit.flow.metric (-1)).inner x v w) a b (-1, z) :=
    Filter.Eventually.mono (hVo.mem_nhds hpV) heq
  have hev : ∀ᶠ i in l, ancientM18TimeWindow (k i) ∈ 𝓝 (-1 : ℝ) ∧
      y i ∈ (extChartAt (𝓡 2) q).target ∧
      (extChartAt (𝓡 2) q).symm (y i) ∈ G.exhaustion (k i) := by
    filter_upwards [hk.eventually (eventually_ge_atTop (max j 1)), hy.eventually hpA]
      with i hki hyi
    exact ⟨timeWindow_mem_nhds_neg_one ((le_max_right _ _).trans hki),
      (hsub hyi).1, G.exhaustion_monotone ((le_max_left _ _).trans hki) (hsub hyi).2⟩
  have hreal : ∀ᶠ i in l,
      ∃ gd : Σ g : RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2)), LeviCivitaData g,
        ∀ᶠ z in 𝓝 (y i), ∀ a b : Fin 2,
          gd.1.euclideanCoefficients z (EuclideanSpace.basisFun (Fin 2) ℝ a)
            (EuclideanSpace.basisFun (Fin 2) ℝ b) =
          ancientPullbackCoefficient (G.embedding (k i)) q a b (-1, z) := by
    filter_upwards [hev] with i hi
    obtain ⟨gi, Di, hi'⟩ := (G.embedding (k i)).exists_local_coordinate_realization
      (G.exhaustion_open (k i)) q (-1, y i) hi.1 hi.2
    exact ⟨⟨gi, Di⟩, hi'⟩
  obtain ⟨gd, hgd⟩ := hreal.choice
  have hscalar := LeviCivitaData.tendsto_scalarCurvature_of_scalar_metric_jets_at_points
    (fun i => (gd i).2) D y p (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (by
      intro r _ a b
      simp only [OrthonormalBasis.coe_toBasis]
      erw [G.limit.carrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        q _ (-1) p g hg r a b]
      have hunif := G.tendstoUniformlyOn_coordinate_spatial_metricJet_neg_one q j r a b hA hsub
      have hunif' : TendstoUniformlyOn
          (fun i => iteratedFDeriv ℝ r (fun z =>
            ancientPullbackCoefficient (G.embedding (k i)) q a b (-1, z)))
          (iteratedFDeriv ℝ r (fun z => G.limit.carrier.coordinateCoefficient q
            (fun t x v w => (G.limit.flow.metric t).inner x v w) a b (-1, z))) l A :=
        fun u hu => hk.eventually (hunif u hu)
      have hcont : ContDiffAt ℝ ∞ (fun z => G.limit.carrier.coordinateCoefficient q
          (fun t x v w => (G.limit.flow.metric t).inner x v w) a b (-1, z)) p :=
        (G.contDiffAt_limit_coordinateCoefficient q a b (-1, p) (by norm_num) hp.1).comp p
          (contDiffAt_const.prodMk contDiffAt_id)
      have hr : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
        change (↑(r : ℕ∞) : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top
      have ht := hunif'.tendsto_comp
        (hcont.continuousAt_iteratedFDeriv hr).continuousWithinAt
        (tendsto_nhdsWithin_iff.mpr ⟨hy, hy.eventually hpA⟩)
      apply ht.congr'
      filter_upwards [hgd] with i hi
      exact (G.limit.carrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        q (ancientPullbackInnerValue (G.embedding (k i))) (-1) (y i) (gd i).1 hi r a b).symm)
  rw [G.limit.carrier.scalarCurvature_eq_of_coordinate_germ
    (G.limit.flow.metric (-1)) (G.limit.flow.connection (-1)) q (-1) p hp.1 g D hg] at hscalar
  apply hscalar.congr'
  filter_upwards [hgd, hev] with i hi hi'
  exact (G.embedding (k i)).scalarCurvature_eq_of_coordinate_germ
    (G.exhaustion_open (k i)) q (-1, y i) hi'.1 hi'.2 (gd i).1 (gd i).2 hi


theorem tendsto_scalarCurvature_at_points_neg_one
    (G : AncientCompactTimeConvergence S) (hcompact : CompactSpace G.limit.carrier.carrier)
    {α : Type*} {l : Filter α} [l.NeBot] (k : α → ℕ) (hk : Tendsto k l atTop)
    (x : α → G.limit.carrier.carrier) {p : G.limit.carrier.carrier}
    (hx : Tendsto x l (𝓝 p)) :
    Tendsto (fun i => ((S.rescaling (G.subsequence (k i))).flow.connection (-1)).scalarCurvature
      ((G.embedding (k i)).toFun (-1, x i)).2) l
      (𝓝 ((G.limit.flow.connection (-1)).scalarCurvature p)) := by
  obtain ⟨j, hj⟩ := (G.eventually_exhaustion_eq_univ hcompact).exists
  let c := extChartAt (𝓡 2) p
  have hp : c p ∈ c.target := c.map_source (mem_extChartAt_source p)
  obtain ⟨A, hA, hpA, hsub⟩ := exists_compact_subset (isOpen_extChartAt_target p) hp
  have hsub' : A ⊆ {y | y ∈ c.target ∧ c.symm y ∈ G.exhaustion j} := by
    intro y hy
    exact ⟨hsub hy, hj ▸ mem_univ _⟩
  have hc : Tendsto (fun i => c (x i)) l (𝓝 (c p)) :=
    (continuousAt_extChartAt p).tendsto.comp hx
  have h := G.tendsto_scalarCurvature_at_coordinate_points_neg_one p j hA hsub'
    (mem_interior_iff_mem_nhds.mp hpA) k hk (fun i => c (x i)) hc
  have hcp : c.symm (c p) = p := c.left_inv (mem_extChartAt_source p)
  rw [hcp] at h
  apply h.congr'
  filter_upwards [hx.eventually ((isOpen_extChartAt_source p).mem_nhds
    (mem_extChartAt_source (I := 𝓡 2) p))] with i hi
  rw [c.left_inv hi]


theorem tendstoUniformly_scalarCurvature_pullback_neg_one
    (G : AncientCompactTimeConvergence S) (hcompact : CompactSpace G.limit.carrier.carrier)
    {c : ℝ} (hround : ∀ x, (G.limit.flow.connection (-1)).scalarCurvature x = c) :
    TendstoUniformly
      (fun k x => ((S.rescaling (G.subsequence k)).flow.connection (-1)).scalarCurvature
        ((G.embedding k).toFun (-1, x)).2) (fun _ => c) atTop := by
  let : CompactSpace G.limit.carrier.carrier := hcompact
  apply tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro x
  apply Uniform.tendsto_nhds_right.mp
  simpa only [hround] using G.tendsto_scalarCurvature_at_points_neg_one hcompact
    (l := (atTop : Filter ℕ) ×ˢ 𝓝 x) Prod.fst tendsto_fst Prod.snd tendsto_snd


theorem tendstoUniformly_scalarCurvature_rescaling_neg_one
    (G : AncientCompactTimeConvergence S) (hcompact : CompactSpace G.limit.carrier.carrier)
    {c : ℝ} (hround : ∀ x, (G.limit.flow.connection (-1)).scalarCurvature x = c) :
    TendstoUniformly
      (fun k x => ((S.rescaling (G.subsequence k)).flow.connection (-1)).scalarCurvature x)
      (fun _ => c) atTop := by
  have h := G.tendstoUniformly_scalarCurvature_pullback_neg_one hcompact hround
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp h ε hε,
    G.eventually_exists_spatialDiffeomorph hcompact] with k hk hφ x
  obtain ⟨φ, hφ⟩ := hφ
  obtain ⟨y, rfl⟩ := φ.surjective x
  change dist c (((S.rescaling (G.subsequence k)).flow.connection (-1)).scalarCurvature
    (φ y)) < ε
  rw [hφ y]
  exact hk y

end PoincareConjecture.AncientCompactTimeConvergence
