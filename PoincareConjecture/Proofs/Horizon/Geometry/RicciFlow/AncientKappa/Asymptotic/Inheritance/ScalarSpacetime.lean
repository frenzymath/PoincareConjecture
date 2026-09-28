import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.ScalarJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.MovingCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Scalar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}


theorem tendsto_coordinate_scalarCurvature_prod (G : AncientCompactTimeConvergence S)
    (q : G.limit.carrier.carrier) (p : ℝ × EuclideanSpace ℝ (Fin n))
    (ht : p.1 < 0) (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) =>
      ((S.rescaling (G.subsequence z.1)).flow.connection z.2.1).scalarCurvature
        ((G.embedding z.1).toFun (z.2.1, (extChartAt (𝓡 n) q).symm z.2.2)).2)
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limit.flow.connection p.1).scalarCurvature
        ((extChartAt (𝓡 n) q).symm p.2))) := by
  classical
  obtain ⟨g, D, V, hVo, hpV, _, heq⟩ := G.limit.carrier.exists_local_coordinate_realization
    (G.limit.flow.metric p.1) q p.1 p.2 hp
  have hg := Filter.Eventually.mono (hVo.mem_nhds hpV) heq
  have hev := G.eventually_coordinate_domain q p ht hp
  have hreal : ∀ᶠ z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) in atTop ×ˢ 𝓝 p,
      ∃ gd : Σ g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)), LeviCivitaData g,
        ∀ᶠ y in 𝓝 z.2.2, ∀ a b : Fin n,
          gd.1.euclideanCoefficients y (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b) =
          ancientPullbackCoefficient (G.embedding z.1) q a b (z.2.1, y) := by
    filter_upwards [hev] with z hz
    obtain ⟨gi, Di, hi⟩ := (G.embedding z.1).exists_local_coordinate_realization
      (G.exhaustion_open z.1) q z.2 hz.1 hz.2
    exact ⟨⟨gi, Di⟩, hi⟩
  obtain ⟨gd, hgd⟩ := hreal.choice
  have hs := LeviCivitaData.tendsto_scalarCurvature_of_moving_scalar_metric_jets
    (fun z => (gd z).2) D (fun z => z.2.2) p.2
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (by
      intro r _ a b
      simp only [OrthonormalBasis.coe_toBasis]
      erw [G.limit.carrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        q _ p.1 p.2 g hg r a b]
      apply (G.tendsto_coordinate_spatial_metricJet_prod q r a b p ht hp).congr'
      filter_upwards [hgd] with z hz
      exact (G.limit.carrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        q (ancientPullbackInnerValue (G.embedding z.1)) z.2.1 z.2.2
        (gd z).1 hz r a b).symm)
  rw [G.limit.carrier.scalarCurvature_eq_of_coordinate_germ
    (G.limit.flow.metric p.1) (G.limit.flow.connection p.1) q p.1 p.2 hp g D hg] at hs
  apply hs.congr'
  filter_upwards [hgd, hev] with z hz hz'
  exact (G.embedding z.1).scalarCurvature_eq_of_coordinate_germ
    (G.exhaustion_open z.1) q z.2 hz'.1 hz'.2 (gd z).1 (gd z).2 hz



theorem tendsto_scalarCurvature_prod (G : AncientCompactTimeConvergence S)
    (p : ℝ × G.limit.carrier.carrier) (ht : p.1 < 0) :
    Tendsto (fun z : ℕ × (ℝ × G.limit.carrier.carrier) =>
      ((S.rescaling (G.subsequence z.1)).flow.connection z.2.1).scalarCurvature
        ((G.embedding z.1).toFun z.2).2)
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limit.flow.connection p.1).scalarCurvature p.2)) := by
  let c := extChartAt (𝓡 n) p.2
  have hx : p.2 ∈ c.source := mem_extChartAt_source p.2
  have hc : ContinuousAt (fun z : ℝ × G.limit.carrier.carrier => (z.1, c z.2)) p :=
    continuousAt_fst.prodMk ((continuousAt_extChartAt p.2).comp continuousAt_snd)
  have hs := (G.tendsto_coordinate_scalarCurvature_prod p.2
    (p.1, c p.2) ht (c.map_source hx)).comp (tendsto_id.prodMap hc.tendsto)
  change Tendsto (fun z : ℕ × (ℝ × G.limit.carrier.carrier) =>
      ((S.rescaling (G.subsequence z.1)).flow.connection z.2.1).scalarCurvature
        ((G.embedding z.1).toFun (z.2.1, c.symm (c z.2.2))).2)
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limit.flow.connection p.1).scalarCurvature (c.symm (c p.2)))) at hs
  rw [c.left_inv hx] at hs
  apply hs.congr'
  filter_upwards [tendsto_snd.eventually (continuousAt_snd.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := 𝓡 n) p.2))] with z hz
  rw [c.left_inv hz]



theorem exists_local_scalarCurvature_lt (G : AncientCompactTimeConvergence S)
    (p : ℝ × G.limit.carrier.carrier) (ht : p.1 < 0) {B : ℝ}
    (hB : (G.limit.flow.connection p.1).scalarCurvature p.2 < B) :
    ∃ U ∈ 𝓝 p, ∀ᶠ k in atTop, ∀ z ∈ U,
      ((S.rescaling (G.subsequence k)).flow.connection z.1).scalarCurvature
        ((G.embedding k).toFun z).2 < B := by
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp
    ((G.tendsto_scalarCurvature_prod p ht).eventually (Iio_mem_nhds hB))
  exact ⟨{z | Q z}, hQ, hP.mono (fun k hk z hz => hPQ hk hz)⟩



theorem eventually_scalarCurvature_lt_on_compact (G : AncientCompactTimeConvergence S)
    {A : Set (ℝ × G.limit.carrier.carrier)} (hA : IsCompact A)
    (ht : ∀ p ∈ A, p.1 < 0) {B : ℝ}
    (hB : ∀ p ∈ A, (G.limit.flow.connection p.1).scalarCurvature p.2 < B) :
    ∀ᶠ k in atTop, ∀ p ∈ A,
      ((S.rescaling (G.subsequence k)).flow.connection p.1).scalarCurvature
        ((G.embedding k).toFun p).2 < B := by
  classical
  choose U hU hb using fun p : A =>
    G.exists_local_scalarCurvature_lt p.val (ht p.val p.property) (hB p.val p.property)
  obtain ⟨s, hs⟩ := hA.elim_nhds_subcover' (fun p hp => U ⟨p, hp⟩)
    (fun p hp => hU ⟨p, hp⟩)
  filter_upwards [s.eventually_all.mpr (fun p _ => hb p)] with k hk p hp
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hs hp)
  exact hk q hq p hpq

end PoincareConjecture.AncientCompactTimeConvergence
