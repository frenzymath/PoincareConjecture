import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.CurvatureJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.MovingCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u
namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {tau : ℝ} {R : AncientRescaling K tau}

theorem AncientSpacetimeEmbedding.eventually_coordinate_pullback
    {L : AncientLimitFlow n} {J : Set ℝ} {U : Set L.carrier.carrier}
    (e : AncientSpacetimeEmbedding (R := R) L (J ×ˢ U)) (hU : IsOpen U)
    (q : L.carrier.carrier) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : J ∈ 𝓝 p.1)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target ∧ (extChartAt (𝓡 n) q).symm p.2 ∈ U) :
    ∀ᶠ y in 𝓝 p.2,
      let φ := fun z ↦ (e.toFun (p.1, (extChartAt (𝓡 n) q).symm z)).2
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ φ y ∧
      Function.Injective (mfderiv (𝓡 n) (𝓡 n) φ y) ∧
      ∀ a b : Fin n, (R.flow.metric p.1).pullbackCoefficients φ y
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b) =
          ancientPullbackCoefficient e q a b (p.1, y) := by
  let c := extChartAt (𝓡 n) q
  let f : L.carrier.carrier → M := fun y ↦ (e.toFun (p.1, y)).2
  let W := c.target ∩ c.symm ⁻¹' U
  have hW : IsOpen W :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) hU
  apply Filter.Eventually.mono (hW.mem_nhds hp)
  intro y hy
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hy.1).contMDiffAt
      (extChartAt_target_mem_nhds' hy.1)
  have hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f (c.symm y) :=
    e.spatialMap_contMDiffAt_of_time_nhds hU ht hy.2
  have hd : mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y =
      (mfderiv (𝓡 n) (𝓡 n) f (c.symm y)).comp (mfderiv (𝓡 n) (𝓡 n) c.symm y) :=
    mfderiv_comp y (hf.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  refine ⟨hf.comp y hc, ?_, ?_⟩
  · change Function.Injective (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y)
    rw [hd]
    have hi : (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hy.1
    exact (e.spatialMap_mfderiv_injective_of_time_nhds hU ht hy.2).comp hi.injective
  · intro a b
    change (R.flow.metric p.1).inner (f (c.symm y))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y (EuclideanSpace.basisFun (Fin n) ℝ a))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y (EuclideanSpace.basisFun (Fin n) ℝ b)) = _
    rw [hd]
    rfl

namespace AncientCompactTimeConvergence

variable {S : AncientRescalingSequence K} (G : AncientCompactTimeConvergence S)

theorem tendsto_coordinate_curvatureTensorNorm_prod (q : G.limit.carrier.carrier)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 < 0)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦
      ((S.rescaling (G.subsequence z.1)).flow.connection z.2.1).curvatureTensorNorm
        ((G.embedding z.1).toFun (z.2.1, (extChartAt (𝓡 n) q).symm z.2.2)).2)
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limit.flow.connection p.1).curvatureTensorNorm
        ((extChartAt (𝓡 n) q).symm p.2))) := by
  obtain ⟨g, D, V, hVo, hpV, _, heq⟩ := G.limit.carrier.exists_local_coordinate_realization
    (G.limit.flow.metric p.1) q p.1 p.2 hp
  have hg := Filter.Eventually.mono (hVo.mem_nhds hpV) heq
  let φ := fun (z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n))) y ↦
    ((G.embedding z.1).toFun (z.2.1, (extChartAt (𝓡 n) q).symm y)).2
  have hφ := (G.eventually_coordinate_domain q p ht hp).mono fun z hz ↦
    (G.embedding z.1).eventually_coordinate_pullback (G.exhaustion_open z.1) q z.2 hz.1 hz.2
  have hj (r : ℕ) (_hr : r ≤ 2) (a b : Fin n) :
      Tendsto (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦ iteratedFDeriv ℝ r
        (fun y ↦ ((S.rescaling (G.subsequence z.1)).flow.metric z.2.1).pullbackCoefficients
          (φ z) y (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b)) z.2.2)
        (atTop ×ˢ 𝓝 p) (𝓝 (iteratedFDeriv ℝ r (fun y ↦ g.inner y
          (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) p.2)) := by
    rw [G.limit.carrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
      q (fun _ x v w ↦ (G.limit.flow.metric p.1).inner x v w) p.1 p.2 g hg r a b]
    apply (G.tendsto_coordinate_spatial_metricJet_prod q r a b p ht hp).congr'
    filter_upwards [hφ] with z hz
    have he : (fun y ↦ ((S.rescaling (G.subsequence z.1)).flow.metric z.2.1).pullbackCoefficients
        (φ z) y (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) =ᶠ[𝓝 z.2.2]
        (fun y ↦ ancientPullbackCoefficient (G.embedding z.1) q a b (z.2.1, y)) :=
      hz.mono (fun y hy ↦ hy.2.2 a b)
    exact (he.iteratedFDeriv ℝ r).self_of_nhds.symm
  have hn := LeviCivitaData.tendsto_curvatureTensorNorm_of_moving_scalar_pullback_jets
    (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦
      (S.rescaling (G.subsequence z.1)).flow.connection z.2.1) φ D
    (fun z ↦ z.2.2) p.2 (hφ.mono fun _ hz ↦ hz.mono fun _ hy ↦ ⟨hy.1, hy.2.1⟩) hj
  rw [G.limit.carrier.curvatureTensorNorm_eq_of_coordinate_germ
    (G.limit.flow.metric p.1) (G.limit.flow.connection p.1) q p.1 p.2 hp g D hg] at hn
  exact hn

theorem tendsto_curvatureTensorNorm_prod (p : ℝ × G.limit.carrier.carrier)
    (ht : p.1 < 0) :
    Tendsto (fun z : ℕ × (ℝ × G.limit.carrier.carrier) ↦
      ((S.rescaling (G.subsequence z.1)).flow.connection z.2.1).curvatureTensorNorm
        ((G.embedding z.1).toFun z.2).2)
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limit.flow.connection p.1).curvatureTensorNorm p.2)) := by
  let c := extChartAt (𝓡 n) p.2
  have hx : p.2 ∈ c.source := mem_extChartAt_source p.2
  have hc : ContinuousAt (fun z : ℝ × G.limit.carrier.carrier ↦ (z.1, c z.2)) p :=
    continuousAt_fst.prodMk ((continuousAt_extChartAt p.2).comp continuousAt_snd)
  have hn := (G.tendsto_coordinate_curvatureTensorNorm_prod p.2
    (p.1, c p.2) ht (c.map_source hx)).comp (tendsto_id.prodMap hc.tendsto)
  change Tendsto (fun z : ℕ × (ℝ × G.limit.carrier.carrier) ↦
      ((S.rescaling (G.subsequence z.1)).flow.connection z.2.1).curvatureTensorNorm
        ((G.embedding z.1).toFun (z.2.1, c.symm (c z.2.2))).2)
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limit.flow.connection p.1).curvatureTensorNorm (c.symm (c p.2)))) at hn
  rw [c.left_inv hx] at hn
  apply hn.congr'
  filter_upwards [tendsto_snd.eventually (continuousAt_snd.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := 𝓡 n) p.2))] with z hz
  rw [c.left_inv hz]

theorem exists_local_curvatureTensorNorm_lt (p : ℝ × G.limit.carrier.carrier)
    (ht : p.1 < 0) {B : ℝ} (hB : (G.limit.flow.connection p.1).curvatureTensorNorm p.2 < B) :
    ∃ U ∈ 𝓝 p, ∀ᶠ k in atTop, ∀ z ∈ U,
      ((S.rescaling (G.subsequence k)).flow.connection z.1).curvatureTensorNorm
        ((G.embedding k).toFun z).2 < B := by
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp
    ((G.tendsto_curvatureTensorNorm_prod p ht).eventually (Iio_mem_nhds hB))
  exact ⟨{z | Q z}, hQ, hP.mono (fun k hk z hz ↦ hPQ hk hz)⟩

theorem eventually_curvatureTensorNorm_lt_on_compact
    {A : Set (ℝ × G.limit.carrier.carrier)} (hA : IsCompact A)
    (ht : ∀ p ∈ A, p.1 < 0) {B : ℝ}
    (hB : ∀ p ∈ A, (G.limit.flow.connection p.1).curvatureTensorNorm p.2 < B) :
    ∀ᶠ k in atTop, ∀ p ∈ A,
      ((S.rescaling (G.subsequence k)).flow.connection p.1).curvatureTensorNorm
        ((G.embedding k).toFun p).2 < B := by
  classical
  choose U hU hb using fun p : A ↦
    G.exists_local_curvatureTensorNorm_lt p.val (ht p.val p.property) (hB p.val p.property)
  obtain ⟨s, hs⟩ := hA.elim_nhds_subcover' (fun p hp ↦ U ⟨p, hp⟩)
    (fun p hp ↦ hU ⟨p, hp⟩)
  filter_upwards [s.eventually_all.mpr (fun p _ ↦ hb p)] with k hk p hp
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hs hp)
  exact hk q hq p hpq

end AncientCompactTimeConvergence
end PoincareConjecture
