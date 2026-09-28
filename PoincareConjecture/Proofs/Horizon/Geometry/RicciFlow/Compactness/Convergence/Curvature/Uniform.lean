import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Curvature.MovingJets
import Mathlib.Topology.UniformSpace.UniformApproximation












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem SmoothSpacetimeEmbedding.eventually_coordinate_pullback
    {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
    {F : BasedFlow n T' T C} {G : BasedFlow n T' T D} {U : Set C.carrier}
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U)) (hU : IsOpen U)
    (q : C.carrier) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target ∧ (extChartAt (𝓡 n) q).symm p.2 ∈ U) :
    ∀ᶠ y in 𝓝 p.2,
      let φ := fun z ↦ (e.toFun (p.1, (extChartAt (𝓡 n) q).symm z)).2
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ φ y ∧
      Function.Injective (mfderiv (𝓡 n) (𝓡 n) φ y) ∧
      ∀ a b : Fin n, (G.flow.metric p.1).pullbackCoefficients φ y
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b) =
          C.coordinateCoefficient q (pullbackInnerValue F G e) a b (p.1, y) := by
  let c := extChartAt (𝓡 n) q
  let f : C.carrier → D.carrier := fun y ↦ (e.toFun (p.1, y)).2
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
    e.spatialMap_contMDiffAt hU ht hy.2
  have hd : mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y =
      (mfderiv (𝓡 n) (𝓡 n) f (c.symm y)).comp (mfderiv (𝓡 n) (𝓡 n) c.symm y) :=
    mfderiv_comp y (hf.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  refine ⟨hf.comp y hc, ?_, ?_⟩
  · change Function.Injective (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y)
    rw [hd]
    have hi : (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hy.1
    exact (e.spatialMap_mfderiv_injective hU ht hy.2).comp hi.injective
  · intro a b
    change (G.flow.metric p.1).inner (f (c.symm y))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y (EuclideanSpace.basisFun (Fin n) ℝ a))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y (EuclideanSpace.basisFun (Fin n) ℝ b)) = _
    rw [hd]
    rfl

namespace PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
  (G : PointedGeometricConvergence S)

private theorem exists_coordinate_neighborhood (q : G.limitCarrier.carrier)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    ∃ j, ∃ U : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsOpen U ∧ p ∈ U ∧
      ∀ z ∈ U, z.1 ∈ Ioo T' T ∧
        z.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion j := by
  let c := extChartAt (𝓡 n) q
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (isCompact_singleton (x := c.symm p.2))
  have hc : ContinuousAt c.symm p.2 :=
    ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hp).contMDiffAt
      (extChartAt_target_mem_nhds' hp)).continuousAt
  have hU : ∀ᶠ z : ℝ × EuclideanSpace ℝ (Fin n) in 𝓝 p,
      z.1 ∈ Ioo T' T ∧ z.2 ∈ c.target ∧ c.symm z.2 ∈ G.exhaustion j :=
    inter_mem (continuousAt_fst.preimage_mem_nhds (isOpen_Ioo.mem_nhds ht))
      (inter_mem (continuousAt_snd.preimage_mem_nhds (extChartAt_target_mem_nhds' hp))
        ((hc.comp continuousAt_snd).preimage_mem_nhds
          ((G.exhaustion_open j).mem_nhds (hj (mem_singleton _)))))
  obtain ⟨U, hUsub, hUo, hpU⟩ := mem_nhds_iff.mp hU
  exact ⟨j, U, hUo, hpU, hUsub⟩

private theorem eventually_coordinate_domain (q : G.limitCarrier.carrier)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    ∀ᶠ z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) in atTop ×ˢ 𝓝 p,
      z.2.1 ∈ Ioo T' T ∧ z.2.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm z.2.2 ∈ G.exhaustion z.1 := by
  obtain ⟨j, U, hUo, hpU, hU⟩ := G.exists_coordinate_neighborhood q p ht hp
  filter_upwards [(eventually_ge_atTop j).prod_mk (hUo.mem_nhds hpU)] with z hz
  exact ⟨(hU z.2 hz.2).1, (hU z.2 hz.2).2.1,
    G.exhaustion_monotone hz.1 (hU z.2 hz.2).2.2⟩

private theorem tendsto_coordinate_metricJet_prod (q : G.limitCarrier.carrier) (r : ℕ)
    (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦
      iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence z.1)) (G.embedding z.1)) a b) z.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limitFlow.flow.metric t).inner x v w) a b) p)) := by
  obtain ⟨j, U, hUo, hpU, hU⟩ := G.exists_coordinate_neighborhood q p ht hp
  obtain ⟨C, hC, hpC, hCU⟩ := exists_compact_between isCompact_singleton hUo
    (singleton_subset_iff.mpr hpU)
  have hCn : C ∈ 𝓝 p := mem_of_superset
    (isOpen_interior.mem_nhds (hpC (mem_singleton p))) interior_subset
  have hdom : C ⊆ {z | z.1 ∈ Ioo T' T ∧
      z.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion j} := fun z hz ↦ hU z (hCU hz)
  have hunif : TendstoUniformlyOn
      (fun k ↦ iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) a b))
      (iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limitFlow.flow.metric t).inner x v w) a b)) atTop C := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q j r C hC hdom ε hε
    exact (eventually_ge_atTop N).mono (fun k hk z hz ↦ by
      simpa only [dist_eq_norm, norm_sub_rev, MetricJet, FlowCarrier.metricInner,
        BasedFlow.metricAt] using hN k hk a b z hz)
  have hunif' : TendstoUniformlyOn
      (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
          (pullbackInnerValue G.limitFlow (S.flow (G.subsequence z.1)) (G.embedding z.1)) a b))
      (iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limitFlow.flow.metric t).inner x v w) a b)) (atTop ×ˢ 𝓝 p) C :=
    fun V hV ↦ tendsto_fst.eventually (hunif V hV)
  apply hunif'.tendsto_comp
    ((G.limitFlow.contDiffAt_coordinateCoefficient_metric q a b p ht hp).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top : (r : ℕ∞ω) ≤ ∞)).continuousWithinAt
  rw [nhdsWithin_eq_nhds.mpr hCn]
  exact tendsto_snd

private theorem tendsto_coordinate_spatial_metricJet_prod (q : G.limitCarrier.carrier) (r : ℕ)
    (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦ iteratedFDeriv ℝ r
      (fun y ↦ G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence z.1)) (G.embedding z.1)) a b
          (z.2.1, y)) z.2.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (iteratedFDeriv ℝ r (fun y ↦ G.limitCarrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limitFlow.flow.metric t).inner x v w) a b (p.1, y)) p.2)) := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ) (fun _ : Fin r ↦
      ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n)))
  have h := P.continuous.continuousAt.tendsto.comp
    (G.tendsto_coordinate_metricJet_prod q r a b p ht hp)
  have hlim : iteratedFDeriv ℝ r (fun y ↦ G.limitCarrier.coordinateCoefficient q
      (fun t x v w ↦ (G.limitFlow.flow.metric t).inner x v w) a b (p.1, y)) p.2 =
      P (iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limitFlow.flow.metric t).inner x v w) a b) p) := by
    ext v
    exact Poincare.Analysis.iteratedFDeriv_spatial_slice _
      (G.limitFlow.contDiffAt_coordinateCoefficient_metric q a b p ht hp) r v
  rw [← hlim] at h
  apply h.congr'
  filter_upwards [G.eventually_coordinate_domain q p ht hp] with z hz
  ext v
  exact (Poincare.Analysis.iteratedFDeriv_spatial_slice _
    ((G.embedding z.1).contDiffAt_coordinateCoefficient_pullback (G.exhaustion_open z.1)
      q a b z.2 hz.1 hz.2) r v).symm

private theorem tendsto_coordinate_curvatureTensorNorm_prod (q : G.limitCarrier.carrier)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦
      ((S.flow (G.subsequence z.1)).flow.connection z.2.1).curvatureTensorNorm
        ((G.embedding z.1).toFun (z.2.1, (extChartAt (𝓡 n) q).symm z.2.2)).2)
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limitFlow.flow.connection p.1).curvatureTensorNorm
        ((extChartAt (𝓡 n) q).symm p.2))) := by
  obtain ⟨g, D, V, hVo, hpV, _, heq⟩ := G.limitCarrier.exists_local_coordinate_realization
    (G.limitFlow.metricAt p.1) q p.1 p.2 hp
  have hg := Filter.Eventually.mono (hVo.mem_nhds hpV) heq
  let φ := fun (z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n))) y ↦
    ((G.embedding z.1).toFun (z.2.1, (extChartAt (𝓡 n) q).symm y)).2
  have hφ := (G.eventually_coordinate_domain q p ht hp).mono fun z hz ↦
    (G.embedding z.1).eventually_coordinate_pullback (G.exhaustion_open z.1) q z.2 hz.1 hz.2
  have hj (r : ℕ) (_hr : r ≤ 2) (a b : Fin n) :
      Tendsto (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦ iteratedFDeriv ℝ r
        (fun y ↦ ((S.flow (G.subsequence z.1)).flow.metric z.2.1).pullbackCoefficients
          (φ z) y (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b)) z.2.2)
        (atTop ×ˢ 𝓝 p) (𝓝 (iteratedFDeriv ℝ r (fun y ↦ g.inner y
          (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) p.2)) := by
    rw [G.limitCarrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
      q (fun _ x v w ↦ (G.limitFlow.flow.metric p.1).inner x v w) p.1 p.2 g hg r a b]
    apply (G.tendsto_coordinate_spatial_metricJet_prod q r a b p ht hp).congr'
    filter_upwards [hφ] with z hz
    have he : (fun y ↦ ((S.flow (G.subsequence z.1)).flow.metric z.2.1).pullbackCoefficients
        (φ z) y (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) =ᶠ[𝓝 z.2.2]
        (fun y ↦ G.limitCarrier.coordinateCoefficient q
          (pullbackInnerValue G.limitFlow (S.flow (G.subsequence z.1)) (G.embedding z.1))
            a b (z.2.1, y)) := hz.mono (fun y hy ↦ hy.2.2 a b)
    exact (he.iteratedFDeriv ℝ r).self_of_nhds.symm
  have hn := LeviCivitaData.tendsto_curvatureTensorNorm_of_moving_scalar_pullback_jets
    (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦
      (S.flow (G.subsequence z.1)).flow.connection z.2.1) φ D
    (fun z ↦ z.2.2) p.2 (hφ.mono fun _ hz ↦ hz.mono fun _ hy ↦ ⟨hy.1, hy.2.1⟩) hj
  rw [G.limitCarrier.curvatureTensorNorm_eq_of_coordinate_germ
    (G.limitFlow.metricAt p.1) (G.limitFlow.flow.connection p.1) q p.1 p.2 hp g D hg] at hn
  exact hn



theorem tendsto_curvatureTensorNorm_prod (p : ℝ × G.limitCarrier.carrier)
    (ht : p.1 ∈ Ioo T' T) :
    Tendsto (fun z : ℕ × (ℝ × G.limitCarrier.carrier) ↦
      ((S.flow (G.subsequence z.1)).flow.connection z.2.1).curvatureTensorNorm
        ((G.embedding z.1).toFun z.2).2)
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limitFlow.flow.connection p.1).curvatureTensorNorm p.2)) := by
  let c := extChartAt (𝓡 n) p.2
  have hx : p.2 ∈ c.source := mem_extChartAt_source p.2
  have hc : ContinuousAt (fun z : ℝ × G.limitCarrier.carrier ↦ (z.1, c z.2)) p :=
    continuousAt_fst.prodMk ((continuousAt_extChartAt p.2).comp continuousAt_snd)
  have hn := (G.tendsto_coordinate_curvatureTensorNorm_prod p.2
    (p.1, c p.2) ht (c.map_source hx)).comp (tendsto_id.prodMap hc.tendsto)
  change Tendsto (fun z : ℕ × (ℝ × G.limitCarrier.carrier) ↦
      ((S.flow (G.subsequence z.1)).flow.connection z.2.1).curvatureTensorNorm
        ((G.embedding z.1).toFun (z.2.1, c.symm (c z.2.2))).2)
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limitFlow.flow.connection p.1).curvatureTensorNorm (c.symm (c p.2)))) at hn
  rw [c.left_inv hx] at hn
  apply hn.congr'
  filter_upwards [tendsto_snd.eventually (continuousAt_snd.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := 𝓡 n) p.2))] with z hz
  rw [c.left_inv hz]

private theorem exists_local_curvatureTensorNorm_lt (p : ℝ × G.limitCarrier.carrier)
    (ht : p.1 ∈ Ioo T' T) {B : ℝ}
    (hB : (G.limitFlow.flow.connection p.1).curvatureTensorNorm p.2 < B) :
    ∃ U ∈ 𝓝 p, ∀ᶠ k in atTop, ∀ z ∈ U,
      ((S.flow (G.subsequence k)).flow.connection z.1).curvatureTensorNorm
        ((G.embedding k).toFun z).2 < B := by
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp
    ((G.tendsto_curvatureTensorNorm_prod p ht).eventually (Iio_mem_nhds hB))
  exact ⟨{z | Q z}, hQ, hP.mono (fun k hk z hz ↦ hPQ hk hz)⟩



theorem eventually_curvatureTensorNorm_lt_on_compact
    {A : Set (ℝ × G.limitCarrier.carrier)} (hA : IsCompact A)
    (ht : ∀ p ∈ A, p.1 ∈ Ioo T' T) {B : ℝ}
    (hB : ∀ p ∈ A, (G.limitFlow.flow.connection p.1).curvatureTensorNorm p.2 < B) :
    ∀ᶠ k in atTop, ∀ p ∈ A,
      ((S.flow (G.subsequence k)).flow.connection p.1).curvatureTensorNorm
        ((G.embedding k).toFun p).2 < B := by
  classical
  choose U hU hb using fun p : A ↦
    G.exists_local_curvatureTensorNorm_lt p.val (ht p.val p.property) (hB p.val p.property)
  obtain ⟨s, hs⟩ := hA.elim_nhds_subcover' (fun p hp ↦ U ⟨p, hp⟩)
    (fun p hp ↦ hU ⟨p, hp⟩)
  filter_upwards [s.eventually_all.mpr (fun p _ ↦ hb p)] with k hk p hp
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hs hp)
  exact hk q hq p hpq

end PointedGeometricConvergence
end PoincareConjecture
