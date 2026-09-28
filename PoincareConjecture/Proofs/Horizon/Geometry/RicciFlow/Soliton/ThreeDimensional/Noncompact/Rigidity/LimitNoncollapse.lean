import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.LimitLowerBound
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.CurvatureJets
import Mathlib.Topology.UniformSpace.UniformApproximation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.SourceNoncollapse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem ball_volume_lower_bound_at_radius_of_metricComplete_zero
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (v : ℝ) {R : ℝ} (hR : 0 < R)
    (hvolume : ∀ A : ℝ, 0 < A → A < R → ∀ᶠ k in atTop,
      ENNReal.ofReal (v * A ^ n) ≤
        (S.carrier (G.subsequence k)).metricRiemannianVolume
          ((S.flow (G.subsequence k)).metricAt 0)
          ((S.flow (G.subsequence k)).zeroBall A)) :
    ENNReal.ofReal (v * R ^ n) ≤
      G.limitCarrier.metricRiemannianVolume
        (G.limitFlow.metricAt 0) (G.limitFlow.zeroBall R) := by
  let V := G.limitCarrier.metricRiemannianVolume
    (G.limitFlow.metricAt 0) (G.limitFlow.zeroBall R)
  have hbound (C : ℝ) (hC : 1 < C) (hC2 : C < 2) :
      ENNReal.ofReal (v * (R / C) ^ n) ≤ ENNReal.ofReal C ^ n * V := by
    have hC0 := zero_lt_one.trans hC
    have hA : 0 < R / C := div_pos hR hC0
    have hAR : R / C < R := (div_lt_self hR hC)
    obtain ⟨k, hkvolume, hkbound⟩ :=
      ((hvolume (R / C) hA hAR).and
        (G.eventually_source_ball_volume_le_of_metricComplete_zero
          hT hcomplete hA hC hC2)).exists
    have heq : C * (R / C) = R := mul_div_cancel₀ R hC0.ne'
    exact hkvolume.trans (by simpa only [heq] using hkbound)
  have hleft : Tendsto (fun C : ℝ => ENNReal.ofReal (v * (R / C) ^ n))
      (𝓝[>] (1 : ℝ)) (𝓝 (ENNReal.ofReal (v * R ^ n))) := by
    have hreal : Tendsto (fun C : ℝ => v * (R / C) ^ n)
        (𝓝[>] (1 : ℝ)) (𝓝 (v * R ^ n)) := by
      have hid : Tendsto (fun C : ℝ => C) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [div_one, Pi.div_apply] using (tendsto_const_nhds (x := v)).mul
        (((tendsto_const_nhds (x := R)).div hid (one_ne_zero : (1 : ℝ) ≠ 0)).pow n)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hfactor : Tendsto (fun C : ℝ => ENNReal.ofReal C ^ n)
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_one, one_pow] using
      ENNReal.Tendsto.pow (n := n)
        ((ENNReal.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds)
  have hright : Tendsto (fun C : ℝ => ENNReal.ofReal C ^ n * V)
      (𝓝[>] (1 : ℝ)) (𝓝 V) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul hfactor (Or.inl one_ne_zero)
      tendsto_const_nhds (Or.inr ENNReal.one_ne_top)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds]
    with C hC hC2
  exact hbound C hC hC2

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

theorem ball_volume_lower_bound_of_eventually_controlled_source_balls
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (κ : ℝ) {R : ℝ} (hR : 0 < R)
    (hnoncollapse : ∀ᶠ k in atTop, ∀ A : ℝ, 0 < A →
      (∀ x ∈ (S.flow (G.subsequence k)).zeroBall A,
        |((S.flow (G.subsequence k)).flow.connection 0).curvatureTensorNorm x| ≤ A⁻¹ ^ 2) →
      ENNReal.ofReal (κ * A ^ n) ≤
        (S.carrier (G.subsequence k)).metricRiemannianVolume
          ((S.flow (G.subsequence k)).metricAt 0)
          ((S.flow (G.subsequence k)).zeroBall A))
    (hcurvature : ∀ A : ℝ, 0 < A → A < R → ∀ᶠ k in atTop,
      ∀ x ∈ (S.flow (G.subsequence k)).zeroBall A,
        |((S.flow (G.subsequence k)).flow.connection 0).curvatureTensorNorm x| ≤ A⁻¹ ^ 2) :
    ENNReal.ofReal (κ * R ^ n) ≤
      G.limitCarrier.metricRiemannianVolume
        (G.limitFlow.metricAt 0) (G.limitFlow.zeroBall R) := by
  apply G.ball_volume_lower_bound_at_radius_of_metricComplete_zero hT hcomplete κ hR
  intro A hA hAR
  filter_upwards [hnoncollapse, hcurvature A hA hAR] with k hk hbound
  exact hk A hA hbound

private theorem exists_coordinate_neighborhood
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    ∃ j, ∃ U : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsOpen U ∧ p ∈ U ∧
      ∀ z ∈ U, z.1 ∈ Ioo T' T ∧ z.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion j := by
  let c := extChartAt (𝓡 n) q
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    (isCompact_singleton (x := c.symm p.2))
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

private theorem eventually_coordinate_domain
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    ∀ᶠ z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) in atTop ×ˢ 𝓝 p,
      z.2.1 ∈ Ioo T' T ∧ z.2.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm z.2.2 ∈ G.exhaustion z.1 := by
  obtain ⟨j, U, hUo, hpU, hU⟩ := exists_coordinate_neighborhood G q p ht hp
  filter_upwards [(eventually_ge_atTop j).prod_mk (hUo.mem_nhds hpU)] with z hz
  exact ⟨(hU z.2 hz.2).1, (hU z.2 hz.2).2.1,
    G.exhaustion_monotone hz.1 (hU z.2 hz.2).2.2⟩

private theorem tendsto_coordinate_metricJet_prod
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier) (r : ℕ)
    (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦
      iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence z.1)) (G.embedding z.1))
        a b) z.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limitFlow.metricAt t).inner x v w) a b) p)) := by
  obtain ⟨j, U, hUo, hpU, hU⟩ := exists_coordinate_neighborhood G q p ht hp
  obtain ⟨C, hC, hpC, hCU⟩ := exists_compact_between isCompact_singleton hUo
    (singleton_subset_iff.mpr hpU)
  have hCn : C ∈ 𝓝 p := mem_of_superset
    (isOpen_interior.mem_nhds (hpC (mem_singleton p))) interior_subset
  have hunif : TendstoUniformlyOn
      (fun k ↦ iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) a b))
      (iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limitFlow.metricAt t).inner x v w) a b)) atTop C := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q j r C hC
      (fun z hz ↦ hU z (hCU hz)) ε hε
    exact (eventually_ge_atTop N).mono (fun k hk z hz ↦ by
      simpa only [dist_eq_norm, norm_sub_rev, MetricJet, FlowCarrier.metricInner]
        using hN k hk a b z hz)
  have hunif' : TendstoUniformlyOn
      (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
          (pullbackInnerValue G.limitFlow (S.flow (G.subsequence z.1)) (G.embedding z.1)) a b))
      (iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limitFlow.metricAt t).inner x v w) a b)) (atTop ×ˢ 𝓝 p) C :=
    fun V hV ↦ tendsto_fst.eventually (hunif V hV)
  apply hunif'.tendsto_comp
    ((G.limitFlow.contDiffAt_coordinateCoefficient_metric q a b p ht hp).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω))).continuousWithinAt
  rw [nhdsWithin_eq_nhds.mpr hCn]
  exact tendsto_snd

private theorem tendsto_coordinate_spatial_metricJet_prod
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier) (r : ℕ)
    (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦ iteratedFDeriv ℝ r
      (fun y ↦ G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence z.1)) (G.embedding z.1))
        a b (z.2.1, y)) z.2.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (iteratedFDeriv ℝ r (fun y ↦ G.limitCarrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limitFlow.metricAt t).inner x v w) a b (p.1, y)) p.2)) := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ) (fun _ : Fin r ↦
      ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n)))
  have h := P.continuous.continuousAt.tendsto.comp
    (tendsto_coordinate_metricJet_prod G q r a b p ht hp)
  have hlim : iteratedFDeriv ℝ r (fun y ↦ G.limitCarrier.coordinateCoefficient q
      (fun t x v w ↦ (G.limitFlow.metricAt t).inner x v w) a b (p.1, y)) p.2 =
      P (iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limitFlow.metricAt t).inner x v w) a b) p) := by
    ext v
    exact Poincare.Analysis.iteratedFDeriv_spatial_slice _
      (G.limitFlow.contDiffAt_coordinateCoefficient_metric q a b p ht hp) r v
  rw [← hlim] at h
  apply h.congr'
  filter_upwards [eventually_coordinate_domain G q p ht hp] with z hz
  ext v
  exact (Poincare.Analysis.iteratedFDeriv_spatial_slice _
    ((G.embedding z.1).contDiffAt_coordinateCoefficient_pullback
      (G.exhaustion_open z.1) q a b z.2 hz.1 hz.2) r v).symm

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem eventually_coordinate_pullback
    (G : PointedGeometricConvergence S) (k : ℕ) (q : G.limitCarrier.carrier)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm p.2 ∈ G.exhaustion k) :
    ∀ᶠ y in 𝓝 p.2,
      let φ := fun z ↦ ((G.embedding k).toFun (p.1, (extChartAt (𝓡 n) q).symm z)).2
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ φ y ∧
      Function.Injective (mfderiv (𝓡 n) (𝓡 n) φ y) ∧
      ∀ a b : Fin n, ((S.flow (G.subsequence k)).metricAt p.1).pullbackCoefficients φ y
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b) =
          G.limitCarrier.coordinateCoefficient q
            (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k))
            a b (p.1, y) := by
  let c := extChartAt (𝓡 n) q
  let f : G.limitCarrier.carrier → (S.carrier (G.subsequence k)).carrier :=
    fun y ↦ ((G.embedding k).toFun (p.1, y)).2
  let W := c.target ∩ c.symm ⁻¹' G.exhaustion k
  have hW : IsOpen W :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) (G.exhaustion_open k)
  apply Filter.Eventually.mono (hW.mem_nhds hp)
  intro y hy
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hy.1).contMDiffAt
      (extChartAt_target_mem_nhds' hy.1)
  have hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f (c.symm y) :=
    (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) ht hy.2
  have hd : mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y =
      (mfderiv (𝓡 n) (𝓡 n) f (c.symm y)).comp (mfderiv (𝓡 n) (𝓡 n) c.symm y) :=
    mfderiv_comp y (hf.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  refine ⟨hf.comp y hc, ?_, ?_⟩
  · change Function.Injective (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y)
    rw [hd]
    have hi : (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hy.1
    exact ((G.embedding k).spatialMap_mfderiv_bijective
      (G.exhaustion_open k) ht hy.2).1.comp hi.injective
  · intro a b
    change ((S.flow (G.subsequence k)).metricAt p.1).inner (f (c.symm y))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y (EuclideanSpace.basisFun (Fin n) ℝ a))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y (EuclideanSpace.basisFun (Fin n) ℝ b)) = _
    rw [hd]
    rfl

theorem tendsto_coordinate_curvatureTensorNorm_prod
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier)
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
  have hφ := (eventually_coordinate_domain G q p ht hp).mono fun z hz ↦
    eventually_coordinate_pullback G z.1 q z.2 hz.1 hz.2
  have hj (r : ℕ) (_hr : r ≤ 2) (a b : Fin n) :
      Tendsto (fun z : ℕ × (ℝ × EuclideanSpace ℝ (Fin n)) ↦ iteratedFDeriv ℝ r
        (fun y ↦ ((S.flow (G.subsequence z.1)).metricAt z.2.1).pullbackCoefficients
          (φ z) y (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b)) z.2.2)
        (atTop ×ˢ 𝓝 p) (𝓝 (iteratedFDeriv ℝ r (fun y ↦ g.inner y
          (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) p.2)) := by
    rw [G.limitCarrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
      q (fun _ x v w ↦ (G.limitFlow.metricAt p.1).inner x v w) p.1 p.2 g hg r a b]
    apply (tendsto_coordinate_spatial_metricJet_prod G q r a b p ht hp).congr'
    filter_upwards [hφ] with z hz
    have he : (fun y ↦ ((S.flow (G.subsequence z.1)).metricAt z.2.1).pullbackCoefficients
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

theorem tendsto_curvatureTensorNorm_prod
    (G : PointedGeometricConvergence S) (p : ℝ × G.limitCarrier.carrier)
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
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limitFlow.flow.connection p.1).curvatureTensorNorm
        (c.symm (c p.2)))) at hn
  rw [c.left_inv hx] at hn
  apply hn.congr'
  filter_upwards [tendsto_snd.eventually (continuousAt_snd.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := 𝓡 n) p.2))] with z hz
  rw [c.left_inv hz]

theorem eventually_curvatureTensorNorm_lt_on_compact
    (G : PointedGeometricConvergence S)
    {A : Set (ℝ × G.limitCarrier.carrier)} (hA : IsCompact A)
    (ht : ∀ p ∈ A, p.1 ∈ Ioo T' T) {B : ℝ}
    (hB : ∀ p ∈ A, (G.limitFlow.flow.connection p.1).curvatureTensorNorm p.2 < B) :
    ∀ᶠ k in atTop, ∀ p ∈ A,
      ((S.flow (G.subsequence k)).flow.connection p.1).curvatureTensorNorm
        ((G.embedding k).toFun p).2 < B := by
  classical
  have hlocal (p : A) : ∃ U ∈ 𝓝 p.val, ∀ᶠ k in atTop, ∀ z ∈ U,
      ((S.flow (G.subsequence k)).flow.connection z.1).curvatureTensorNorm
        ((G.embedding k).toFun z).2 < B := by
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp
      ((G.tendsto_curvatureTensorNorm_prod p.val (ht p.val p.property)).eventually
        (Iio_mem_nhds (hB p.val p.property)))
    exact ⟨{z | Q z}, hQ, hP.mono (fun k hk z hz ↦ hPQ hk hz)⟩
  choose U hU hb using hlocal
  obtain ⟨s, hs⟩ := hA.elim_nhds_subcover' (fun p hp ↦ U ⟨p, hp⟩)
    (fun p hp ↦ hU ⟨p, hp⟩)
  filter_upwards [s.eventually_all.mpr (fun p _ ↦ hb p)] with k hk p hp
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hs hp)
  exact hk q hq p hpq

attribute [local instance] FlowCarrier.t3Space

theorem eventually_source_ball_curvature_bound
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    {R : ℝ} (hR : 0 < R)
    (hbound : ∀ x ∈ G.limitFlow.zeroBall R,
      |(G.limitFlow.flow.connection 0).curvatureTensorNorm x| ≤ R⁻¹ ^ 2)
    {A : ℝ} (hA : 0 < A) (hAR : A < R) :
    ∀ᶠ k in atTop, ∀ x ∈ (S.flow (G.subsequence k)).zeroBall A,
      |((S.flow (G.subsequence k)).flow.connection 0).curvatureTensorNorm x| ≤ A⁻¹ ^ 2 := by
  obtain ⟨C, hC, hCmax⟩ := exists_between
    (lt_min (by norm_num : (1 : ℝ) < 2) ((one_lt_div hA).mpr hAR))
  have hC0 : 0 < C := zero_lt_one.trans hC
  have hCAR : C * A < R := (lt_div_iff₀ hA).mp (lt_min_iff.mp hCmax).2
  let gL := G.limitFlow.metricAt 0
  let pL := G.limitFlow.base
  let K := {x | gL.edist pL x ≤ ENNReal.ofReal (C * A)}
  have hK : IsCompact K := gL.isCompact_closedBall_of_metricComplete hcomplete pL (C * A)
  have hKR : K ⊆ G.limitFlow.zeroBall R := by
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hCAR)
  have hthreshold : R⁻¹ ^ 2 < A⁻¹ ^ 2 := by
    have hi : R⁻¹ < A⁻¹ := (inv_lt_inv₀ hR hA).mpr hAR
    nlinarith [inv_pos.mpr hR, inv_pos.mpr hA]
  have hcurv := G.eventually_curvatureTensorNorm_lt_on_compact
    (isCompact_singleton.prod hK) (fun z hz ↦ by
      rcases z with ⟨t, x⟩
      rcases hz with ⟨rfl, _⟩
      exact hT)
    (B := A⁻¹ ^ 2) (fun z hz ↦ by
      rcases z with ⟨t, x⟩
      rcases hz with ⟨rfl, hx⟩
      exact (le_abs_self _).trans_lt ((hbound x (hKR hx)).trans_lt hthreshold))
  have hcover := G.source_ball_coverage_of_metricComplete_zero hT hcomplete
  obtain ⟨j, hj⟩ := hcover A hA
  filter_upwards [hcurv, hj, eventually_ge_atTop j,
    G.eventually_inverse_edist_bounds_of_source_ball_coverage hT hcover hA hC
      (lt_min_iff.mp hCmax).1] with k hkcurv hkcover hjk hkdist
  let Q := S.carrier (G.subsequence k)
  let gS := (S.flow (G.subsequence k)).metricAt 0
  let pS := (S.flow (G.subsequence k)).base
  let f := fun z ↦ ((G.embedding k).toFun (0, z)).2
  let inv := fun z ↦ ((G.embedding k).inverse (0, z)).2
  have hleft (z : G.limitCarrier.carrier) (hz : z ∈ G.exhaustion k) : inv (f z) = z :=
    (G.embedding k).spatialInverse_comp_spatialMap hT hz
  have hbase : inv pS = pL := by
    rw [show pS = f pL from (congrArg Prod.snd (G.base_preserving k)).symm]
    exact hleft pL (G.base_in_exhaustion k)
  let : EMetricSpace Q.carrier := Q.metricEMetricSpace gS
  have hpS : pS ∈ (S.flow (G.subsequence k)).zeroBall A := by
    change edist pS pS < ENNReal.ofReal A
    simpa only [edist_self] using ENNReal.ofReal_pos.mpr hA
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hkcover hy
  have hdist := (hkdist pS hpS (f x) hy).1
  change gL.edist (inv pS) (inv (f x)) ≤ ENNReal.ofReal C * gS.edist pS (f x) at hdist
  rw [hbase, hleft x (G.exhaustion_monotone hjk hx)] at hdist
  have hxK : x ∈ K := by
    apply hdist.trans
    rw [ENNReal.ofReal_mul hC0.le]
    exact mul_le_mul_right (show gS.edist pS (f x) ≤ ENNReal.ofReal A from hy.le) _
  have h := hkcurv (0, x) ⟨rfl, hxK⟩
  have hn : 0 ≤ ((S.flow (G.subsequence k)).flow.connection 0).curvatureTensorNorm (f x) :=
    Real.sqrt_nonneg _
  rw [abs_of_nonneg hn]
  exact h.le

theorem ball_volume_lower_bound_of_source_noncollapse
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (κ : ℝ)
    (hnoncollapse : ∀ᶠ k in atTop, ∀ A : ℝ, 0 < A →
      (∀ x ∈ (S.flow (G.subsequence k)).zeroBall A,
        |((S.flow (G.subsequence k)).flow.connection 0).curvatureTensorNorm x| ≤ A⁻¹ ^ 2) →
      ENNReal.ofReal (κ * A ^ n) ≤
        (S.carrier (G.subsequence k)).metricRiemannianVolume
          ((S.flow (G.subsequence k)).metricAt 0)
          ((S.flow (G.subsequence k)).zeroBall A))
    {R : ℝ} (hR : 0 < R)
    (hbound : ∀ x ∈ G.limitFlow.zeroBall R,
      |(G.limitFlow.flow.connection 0).curvatureTensorNorm x| ≤ R⁻¹ ^ 2) :
    ENNReal.ofReal (κ * R ^ n) ≤
      G.limitCarrier.metricRiemannianVolume
        (G.limitFlow.metricAt 0) (G.limitFlow.zeroBall R) := by
  apply G.ball_volume_lower_bound_of_eventually_controlled_source_balls
    hT hcomplete κ hR hnoncollapse
  exact fun A hA hAR ↦ G.eventually_source_ball_curvature_bound hT hcomplete hR hbound hA hAR

end PoincareConjecture.PointedGeometricConvergence

namespace PoincareConjecture.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space

private def shiftedFlow {n : ℕ} {C : FlowCarrier.{0} n} {T : ℝ}
    (F : RicciFlow n C.carrier (Iio T)) (s : ℝ) :
    RicciFlow n C.carrier (Iio (T - s)) :=
  F.translate s (by
    rintro _ ⟨t, ht, rfl⟩
    change t < T - s at ht
    change t + s < T
    linarith)
    ordConnected_Iio ⟨T - s - 2, by simp, T - s - 1, by simp, by linarith⟩

private theorem coordinateCoefficient_time_shift {n : ℕ} (C : FlowCarrier n)
    (q : C.carrier) (B : ∀ _t : ℝ, ∀ x : C.carrier, C.tangent x → C.tangent x → ℝ)
    (a b : Fin n) (s : ℝ) :
    C.coordinateCoefficient q (fun t ↦ B (t + s)) a b =
      C.coordinateCoefficient q B a b ∘ (fun z ↦ z + (s, 0)) := by
  funext z
  change C.coordinateCoefficient q (fun t ↦ B (t + s)) a b z =
    C.coordinateCoefficient q B a b (z + (s, 0))
  have hz : z + (s, 0) = (z.1 + s, z.2) := Prod.ext rfl (add_zero _)
  rw [hz]
  rfl

def shiftTime {n : ℕ} {C : ℕ → FlowCarrier.{0} n}
    {g : ∀ k, ℝ → (C k).metric} {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C g p T) (s : ℝ) :
    AncientPointedGeometricConvergence C (fun k t ↦ g k (t + s)) p (T - s) where
  limitCarrier := G.limitCarrier
  limitFlow := shiftedFlow G.limitFlow s
  base := G.base
  subsequence := G.subsequence
  subsequence_strictMono := G.subsequence_strictMono
  exhaustion := G.exhaustion
  exhaustion_open := G.exhaustion_open
  exhaustion_connected := G.exhaustion_connected
  exhaustion_compactClosure := G.exhaustion_compactClosure
  exhaustion_increasing := G.exhaustion_increasing
  exhaustion_covers := G.exhaustion_covers
  embedding := G.embedding
  embedding_open := G.embedding_open
  embedding_smooth := G.embedding_smooth
  base_in_exhaustion := G.base_in_exhaustion
  base_preserving := G.base_preserving
  pullback_metric_converges := by
    intro j K I hK hKE hI hIT ε hε
    obtain ⟨N, hjN, hN⟩ := G.pullback_metric_converges j K
      ((fun t : ℝ ↦ t + s) '' I) hK hKE (hI.image (continuous_id.add continuous_const))
      (by
        rintro _ ⟨t, ht, rfl⟩
        have hh : t < T - s := hIT ht
        change t + s < T
        linarith) ε hε
    exact ⟨N, hjN, fun k hk t ht ↦ hN k hk (t + s) (mem_image_of_mem _ ht)⟩
  pullback_metric_CInfinity := by
    intro q j r K hK hKE ε hε
    let f := fun z : ℝ × EuclideanSpace ℝ (Fin n) ↦ z + (s, 0)
    have hdom : f '' K ⊆ {z | z.1 ∈ Iio T ∧
        z.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion j} := by
      rintro _ ⟨z, hz, rfl⟩
      have hh := hKE hz
      change z.1 + s ∈ Iio T ∧ z.2 + 0 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm (z.2 + 0) ∈ G.exhaustion j
      refine ⟨?_, by simpa only [add_zero] using hh.2⟩
      change z.1 + s < T
      have := hh.1
      change z.1 < T - s at this
      linarith
    obtain ⟨N, hjN, hN⟩ := G.pullback_metric_CInfinity q j r (f '' K)
      (hK.image (continuous_id.add continuous_const)) hdom ε hε
    refine ⟨N, hjN, fun k hk a b z hz ↦ ?_⟩
    have hh := hN k hk a b (f z) (mem_image_of_mem f hz)
    let ck := G.limitCarrier.coordinateCoefficient q
      (fun t x v w ↦ spatialPullbackInner G.limitCarrier (C (G.subsequence k))
        (g (G.subsequence k) t) (G.embedding k) x v w) a b
    let cl := G.limitCarrier.coordinateCoefficient q
      (fun t x v w ↦ G.limitCarrier.metricInner (G.limitFlow.metric t) x v w) a b
    change ‖iteratedFDeriv ℝ r
      (G.limitCarrier.coordinateCoefficient q
        (fun t ↦ (fun u x v w ↦ spatialPullbackInner G.limitCarrier (C (G.subsequence k))
          (g (G.subsequence k) u) (G.embedding k) x v w) (t + s)) a b) z -
      iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (fun t ↦ (fun u x v w ↦ G.limitCarrier.metricInner (G.limitFlow.metric u) x v w)
          (t + s)) a b) z‖ < ε
    rw [coordinateCoefficient_time_shift G.limitCarrier q
      (fun t x v w ↦ spatialPullbackInner G.limitCarrier (C (G.subsequence k))
        (g (G.subsequence k) t) (G.embedding k) x v w) a b s,
      coordinateCoefficient_time_shift G.limitCarrier q
        (fun t x v w ↦ G.limitCarrier.metricInner (G.limitFlow.metric t) x v w) a b s]
    change ‖iteratedFDeriv ℝ r (fun w ↦ ck (w + (s, 0))) z -
      iteratedFDeriv ℝ r (fun w ↦ cl (w + (s, 0))) z‖ < ε
    rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := ck) r (s, 0) z,
      iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := cl) r (s, 0) z]
    exact hh

def repoint {n : ℕ} {C : ℕ → FlowCarrier.{0} n}
    {g : ∀ k, ℝ → (C k).metric} {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C g p T)
    (x : G.limitCarrier.carrier) (N : ℕ) (hx : x ∈ G.exhaustion N) :
    AncientPointedGeometricConvergence (fun k ↦ C (G.subsequence (k + N)))
      (fun k ↦ g (G.subsequence (k + N))) (fun k ↦ G.embedding (k + N) x) T where
  limitCarrier := G.limitCarrier
  limitFlow := G.limitFlow
  base := x
  subsequence := id
  subsequence_strictMono := strictMono_id
  exhaustion := fun k ↦ G.exhaustion (k + N)
  exhaustion_open := fun k ↦ G.exhaustion_open (k + N)
  exhaustion_connected := fun k ↦ G.exhaustion_connected (k + N)
  exhaustion_compactClosure := fun k ↦ G.exhaustion_compactClosure (k + N)
  exhaustion_increasing := fun k ↦ by
    simpa only [Nat.add_right_comm k 1 N] using G.exhaustion_increasing (k + N)
  exhaustion_covers := by
    ext y
    constructor
    · exact fun _ ↦ mem_univ _
    · intro _
      have hy : y ∈ ⋃ k, G.exhaustion k := by rw [G.exhaustion_covers]; exact mem_univ _
      obtain ⟨k, hk⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨k, (monotone_nat_of_le_succ G.exhaustion_increasing)
        (by omega : k ≤ k + N) hk⟩
  embedding := fun k ↦ G.embedding (k + N)
  embedding_open := fun k ↦ G.embedding_open (k + N)
  embedding_smooth := fun k ↦ G.embedding_smooth (k + N)
  base_in_exhaustion := fun k ↦ (monotone_nat_of_le_succ G.exhaustion_increasing)
    (by omega : N ≤ k + N) hx
  base_preserving := fun _ ↦ rfl
  pullback_metric_converges := by
    intro j K I hK hKE hI hIT ε hε
    obtain ⟨l, hjl, hl⟩ := G.pullback_metric_converges (j + N) K I hK hKE hI hIT ε hε
    exact ⟨l, by omega, fun k hk ↦ hl (k + N) (by omega)⟩
  pullback_metric_CInfinity := by
    intro q j r K hK hKE ε hε
    obtain ⟨l, hjl, hl⟩ := G.pullback_metric_CInfinity q (j + N) r K hK hKE ε hε
    exact ⟨l, by omega, fun k hk ↦ hl (k + N) (by omega)⟩

theorem ball_volume_lower_bound_at_radius_of_ancient_source_bounds
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {J : ℕ → Set ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (J k)) {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
    (hT : 0 < T)
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (v : ℝ) {R : ℝ} (hR : 0 < R)
    (hvolume : ∀ r : ℝ, 0 < r → r < R → ∀ᶠ k in atTop,
      ENNReal.ofReal (v * r ^ n) ≤
        ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) r)) :
    ENNReal.ofReal (v * R ^ n) ≤
      (G.limitFlow.metric 0).volumeMeasure ((G.limitFlow.metric 0).ball G.base R) := by
  obtain ⟨a, b, ha, hb, hbT, _⟩ := exists_ancient_window_of_isCompact hT
    isCompact_singleton (singleton_subset_iff.mpr hT)
  obtain ⟨N, hN⟩ := exists_source_window_tail
    (G.subsequence_strictMono.tendsto_atTop.eventually (htime a b hbT))
  let W := G.window F (ha.trans hb) hbT.le N hN
  apply W.ball_volume_lower_bound_at_radius_of_metricComplete_zero
    ⟨ha, hb⟩ hcomplete v hR
  intro r hr hrR
  exact (G.subsequence_strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat N)).eventually
    (hvolume r hr hrR)

theorem ball_volume_lower_bound_of_ancient_source_noncollapse
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {T : ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (Iio T)) {p : ∀ k, (C k).carrier}
    (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
    (hT : 0 < T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (κ : ℝ)
    (hnoncollapse : ∀ k, ∀ r : ℝ, 0 < r →
      (∀ y ∈ ((F k).metric 0).ball (p k) r,
        |((F k).connection 0).curvatureTensorNorm y| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤
        ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) r))
    {R : ℝ} (hR : 0 < R)
    (hbound : ∀ y ∈ (G.limitFlow.metric 0).ball G.base R,
      |(G.limitFlow.connection 0).curvatureTensorNorm y| ≤ R⁻¹ ^ 2) :
    ENNReal.ofReal (κ * R ^ n) ≤
      (G.limitFlow.metric 0).volumeMeasure ((G.limitFlow.metric 0).ball G.base R) := by
  obtain ⟨a, b, ha, hb, hbT, _⟩ := exists_ancient_window_of_isCompact hT
    isCompact_singleton (singleton_subset_iff.mpr hT)
  have hsub : ∀ k : ℕ, Ioo a b ⊆ Iio T := fun _ _ ht ↦ ht.2.trans hbT
  let W := G.window F (ha.trans hb) hbT.le 0 hsub
  apply W.ball_volume_lower_bound_of_source_noncollapse ⟨ha, hb⟩ hcomplete κ
    (Eventually.of_forall fun k ↦ hnoncollapse (G.subsequence (k + 0))) hR hbound

theorem ball_volume_lower_bound_of_static_source_noncollapse
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {T : ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (Iio T)) {p : ∀ k, (C k).carrier}
    (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
    (t : ℝ) (ht : t < T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric t))
    (κ : ℝ)
    (hnoncollapse : ∀ k, ∀ x : (C k).carrier, ∀ r : ℝ, 0 < r →
      (∀ y ∈ ((F k).metric t).ball x r,
        |((F k).connection t).curvatureTensorNorm y| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤
        ((F k).metric t).volumeMeasure (((F k).metric t).ball x r)) :
    ∀ x : G.limitCarrier.carrier, ∀ r : ℝ, 0 < r →
      (∀ y ∈ (G.limitFlow.metric t).ball x r,
        |(G.limitFlow.connection t).curvatureTensorNorm y| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤
        (G.limitFlow.metric t).volumeMeasure ((G.limitFlow.metric t).ball x r) := by
  intro x r hr hbound
  have hx : x ∈ ⋃ j, G.exhaustion j := by rw [G.exhaustion_covers]; exact mem_univ _
  obtain ⟨N, hxN⟩ := mem_iUnion.mp hx
  let H := G.shiftTime t
  let H' := H.repoint x N hxN
  let F' := fun k ↦ shiftedFlow (F (G.subsequence (k + N))) t
  have hzS (k : ℕ) (y : (C k).carrier) :
      ((F k).connection (0 + t)).curvatureTensorNorm y =
        ((F k).connection t).curvatureTensorNorm y :=
    congrArg (fun s ↦ ((F k).connection s).curvatureTensorNorm y) (zero_add t)
  have hzL (y : G.limitCarrier.carrier) :
      (G.limitFlow.connection (0 + t)).curvatureTensorNorm y =
        (G.limitFlow.connection t).curvatureTensorNorm y :=
    congrArg (fun s ↦ (G.limitFlow.connection s).curvatureTensorNorm y) (zero_add t)
  have hvol := H'.ball_volume_lower_bound_of_ancient_source_noncollapse F'
    (by linarith : 0 < T - t)
    (by simpa only [H', H, repoint, shiftTime, shiftedFlow, RicciFlow.translate, zero_add]
      using hcomplete) κ
    (fun k ↦ by
      convert! hnoncollapse (G.subsequence (k + N)) (G.embedding (k + N) x) using 1
      simp only [F', H, shiftTime, shiftedFlow, RicciFlow.translate, hzS, zero_add]) hr
    (by
      convert! hbound using 1
      simp only [H', H, repoint, shiftTime, shiftedFlow, RicciFlow.translate, hzL, zero_add])
  simpa only [H', H, repoint, shiftTime, shiftedFlow, RicciFlow.translate, zero_add]
    using hvol

end PoincareConjecture.AncientPointedGeometricConvergence

universe u

namespace PoincareConjecture.RicciFlow.SpatialLineLimit

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold
  smallMeasurableSpace smallBorelSpace smallT3Space

variable {M : Type u} [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {F : RicciFlow 3 M (Iic 0)} {t₀ : ℝ} {p : M}

theorem metricKappaNoncollapsed (L : SpatialLineLimit F t₀ p) (ht₀ : t₀ < 0)
    {κ : ℝ}
    (hκ : ∀ t ≤ 0, MetricKappaNoncollapsed (F.metric t) (F.connection t) κ)
    (t : ℝ) (ht : t < L.buffer) :
    MetricKappaNoncollapsed (L.convergence.limitFlow.metric t)
      (L.convergence.limitFlow.connection t) κ := by
  let Q := fun i ↦ (F.connection t₀).scalarCurvature (L.centers i)
  let H := fun i ↦ F.interiorAncientRescaleAt (Q i) (L.scalar_pos i) t₀
  have htime (i : ℕ) (s : ℝ) (hs : s < L.buffer) : s - L.buffer < -t₀ * Q i := by
    have hpos := mul_pos (neg_pos.mpr ht₀) (L.scalar_pos i)
    change 0 < -t₀ * Q i at hpos
    linarith
  let C := fun _ : ℕ ↦ (FlowCarrier.ofConnectedManifold 3 M).shrink
  let F' : ∀ i, RicciFlow 3 (C i).carrier (Iio L.buffer) := fun i ↦
    (H i).shrink.translate (-L.buffer)
      (by rintro _ ⟨s, hs, rfl⟩; exact htime i s hs)
      ordConnected_Iio
      ⟨L.buffer - 2, by simp, L.buffer - 1, by simp, by linarith⟩
  refine ⟨(hκ 0 le_rfl).1, ?_⟩
  have hvol := L.convergence.ball_volume_lower_bound_of_static_source_noncollapse F'
    t ht (L.complete t ht) κ (fun i x r hr hbound ↦ by
      have hbase := F.interiorAncientRescaleAt_metricKappaNoncollapsed hκ
        (Q i) (L.scalar_pos i) t₀ (t - L.buffer) (htime i t ht)
      have hsmall := (H i).metricKappaNoncollapsed_shrink (t - L.buffer) hbase
      simpa only [F', C, FlowCarrier.shrink, FlowCarrier.ofConnectedManifold,
        RicciFlow.translate, sub_eq_add_neg, calibratedMetricVolume_eq_volumeMeasure]
        using hsmall.2 x r hr hbound)
  simpa only [calibratedMetricVolume_eq_volumeMeasure] using hvol

end PoincareConjecture.RicciFlow.SpatialLineLimit
