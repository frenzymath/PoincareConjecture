import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.LocalRealization








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

namespace AncientSpacetimeEmbedding

variable {L : AncientLimitFlow n} {J : Set ℝ} {U : Set L.carrier.carrier}

theorem spatialMap_contMDiffAt_of_time_nhds (e : AncientSpacetimeEmbedding (R := R) L (J ×ˢ U))
    (hU : IsOpen U) {t : ℝ} (ht : J ∈ 𝓝 t) {x : L.carrier.carrier} (hx : x ∈ U) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun y ↦ (e.toFun (t, y)).2) x := by
  exact ((e.smooth_on.contMDiffAt (prod_mem_nhds ht (hU.mem_nhds hx))).comp x
    (contMDiffAt_const.prodMk contMDiffAt_id)).snd

theorem spatialMap_mfderiv_injective_of_time_nhds
    (e : AncientSpacetimeEmbedding (R := R) L (J ×ˢ U))
    (hU : IsOpen U) {t : ℝ} (ht : J ∈ 𝓝 t) {x : L.carrier.carrier} (hx : x ∈ U) :
    Function.Injective (mfderiv (𝓡 n) (𝓡 n) (fun y ↦ (e.toFun (t, y)).2) x) := by
  let f : L.carrier.carrier → M := fun y ↦ (e.toFun (t, y)).2
  let g : M → L.carrier.carrier := fun y ↦ (e.inverse (t, y)).2
  have hpair (y : L.carrier.carrier) : e.toFun (t, y) = (t, f y) :=
    Prod.ext (e.time_preserving t y) rfl
  have hmaps : MapsTo (fun y : M ↦ (t, y)) (f '' U) (e.toFun '' (J ×ˢ U)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(t, y), ⟨mem_of_mem_nhds ht, hy⟩, hpair y⟩
  have hinv : ContMDiffWithinAt (𝓡 n) (𝓡 n) ∞ g (f '' U) (f x) := by
    exact ((e.smooth_inverse_on (t, f x) (hmaps ⟨x, hx, rfl⟩)).comp (f x)
      (contMDiffWithinAt_const.prodMk contMDiffWithinAt_id) hmaps).snd
  have hleft : ∀ y ∈ U, (g ∘ f) y = id y := by
    intro y hy
    have h := congrArg Prod.snd (e.left_inverse (t, y) ⟨mem_of_mem_nhds ht, hy⟩)
    simpa only [hpair, Function.comp_apply, id_eq, g] using h
  have hf : MDifferentiableAt (𝓡 n) (𝓡 n) f x :=
    (e.spatialMap_contMDiffAt_of_time_nhds hU ht hx).mdifferentiableAt (by simp)
  have hu : UniqueMDiffWithinAt (𝓡 n) U x := hU.uniqueMDiffWithinAt hx
  have hcomp := mfderivWithin_comp x (hinv.mdifferentiableWithinAt (by simp))
    hf.mdifferentiableWithinAt (fun y hy ↦ ⟨y, hy, rfl⟩) hu
  rw [mfderivWithin_congr_of_mem hleft hx, mfderivWithin_id hu,
    mfderivWithin_eq_mfderiv hu hf] at hcomp
  intro v w hvw
  have h := congrArg (mfderivWithin (𝓡 n) (𝓡 n) g (f '' U) (f x)) hvw
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← hcomp] at h
  exact h

theorem contDiffAt_coordinateCoefficient
    (e : AncientSpacetimeEmbedding (R := R) L (J ×ˢ U))
    (hU : IsOpen U) (q : L.carrier.carrier) (a b : Fin n)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : J ∈ 𝓝 p.1) (ht0 : p.1 < 0)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm p.2 ∈ U) :
    ContDiffAt ℝ ∞ (ancientPullbackCoefficient e q a b) p := by
  let c := extChartAt (𝓡 n) q
  let f : ℝ × EuclideanSpace ℝ (Fin n) → M := fun z ↦ (e.toFun (z.1, c.symm z.2)).2
  have hc {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hf {z : ℝ × EuclideanSpace ℝ (Fin n)}
      (hz : J ∈ 𝓝 z.1 ∧ z.2 ∈ c.target ∧ c.symm z.2 ∈ U) :
      ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ f z := by
    exact ((e.smooth_on.contMDiffAt (prod_mem_nhds hz.1 (hU.mem_nhds hz.2.2))).comp z
      (contDiffAt_fst.contMDiffAt.prodMk
        ((hc hz.2.1).comp z contDiffAt_snd.contMDiffAt))).snd
  have hd {z : ℝ × EuclideanSpace ℝ (Fin n)}
      (hz : J ∈ 𝓝 z.1 ∧ z.2 ∈ c.target ∧ c.symm z.2 ∈ U)
      (v : EuclideanSpace ℝ (Fin n)) :
      mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) f z (0, v) =
        mfderiv (𝓡 n) (𝓡 n) (fun x ↦ (e.toFun (z.1, x)).2) (c.symm z.2)
          (mfderiv (𝓡 n) (𝓡 n) c.symm z.2 v) := by
    rw [← RiemannianMetric.mfderiv_slice_apply ((hf hz).mdifferentiableAt (by simp))]
    exact congrArg (fun A ↦ A v) (mfderiv_comp z.2
      ((e.spatialMap_contMDiffAt_of_time_nhds hU hz.1 hz.2.2).mdifferentiableAt (by simp))
      ((hc hz.2.1).mdifferentiableAt (by simp)))
  have hnhds : ∀ᶠ z : ℝ × EuclideanSpace ℝ (Fin n) in 𝓝 p,
      J ∈ 𝓝 z.1 ∧ z.2 ∈ c.target ∧ c.symm z.2 ∈ U := by
    have h₁ := continuousAt_fst.preimage_mem_nhds (eventually_mem_nhds_iff.mpr ht)
    have h₂ := continuousAt_snd.preimage_mem_nhds (extChartAt_target_mem_nhds' hp.1)
    have h₃ := ((hc hp.1).continuousAt.comp continuousAt_snd).preimage_mem_nhds
      (hU.mem_nhds hp.2)
    exact inter_mem h₁ (inter_mem h₂ h₃)
  apply (R.flow.contDiffAt_family_pullback_inner (Iio_mem_nhds ht0)
    (hf ⟨ht, hp⟩) (0, EuclideanSpace.basisFun (Fin n) ℝ a)
      (0, EuclideanSpace.basisFun (Fin n) ℝ b)).congr_of_eventuallyEq
  filter_upwards [hnhds] with z hz
  dsimp [ancientPullbackCoefficient, ancientPullbackInnerValue]
  rw [hd hz, hd hz]
  rfl

theorem exists_local_coordinate_realization
    (e : AncientSpacetimeEmbedding (R := R) L (J ×ˢ U))
    (hU : IsOpen U) (q : L.carrier.carrier)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : J ∈ 𝓝 p.1)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm p.2 ∈ U) :
    ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (_D : LeviCivitaData g),
      ∀ᶠ y in 𝓝 p.2, ∀ a b : Fin n,
        g.euclideanCoefficients y (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b) = ancientPullbackCoefficient e q a b (p.1, y) := by
  let c := extChartAt (𝓡 n) q
  let f : L.carrier.carrier → M := fun y ↦ (e.toFun (p.1, y)).2
  let W := c.target ∩ c.symm ⁻¹' U
  have hW : IsOpen W :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) hU
  have hc (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm x :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx.1).contMDiffAt
      (extChartAt_target_mem_nhds' hx.1)
  have hf (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ f (c.symm x) :=
    e.spatialMap_contMDiffAt_of_time_nhds hU ht hx.2
  have hd (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) :
      mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x =
        (mfderiv (𝓡 n) (𝓡 n) f (c.symm x)).comp
          (mfderiv (𝓡 n) (𝓡 n) c.symm x) :=
    mfderiv_comp x ((hf x hx).mdifferentiableAt (by simp))
      ((hc x hx).mdifferentiableAt (by simp))
  have hi (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) :
      Function.Injective (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x) := by
    rw [hd x hx]
    have hchart : (mfderiv (𝓡 n) (𝓡 n) c.symm x).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hx.1
    exact (e.spatialMap_mfderiv_injective_of_time_nhds hU ht hx.2).comp hchart.injective
  have hsmooth : ContDiffOn ℝ ∞
      ((R.flow.metric p.1).pullbackCoefficients (f ∘ c.symm)) W := by
    intro x hx
    exact ((R.flow.metric p.1).contDiffAt_pullbackCoefficients
      ((hf x hx).comp x (hc x hx))).contDiffWithinAt
  have hsymm : ∀ x ∈ W, ∀ v w,
      (R.flow.metric p.1).pullbackCoefficients (f ∘ c.symm) x v w =
        (R.flow.metric p.1).pullbackCoefficients (f ∘ c.symm) x w v := by
    intro x hx v w
    exact (R.flow.metric p.1).symm _ _ _
  have hpos : ∀ x ∈ W, ∀ v, v ≠ 0 →
      0 < (R.flow.metric p.1).pullbackCoefficients (f ∘ c.symm) x v v := by
    intro x hx v hv
    change 0 < (R.flow.metric p.1).inner (f (c.symm x))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x v)
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x v)
    apply (R.flow.metric p.1).pos (f (c.symm x))
    intro hz
    apply hv
    apply hi x hx
    simpa only [map_zero] using hz
  obtain ⟨g, D, V, hVo, hpV, hV, heq⟩ :=
    RiemannianMetric.exists_local_realization hW hp
      ((R.flow.metric p.1).pullbackCoefficients (f ∘ c.symm)) hsmooth hsymm hpos
  refine ⟨g, D, Filter.Eventually.mono (hVo.mem_nhds hpV) ?_⟩
  intro x hx a b
  rw [heq x hx]
  change (R.flow.metric p.1).inner (f (c.symm x))
    (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ a))
    (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ b)) = _
  rw [hd x (hV hx)]
  rfl

end AncientSpacetimeEmbedding

namespace AncientCompactTimeConvergence

variable {S : AncientRescalingSequence K} (G : AncientCompactTimeConvergence S)

theorem exhaustion_monotone : Monotone G.exhaustion :=
  monotone_nat_of_le_succ G.exhaustion_increasing

theorem eventually_mem_exhaustion (x : G.limit.carrier.carrier) :
    ∀ᶠ k in atTop, x ∈ G.exhaustion k := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp (G.exhaustion_covers.symm ▸ mem_univ x)
  exact (eventually_ge_atTop j).mono (fun k hk ↦ G.exhaustion_monotone hk hj)

theorem eventually_timeWindow_mem_nhds {t : ℝ} (ht : t < 0) :
    ∀ᶠ k : ℕ in atTop, ancientM18TimeWindow k ∈ 𝓝 t := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp
    (ancientM18TimeWindow_covers.symm ▸ (show t ∈ Iio 0 from ht))
  have hb : t ∈ Ioo (-((j : ℝ) + 2)) (-((j : ℝ) + 2)⁻¹) := by
    refine ⟨by linarith [hj.1], lt_of_le_of_lt hj.2 ?_⟩
    apply neg_lt_neg
    exact (inv_lt_inv₀ (by positivity : 0 < (j : ℝ) + 2)
      (by positivity : 0 < (j : ℝ) + 1)).2 (by linarith)
  have hnhds : ancientM18TimeWindow (j + 1) ∈ 𝓝 t := by
    apply mem_of_superset (isOpen_Ioo.mem_nhds hb)
    simpa only [ancientM18TimeWindow, Nat.cast_add, Nat.cast_one, add_assoc,
      show (1 : ℝ) + 1 = 2 from by norm_num] using
      (Ioo_subset_Icc_self : Ioo (-((j : ℝ) + 2)) (-((j : ℝ) + 2)⁻¹) ⊆
        Icc (-((j : ℝ) + 2)) (-((j : ℝ) + 2)⁻¹))
  exact (eventually_ge_atTop (j + 1)).mono (fun k hk ↦
    mem_of_superset hnhds (ancientM18TimeWindow_mono hk))

theorem tendsto_coordinate_metricJet (q : G.limit.carrier.carrier) (r : ℕ)
    (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 < 0)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun k ↦ iteratedFDeriv ℝ r (ancientPullbackCoefficient (G.embedding k) q a b) p)
      atTop (𝓝 (iteratedFDeriv ℝ r (G.limit.carrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limit.flow.metric t).inner x v w) a b) p)) := by
  obtain ⟨j, hjt, hjx⟩ := ((eventually_timeWindow_mem_nhds ht).and
    (G.eventually_mem_exhaustion ((extChartAt (𝓡 n) q).symm p.2))).exists
  have hdom : {p} ⊆ {z | z.1 ∈ ancientM18TimeWindow j ∧
      z.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion j} :=
    singleton_subset_iff.mpr ⟨mem_of_mem_nhds hjt, hp, hjx⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q j r {p} isCompact_singleton hdom ε hε
  exact ⟨N, fun k hk ↦ by
    simpa only [dist_eq_norm, MetricJet] using hN k hk a b p (mem_singleton p)⟩

theorem contDiffAt_limit_coordinateCoefficient (q : G.limit.carrier.carrier)
    (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 < 0)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    ContDiffAt ℝ ∞ (G.limit.carrier.coordinateCoefficient q
      (fun t x v w ↦ (G.limit.flow.metric t).inner x v w) a b) p := by
  let c := extChartAt (𝓡 n) q
  let f : ℝ × EuclideanSpace ℝ (Fin n) → G.limit.carrier.carrier := fun z ↦ c.symm z.2
  have hf {z : ℝ × EuclideanSpace ℝ (Fin n)} (hz : z.2 ∈ c.target) :
      ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ f z := by
    exact ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hz).contMDiffAt
      (extChartAt_target_mem_nhds' hz)).comp z contDiffAt_snd.contMDiffAt
  apply (G.limit.flow.contDiffAt_family_pullback_inner (Iio_mem_nhds ht)
    (hf hp) (0, EuclideanSpace.basisFun (Fin n) ℝ a)
      (0, EuclideanSpace.basisFun (Fin n) ℝ b)).congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.preimage_mem_nhds (extChartAt_target_mem_nhds' hp)]
    with z hz
  rw [← RiemannianMetric.mfderiv_slice_apply ((hf hz).mdifferentiableAt (by simp)),
    ← RiemannianMetric.mfderiv_slice_apply ((hf hz).mdifferentiableAt (by simp))]
  rfl

theorem tendsto_coordinate_spatial_metricJet (q : G.limit.carrier.carrier) (r : ℕ)
    (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 < 0)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun k ↦ iteratedFDeriv ℝ r
      (fun y ↦ ancientPullbackCoefficient (G.embedding k) q a b (p.1, y)) p.2)
      atTop (𝓝 (iteratedFDeriv ℝ r (fun y ↦ G.limit.carrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limit.flow.metric t).inner x v w) a b (p.1, y)) p.2)) := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ) (fun _ : Fin r ↦
      ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n)))
  have h := P.continuous.continuousAt.tendsto.comp
    (G.tendsto_coordinate_metricJet q r a b p ht hp)
  have hlim : iteratedFDeriv ℝ r (fun y ↦ G.limit.carrier.coordinateCoefficient q
      (fun t x v w ↦ (G.limit.flow.metric t).inner x v w) a b (p.1, y)) p.2 =
      P (iteratedFDeriv ℝ r (G.limit.carrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limit.flow.metric t).inner x v w) a b) p) := by
    ext v
    exact Poincare.Analysis.iteratedFDeriv_spatial_slice _
      (G.contDiffAt_limit_coordinateCoefficient q a b p ht hp) r v
  rw [← hlim] at h
  apply h.congr'
  filter_upwards [eventually_timeWindow_mem_nhds ht,
    G.eventually_mem_exhaustion ((extChartAt (𝓡 n) q).symm p.2)] with k hkt hkx
  ext v
  exact (Poincare.Analysis.iteratedFDeriv_spatial_slice _
    ((G.embedding k).contDiffAt_coordinateCoefficient (G.exhaustion_open k)
      q a b p hkt ht ⟨hp, hkx⟩) r v).symm

end AncientCompactTimeConvergence
end PoincareConjecture
