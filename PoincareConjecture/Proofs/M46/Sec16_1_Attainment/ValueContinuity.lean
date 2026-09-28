import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.ValueLowerContinuity

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T start : ℝ} {x : G.Point}

theorem cappedSliceAction_upperSemicontinuousOn
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (C : ActionConfinement G T start x)
    (hstrip : Icc start T ⊆ I.domain)
    {a c : ℝ} (ha : 0 < a) (hc : c ^ 2 ≤ T - start) :
    UpperSemicontinuousOn (cappedSliceAction G T x C.barrier) (Icc a c) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have hbound (b : ℝ) (hb : b ∈ Icc a c) : b ^ 2 ≤ T - start :=
    ((sq_le_sq₀ (ha.trans_le hb.1).le ((ha.trans_le hb.1).le.trans hb.2)).mpr hb.2).trans hc
  intro b hb d hd
  have hbpos := ha.trans_le hb.1
  by_cases hactive : cappedSliceAction G T x C.barrier b < C.barrier
  · obtain ⟨Z, hZ, _, hact⟩ := cappedSliceAction_exponential hM04 hM12 LG E C
      hbpos (hbound b hb) hactive
    obtain ⟨U, hU, hZU, hsub⟩ := E.domain_relative_open (Z, b) hZ
    have hUnear : ∀ᶠ s in 𝓝[Icc a c] b, (Z, s) ∈ U :=
      mem_nhdsWithin_of_mem_nhds
        ((continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
          (hU.mem_nhds hZU))
    have hsurv : ∀ᶠ s in 𝓝[Icc a c] b, (Z, s) ∈ E.domain := by
      filter_upwards [hUnear, self_mem_nhdsWithin] with s hsU hs
      exact hsub ⟨hsU, (ha.trans_le hs.1).le,
        hstrip ⟨by linarith [hbound s hs], sub_le_self _ (sq_nonneg s)⟩⟩
    have hpair : Tendsto (fun s : ℝ => (Z, s)) (𝓝[Icc a c] b)
        (𝓝[E.domain ∩ {z | 0 < z.2}] (Z, b)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(continuous_const.prodMk continuous_id).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [hsurv, self_mem_nhdsWithin] with s hs hsI
      exact ⟨hs, ha.trans_le hsI.1⟩
    have hcont := (LG.exponential.action_differential T x E).1.continuousOn
      (Z, b) ⟨hZ, hbpos⟩
    have hcost : ∀ᶠ s in 𝓝[Icc a c] b, E.action Z s < d :=
      (Filter.Tendsto.comp hcont hpair).eventually (Iio_mem_nhds (hact.le.trans_lt hd))
    filter_upwards [hcost, hsurv, self_mem_nhdsWithin] with s hsCost hsSurv hs
    have hm := (cappedSliceAction_alternative hM04 hM12 LG E C
      (ha.trans_le hs.1) (hbound s hs)).2.1
      (E.gamma Z s) (E.path Z s hsSurv (ha.trans_le hs.1))
    rw [← E.action_eq Z s hsSurv (ha.trans_le hs.1)] at hm
    exact hm.trans_lt hsCost
  · have heq : cappedSliceAction G T x C.barrier b = C.barrier :=
      le_antisymm (cappedSliceAction_alternative hM04 hM12 LG E C hbpos (hbound b hb)).1
        (le_of_not_gt hactive)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (cappedSliceAction_alternative hM04 hM12 LG E C
      (ha.trans_le hs.1) (hbound s hs)).1.trans_lt (heq ▸ hd)

theorem cappedSliceAction_continuousOn
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (C : ActionConfinement G T start x)
    (hstrip : Icc start T ⊆ I.domain)
    {a c : ℝ} (ha : 0 < a) (hc : c ^ 2 ≤ T - start) :
    ContinuousOn (cappedSliceAction G T x C.barrier) (Icc a c) :=
  continuousOn_iff_lower_upperSemicontinuousOn.mpr
    ⟨cappedSliceAction_lowerSemicontinuousOn hM04 hM12 LG E C hstrip ha hc,
      cappedSliceAction_upperSemicontinuousOn hM04 hM12 LG E C hstrip ha hc⟩

end PoincareConjecture.Proofs.M46
