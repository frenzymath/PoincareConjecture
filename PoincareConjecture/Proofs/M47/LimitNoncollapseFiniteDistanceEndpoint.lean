import PoincareConjecture.Proofs.M47.LimitNoncollapseFiniteHarnack
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.MetricMonotonicity

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    T3Space L.carrier.carrier := L.carrier.t3Space
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    ConnectedSpace L.carrier.carrier := L.connectedSpace

private theorem pair_ball {J : Set ℝ} (L : BlowupLimitFlow.{u} J)
    (s : ℝ) (x y : L.carrier.carrier) :
    let r := ((L.flow.metric s).edist x y).toReal + 1
    x ∈ (L.flow.metric s).ball x r ∧ y ∈ (L.flow.metric s).ball x r := by
  dsimp only
  constructor
  · change (L.flow.metric s).edist x x < _
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      (ENNReal.ofReal_pos.mpr (by positivity :
        0 < ((L.flow.metric s).edist x y).toReal + 1))
  · change (L.flow.metric s).edist x y < _
    conv_lhs => rw [← ENNReal.ofReal_toReal ((L.flow.metric s).edist_ne_top x y)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)

theorem limitFinite_distance_exp (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) {Q : ℝ} (hQ : 0 < Q)
    (hQ0 : ∀ x : L.carrier.carrier, (L.flow.connection 0).scalarCurvature x ≤ Q)
    {s t : ℝ} (hs : s ∈ Icc (-H.toReal / 2) 0) (ht : t ∈ Icc (-H.toReal / 2) 0)
    (x y : L.carrier.carrier) :
    ((L.flow.metric t).edist x y).toReal ≤ Real.exp (2 * Q * |t - s|) *
      ((L.flow.metric s).edist x y).toReal := by
  have hT := limitFinite_horizon_pos hH hfinite
  have hsub : Icc (-H.toReal / 2) 0 ⊆ blowupBackwardInterval H := by
    rw [limitFinite_domain_eq hfinite]
    exact fun _ hu => ⟨by linarith [hu.1], hu.2⟩
  have hcoef : Q * H.toReal / (-H.toReal / 2 + H.toReal) = 2 * Q := by
    apply (div_eq_iff (by linarith : -H.toReal / 2 + H.toReal ≠ 0)).mpr
    ring
  have hRic (τ : ℝ) (hτ : τ ∈ Icc (-H.toReal / 2) 0)
      (z : L.carrier.carrier) (v : TangentSpace (𝓡 3) z) :
      |(L.flow.connection τ).ricci z v v| ≤ 2 * Q * (L.flow.metric τ).inner z v v := by
    have h := limitFinite_ricci_slab h04 hH hfinite L hQ hQ0
      (by linarith : -H.toReal < -H.toReal / 2) (le_refl 0) τ hτ z v
    simpa only [abs_of_nonneg h.1, hcoef] using h.2
  let r := ((L.flow.metric s).edist x y).toReal + 1
  have hr : 0 < r := by dsimp only [r]; positivity
  have hp := pair_ball L s x y
  have h := L.flow.edist_le_exp_mul_of_ricci_bound (convex_Icc _ _) hsub
    x r (2 * Q) hr hs ht (fun τ hτ z _ v => hRic τ hτ z v) hp.1 hp.2
  have hfin : ENNReal.ofReal (Real.exp (2 * Q * |t - s|)) *
      (L.flow.metric s).edist x y ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((L.flow.metric s).edist_ne_top x y)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
    ENNReal.toReal_mono hfin h

theorem limitFinite_distance_tendsto_zero (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) {Q : ℝ} (hQ : 0 < Q)
    (hQ0 : ∀ x : L.carrier.carrier, (L.flow.connection 0).scalarCurvature x ≤ Q)
    (x y : L.carrier.carrier) :
    Tendsto (fun t => ((L.flow.metric t).edist x y).toReal)
      (𝓝[blowupBackwardInterval H] 0) (𝓝 (((L.flow.metric 0).edist x y).toReal)) := by
  have hT := limitFinite_horizon_pos hH hfinite
  let d := ((L.flow.metric 0).edist x y).toReal
  have h0 : (0 : ℝ) ∈ Icc (-H.toReal / 2) 0 := ⟨by linarith, le_rfl⟩
  have hI : ∀ᶠ s in 𝓝[blowupBackwardInterval H] 0, s ∈ Icc (-H.toReal / 2) 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (by linarith : -H.toReal / 2 < 0)).filter_mono
        nhdsWithin_le_nhds] with s hs hs'
    exact ⟨hs'.le, hs.1⟩
  have hl : Tendsto (fun s : ℝ => Real.exp (-2 * Q * |s|) * d)
      (𝓝[blowupBackwardInterval H] 0) (𝓝 d) := by
    have hc : Continuous (fun s : ℝ => Real.exp (-2 * Q * |s|) * d) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := blowupBackwardInterval H))
  have hu : Tendsto (fun s : ℝ => Real.exp (2 * Q * |s|) * d)
      (𝓝[blowupBackwardInterval H] 0) (𝓝 d) := by
    have hc : Continuous (fun s : ℝ => Real.exp (2 * Q * |s|) * d) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := blowupBackwardInterval H))
  apply hl.squeeze' hu
  · filter_upwards [hI] with s hs
    have h := limitFinite_distance_exp h04 hH hfinite L hQ hQ0 hs h0 x y
    simp only [zero_sub, abs_neg] at h
    calc
      Real.exp (-2 * Q * |s|) * d = d / Real.exp (2 * Q * |s|) := by
        rw [show -2 * Q * |s| = -(2 * Q * |s|) by ring, Real.exp_neg]
        ring
      _ ≤ ((L.flow.metric s).edist x y).toReal :=
        (div_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using h)
  · filter_upwards [hI] with s hs
    simpa only [sub_zero] using
      limitFinite_distance_exp h04 hH hfinite L hQ hQ0 h0 hs x y

theorem limitFinite_distance_interior_antitone (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H))
    {s t : ℝ} (hs : -H.toReal < s) (ht : t < 0) (hst : s ≤ t)
    (x y : L.carrier.carrier) :
    ((L.flow.metric t).edist x y).toReal ≤ ((L.flow.metric s).edist x y).toReal := by
  have hJ : Icc s t ⊆ interior (blowupBackwardInterval H) := by
    rw [limitFinite_interior_eq hfinite]
    exact fun _ hτ => ⟨hs.trans_le hτ.1, hτ.2.trans_lt ht⟩
  let r := ((L.flow.metric s).edist x y).toReal + 1
  have hp := pair_ball L s x y
  have h := RiemannianMetric.edist_le_mul_edist_of_tangentNorm_le_on_ball
    (L.flow.metric s) (L.flow.metric t) x r 1 (by dsimp only [r]; positivity)
    zero_lt_one (fun z _ v => by
      simpa only [one_mul] using L.flow.tangentNorm_le_of_ricci_nonneg hJ z v
        (fun τ hτ => (limitFinite_ricci_bounds h04 L τ (interior_subset (hJ hτ)) z v).1)
        (show s ∈ Icc s t from ⟨le_rfl, hst⟩)
        (show t ∈ Icc s t from ⟨hst, le_rfl⟩) hst) hp.1 hp.2
  simp only [ENNReal.ofReal_one, one_mul] at h
  exact ENNReal.toReal_mono ((L.flow.metric s).edist_ne_top x y) h

theorem limitFinite_distance_antitone (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) {Q : ℝ} (hQ : 0 < Q)
    (hQ0 : ∀ x : L.carrier.carrier, (L.flow.connection 0).scalarCurvature x ≤ Q)
    {s t : ℝ} (hs : s ∈ blowupBackwardInterval H)
    (ht : t ∈ blowupBackwardInterval H) (hst : s ≤ t) (x y : L.carrier.carrier) :
    ((L.flow.metric t).edist x y).toReal ≤ ((L.flow.metric s).edist x y).toReal := by
  have hs' : -H.toReal < s := ((limitFinite_domain_eq hfinite ▸ hs) : s ∈ Ioc _ _).1
  rcases lt_or_eq_of_le ht.1 with htneg | rfl
  · exact limitFinite_distance_interior_antitone h04 hfinite L hs' htneg hst x y
  rcases lt_or_eq_of_le hst with hsneg | rfl
  · have hzero : (0 : ℝ) ∈ closure (Ioo s 0) := by
      rw [closure_Ioo hsneg.ne]
      exact ⟨hsneg.le, le_rfl⟩
    have hsub : Ioo s 0 ⊆ blowupBackwardInterval H := by
      rw [limitFinite_domain_eq hfinite]
      exact fun _ hτ => ⟨hs'.trans hτ.1, hτ.2.le⟩
    have hc : ContinuousWithinAt (fun τ => ((L.flow.metric τ).edist x y).toReal)
        (blowupBackwardInterval H) 0 :=
      limitFinite_distance_tendsto_zero h04 hH hfinite L hQ hQ0 x y
    exact ContinuousWithinAt.closure_le hzero (hc.mono hsub) continuousWithinAt_const
      (fun τ hτ => limitFinite_distance_interior_antitone h04 hfinite L hs' hτ.2 hτ.1.le x y)
  · exact le_rfl

end PoincareConjecture.M47
