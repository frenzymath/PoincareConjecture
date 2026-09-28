import PoincareConjecture.Proofs.M34.Standard.LocalRicciFlowVolume
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.EarlyBallVolume
import PoincareConjecture.Proofs.M04.TensorNormBounds
import PoincareConjecture.Proofs.M09.RiemannianProper











set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M34




theorem partialFlow_exists_fixed_exterior_volume
    {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0)
    (P : RicciFlowCurvatureTheory.{0}) {T0 B : ℝ} (hT0 : T0 ∈ Ioo 0 F.lifetime)
    (hB : 0 < B) {X : Set StandardCapSpace} (hX : IsCompact X)
    (hcurv : ∀ t ∈ Ico T0 F.lifetime, ∀ x ∉ X,
      (F.flow.connection t).curvatureTensorNorm x ≤ 2 * B) :
    ∃ Omega : Set StandardCapSpace, IsOpen Omega ∧ Omega.Nonempty ∧
      IsCompact (closure Omega) ∧ Omega ⊆ Xᶜ ∧
      ∃ v : ℝ, 0 < v ∧ ∀ t ∈ Ico T0 F.lifetime,
        ENNReal.ofReal v ≤ calibratedMetricVolume (F.flow.metric t) Omega := by
  obtain ⟨r0, kappa, hr0, hkappa, hearly⟩ :=
    partialFlow_early_small_ball_volume F P ⟨hT0.1.le, hT0.2⟩
  obtain ⟨x, hx⟩ := nonempty_compl.mpr hX.ne_univ
  let g := F.flow.metric T0
  let : PseudoEMetricSpace StandardCapSpace := g.comparisonPseudoEMetric
  obtain ⟨eps, heps, hball⟩ := EMetric.mem_nhds_iff.mp (hX.isClosed.isOpen_compl.mem_nhds hx)
  obtain ⟨d, _, hd, hdeps⟩ := ENNReal.lt_iff_exists_real_btwn.mp heps
  have hdpos : 0 < d := ENNReal.ofReal_pos.mp hd
  let r := min r0 d
  have hr : 0 < r := lt_min hr0 hdpos
  let Omega := g.ball x r
  have hOmega : IsOpen Omega := isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hxOmega : x ∈ Omega := by
    change g.comparisonPseudoEMetric.edist x x < ENNReal.ofReal r
    rw [g.comparisonPseudoEMetric.edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hOmegaU : Omega ⊆ Xᶜ := by
    intro y hy
    apply hball
    change g.comparisonPseudoEMetric.edist y x < eps
    rw [g.comparisonPseudoEMetric.edist_comm]
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _)) |>.trans hdeps
  let c := Real.exp (6 * B * F.lifetime)
  have hc : 0 < c := Real.exp_pos _
  let v := kappa * r ^ 3 / c ^ 3
  have hv : 0 < v := div_pos (mul_pos hkappa (pow_pos hr 3)) (pow_pos hc 3)
  refine ⟨Omega, hOmega, ⟨x, hxOmega⟩,
    Proofs.M09.isCompact_closure_metric_ball g (partialFlow_complete F P ⟨hT0.1.le, hT0.2⟩) x r,
    hOmegaU, v, hv, ?_⟩
  intro t ht
  have hsub : Icc T0 t ⊆ Ico 0 F.lifetime :=
    fun s hs => ⟨hT0.1.le.trans hs.1, hs.2.trans_lt ht.2⟩
  have hRic : ∀ tau ∈ Icc T0 t, ∀ y ∈ Xᶜ, ∀ w : TangentSpace (𝓡 3) y,
      |(F.flow.connection tau).ricci y w w| ≤ (6 * B) * (F.flow.metric tau).inner y w w := by
    intro tau htau y hy w
    have hfull := hcurv tau ⟨htau.1, htau.2.trans_lt ht.2⟩ y hy
    have hself : 0 ≤ (F.flow.metric tau).inner y w w := by
      by_cases hw : w = 0
      · simp [hw]
      · exact ((F.flow.metric tau).pos y w hw).le
    calc
      _ ≤ (3 : ℝ) * (F.flow.connection tau).curvatureTensorNorm y *
          (F.flow.metric tau).inner y w w := M04.abs_ricci_le_curvatureTensorNorm _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hself
  have hlength : |T0 - t| ≤ F.lifetime := by
    rw [abs_of_nonpos (sub_nonpos.mpr ht.1)]
    linarith [hT0.1, ht.2]
  have hvolume := calibratedMetricVolume_le_exp_mul_of_local_ricci_bound F.flow
    (convex_Icc T0 t) hsub hX.isClosed.isOpen_compl hOmega.measurableSet hOmegaU
    (show 0 ≤ 6 * B by positivity) ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ hlength hRic
  have hreference := hearly T0 ⟨hT0.1.le, le_rfl⟩ x r hr (min_le_left _ _)
  have hmeasure : ENNReal.ofReal (kappa * r ^ 3) ≤
      ENNReal.ofReal c ^ 3 * calibratedMetricVolume (F.flow.metric t) Omega :=
    hreference.trans hvolume
  have hc3 : 0 < c ^ 3 := pow_pos hc 3
  change ENNReal.ofReal (kappa * r ^ 3 / c ^ 3) ≤ _
  rw [ENNReal.ofReal_div_of_pos hc3]
  apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hc3).ne' ENNReal.ofReal_ne_top).mpr
  simpa only [ENNReal.ofReal_pow hc.le, mul_comm] using hmeasure

end PoincareConjecture.M34
