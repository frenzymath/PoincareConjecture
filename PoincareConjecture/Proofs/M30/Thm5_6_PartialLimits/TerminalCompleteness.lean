import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Completeness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space

theorem metricComplete_terminal_of_closed_slab_curvature_bound
    {n : ℕ} (C : FlowCarrier.{u} n) {J : Set ℝ}
    (F : RicciFlow n C.carrier J) (p : C.carrier)
    {a : ℝ} (ha : a ≤ 0) (hslab : Icc a 0 ⊆ J)
    (hcomplete : C.metricComplete (F.metric a))
    (hcurv : ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧
      ∀ t ∈ Icc a 0, ∀ x ∈ (F.metric 0).ball p A,
        (F.connection t).curvatureTensorNorm x ≤ K) :
    C.metricComplete (F.metric 0) := by
  let d₀ := (C.metricEMetricSpace (F.metric a)).toPseudoEMetricSpace
  let d₁ := (C.metricEMetricSpace (F.metric 0)).toPseudoEMetricSpace
  change @CompleteSpace C.carrier d₁.toUniformSpace
  apply Poincare.completeSpace_of_continuous_local_edist_bound d₀ d₁ p hcomplete
  · change @Continuous C.carrier C.carrier C.topologicalSpace C.topologicalSpace id
    exact continuous_id
  · exact fun x => @Poincare.edist_ne_top_of_preconnected C.carrier d₁
      (C.preconnected_metricEMetricSpace (F.metric 0)) x p
  · intro R
    let r : ℝ := R + 1
    have hr : 0 < r := by dsimp only [r]; positivity
    obtain ⟨K, _, hK⟩ := hcurv (3 * r) (by positivity)
    let L : ℝ := (n : ℝ) ^ 3 * K
    let E : ℝ := Real.exp (L * |a|)
    refine ⟨Real.toNNReal E, fun x y hx hy => ?_⟩
    have hRic : ∀ t ∈ Icc a 0, ∀ z ∈ (F.metric 0).ball p (3 * r),
        ∀ v : C.tangent z,
          |(F.connection t).ricci z v v| ≤ L * (F.metric t).inner z v v := by
      intro t ht z hz v
      have hQ : 0 ≤ (F.metric t).inner z v v := by
        by_cases hv : v = 0
        · subst v; simp
        · exact ((F.metric t).pos z v hv).le
      have hnorm := (F.connection t).abs_ricci_quadratic_le_curvatureTensorNorm z v
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) z) = n :=
        finrank_euclideanSpace_fin
      simp only [Fintype.card_fin, hdim] at hnorm
      exact hnorm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hK t ht z hz) (by positivity)) hQ)
    have hR : (R : ℝ≥0∞) < ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_lt_ofReal_iff hr |>.mpr (by dsimp only [r]; linarith)
    have hmem (z : C.carrier) (hz : d₁.edist z p ≤ R) :
        z ∈ (F.metric 0).ball p r := by
      change d₁.edist p z < ENNReal.ofReal r
      rw [d₁.edist_comm]
      exact hz.trans_lt hR
    have hdist := F.edist_le_exp_mul_of_ricci_bound (convex_Icc a 0)
      hslab p r L hr
      (show (0 : ℝ) ∈ Icc a 0 from ⟨ha, le_rfl⟩)
      (show a ∈ Icc a 0 from ⟨le_rfl, ha⟩) hRic (hmem x hx) (hmem y hy)
    change (F.metric a).edist x y ≤ ENNReal.ofReal E * (F.metric 0).edist x y
    simpa only [sub_zero] using hdist

end PoincareConjecture.M30
