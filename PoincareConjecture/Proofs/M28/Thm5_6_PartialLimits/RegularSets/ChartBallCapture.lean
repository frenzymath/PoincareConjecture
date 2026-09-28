import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.MetricConvergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.Distance










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28.RegularPointedMetricConvergence

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  [∀ k, T3Space (M k)] [∀ k, PreconnectedSpace (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}




theorem exists_eventual_chart_ball_capture
    (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : G.limitCarrier.carrier) (rho : ℝ), 0 < rho →
      ∃ r : ℝ, 0 < r ∧
        closedBall (extChartAt (𝓡 n) q q) (2 * r) ⊆ (extChartAt (𝓡 n) q).target ∧
        ∀ᶠ k in atTop,
          (extChartAt (𝓡 n) q).symm ''
            closedBall (extChartAt (𝓡 n) q q) (2 * r) ⊆ G.exhaustion k ∧
          ∀ z ∈ closedBall (extChartAt (𝓡 n) q q) (2 * r),
            G.embedding k ((extChartAt (𝓡 n) q).symm z) ∈
              (g (G.subsequence k)).ball (G.embedding k q) rho := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q rho hrho
  let c := extChartAt (𝓡 n) q
  let x := c q
  have hx : x ∈ c.target := mem_extChartAt_target q
  have hc : c.symm x = q := extChartAt_to_inv q
  obtain ⟨j, hj⟩ : ∃ j, q ∈ G.exhaustion j := by
    have hq : q ∈ ⋃ j, G.exhaustion j := G.exhaustion_covers.symm ▸ mem_univ q
    exact mem_iUnion.mp hq
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  let U := c.target ∩ c.symm ⁻¹' G.exhaustion j
  have hU : IsOpen U :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) (G.exhaustion_open j)
  have hxU : x ∈ U := ⟨hx, by simpa only [mem_preimage, hc] using hj⟩
  obtain ⟨R, hR, hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hxU)
  let K := closedBall x R
  have hK : IsCompact K := isCompact_closedBall _ _
  let B₀ := G.limitMetric.pullbackCoefficients c.symm
  let B := fun k => (g (G.subsequence k)).pullbackCoefficients (G.embedding k ∘ c.symm)
  have hcontinuous : ContinuousOn B₀ K := by
    intro z hz
    exact (G.limitMetric.contDiffAt_pullbackCoefficients
      ((contMDiffOn_extChartAt_symm q).contMDiffAt
        ((isOpen_extChartAt_target q).mem_nhds (hRU hz).1))).continuousAt.continuousWithinAt
  obtain ⟨b₀, hb₀⟩ := hK.exists_bound_of_continuousOn hcontinuous
  let b := max (b₀ + 1) 1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hzero : TendstoUniformlyOn B B₀ atTop K := by
    exact (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
        (G.metric_jets q 0 K hK (fun z hz => (hRU hz).1))
  have hnear := Metric.tendstoUniformlyOn_iff.mp hzero 1 zero_lt_one
  let r := min (R / 4) (rho / (4 * Real.sqrt b))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : 2 * r < R := by
    have h := min_le_left (R / 4) (rho / (4 * Real.sqrt b))
    dsimp only [r]
    linarith
  have hrho' : Real.sqrt b * (2 * r) < rho := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hsqrt)).mp
      (min_le_right (R / 4) (rho / (4 * Real.sqrt b)))
    dsimp only [r]
    nlinarith
  have hsmall : closedBall x (2 * r) ⊆ ball x R := closedBall_subset_ball hrR
  refine ⟨r, hr, (hsmall.trans ball_subset_closedBall).trans
    (fun z hz => (hRU hz).1), ?_⟩
  filter_upwards [hnear, eventually_ge_atTop j] with k hk hjk
  have hstage : ∀ z ∈ K, c.symm z ∈ G.exhaustion k :=
    fun z hz => hmono hjk (hRU hz).2
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hstage z (ball_subset_closedBall (hsmall hz))
  intro z hz
  have hsmooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞
      (G.embedding k ∘ c.symm) (ball x R) := by
    intro y hy
    have hyK : y ∈ K := ball_subset_closedBall hy
    exact ((G.embedding_smooth k ⟨c.symm y, hstage y hyK⟩).contMDiffAt.comp y
      ((contMDiffOn_extChartAt_symm q).contMDiffAt
        ((isOpen_extChartAt_target q).mem_nhds (hRU hyK).1))).contMDiffWithinAt
  have hupper : ∀ y ∈ ball x R, ∀ v : EuclideanSpace ℝ (Fin n),
      B k y v v ≤ b * ‖v‖ ^ 2 := by
    intro y hy v
    have hyK : y ∈ K := ball_subset_closedBall hy
    have hnorm : ‖B k y‖ ≤ b := by
      have hdist : ‖B k y - B₀ y‖ < 1 := by
        simpa only [dist_eq_norm, norm_sub_rev] using hk y hyK
      have htriangle := norm_add_le (B k y - B₀ y) (B₀ y)
      rw [sub_add_cancel] at htriangle
      exact (by linarith [hb₀ y hyK] : ‖B k y‖ ≤ b₀ + 1).trans (le_max_left _ _)
    calc
      B k y v v ≤ ‖B k y v v‖ := by
        simpa only [Real.norm_eq_abs] using le_abs_self (B k y v v)
      _ ≤ ‖B k y‖ * ‖v‖ * ‖v‖ := (B k y).le_opNorm₂ v v
      _ ≤ b * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
  have hdist := (g (G.subsequence k)).toReal_edist_le_of_pullback_upper
    isOpen_ball (convex_ball x R) hsmooth hb.le hupper
    (mem_ball_self hR) (hsmall hz)
  have hreal : ((g (G.subsequence k)).edist (G.embedding k q)
      (G.embedding k (c.symm z))).toReal < rho := by
    have hzx : dist x z ≤ 2 * r := by simpa only [dist_comm] using mem_closedBall.mp hz
    simpa only [Function.comp_apply, hc] using
      hdist.trans_lt ((mul_le_mul_of_nonneg_left hzx hsqrt.le).trans_lt hrho')
  change (g (G.subsequence k)).edist (G.embedding k q)
    (G.embedding k (c.symm z)) < ENNReal.ofReal rho
  rw [← ENNReal.ofReal_toReal ((g (G.subsequence k)).edist_ne_top _ _)]
  exact (ENNReal.ofReal_lt_ofReal_iff hrho).mpr hreal

end PoincareConjecture.M28.RegularPointedMetricConvergence
