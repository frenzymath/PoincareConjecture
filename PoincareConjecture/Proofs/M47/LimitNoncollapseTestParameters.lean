import PoincareConjecture.Proofs.M47.LimitNoncollapseSharpCapture
import PoincareConjecture.Proofs.M47.LimitNoncollapseCylinders
import PoincareConjecture.Proofs.M09.RiemannianProper

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem limitNoncollapse_exists_finite_test_horizon
    {H : ENNReal} {t rho : ℝ} (ht : t ≤ 0) (_hrho : 0 < rho)
    (hbottom : t - rho ^ 2 ∈ blowupBackwardInterval H) :
    ∃ T : ℝ, 0 < T ∧ ENNReal.ofReal T < H ∧
      Icc (t - rho ^ 2) t ⊆ Ioc (-T) 0 := by
  obtain ⟨T, _, hlow, hhigh⟩ := ENNReal.lt_iff_exists_real_btwn.mp hbottom.2
  have hT : 0 < T := ENNReal.ofReal_pos.mp (zero_le.trans_lt hlow)
  have hlt : -(t - rho ^ 2) < T :=
    (ENNReal.ofReal_lt_ofReal_iff hT).mp hlow
  refine ⟨T, hT, hhigh, ?_⟩
  intro s hs
  exact ⟨by linarith [hs.1], hs.2.trans ht⟩

theorem limitNoncollapse_closure_ball_subset
    {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (p : M) {R r : ℝ} (hr : 0 < r) (hRr : R < r) :
    closure (g.ball p R) ⊆ g.ball p r := by
  let : PseudoEMetricSpace M := g.comparisonPseudoEMetric
  have hclosed : IsClosed {x : M | g.edist p x ≤ ENNReal.ofReal R} :=
    isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hsubset : closure (g.ball p R) ⊆ {x : M | g.edist p x ≤ ENNReal.ofReal R} :=
    closure_minimal (fun x (hx : x ∈ g.ball p R) =>
      show g.edist p x ≤ ENNReal.ofReal R from
        (show g.edist p x < ENNReal.ofReal R from hx).le) hclosed
  intro x hx
  exact (hsubset hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hRr)

theorem limitNoncollapse_eventually_physical_radius
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (rho : ℝ) {r0 : ℝ} (hr0 : 0 < r0) :
    ∀ᶠ k : ℕ in atTop, rho / Real.sqrt (S.scale (G.subsequence k)) ≤ r0 := by
  have hQ : Tendsto (fun k => S.scale (G.subsequence k)) atTop atTop :=
    S.scalar_diverges.comp G.subsequence_strictMono.tendsto_atTop
  have hzero : Tendsto (fun k => rho / Real.sqrt (S.scale (G.subsequence k)))
      atTop (𝓝 0) := (Real.tendsto_sqrt_atTop.comp hQ).const_div_atTop rho
  exact (hzero.eventually (Iio_mem_nhds hr0)).mono (fun _ hk => hk.le)

theorem limitNoncollapse_cancel_physical_volume
    {Q lambda rho kappa : ℝ} (hQ : 0 < Q) (hlambda : 0 < lambda)
    {W V : ENNReal}
    (hlow : ENNReal.ofReal (kappa * (rho / Real.sqrt Q) ^ 3) ≤ W)
    (hupp : W ≤ ENNReal.ofReal (1 / (lambda * Real.sqrt Q)) ^ 3 * V) :
    ENNReal.ofReal (kappa * lambda ^ 3 * rho ^ 3) ≤ V := by
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hprod : 0 < lambda * Real.sqrt Q := mul_pos hlambda hroot
  have hcancel : ENNReal.ofReal (lambda * Real.sqrt Q) ^ 3 *
      ENNReal.ofReal (1 / (lambda * Real.sqrt Q)) ^ 3 = 1 := by
    rw [← mul_pow, ← ENNReal.ofReal_mul hprod.le]
    simp only [mul_one_div_cancel hprod.ne', ENNReal.ofReal_one, one_pow]
  have heq : ENNReal.ofReal (lambda * Real.sqrt Q) ^ 3 *
      ENNReal.ofReal (kappa * (rho / Real.sqrt Q) ^ 3) =
      ENNReal.ofReal (kappa * lambda ^ 3 * rho ^ 3) := by
    rw [← ENNReal.ofReal_pow hprod.le, ← ENNReal.ofReal_mul (pow_nonneg hprod.le 3)]
    congr 1
    field_simp
  have hb := mul_le_mul_right (hlow.trans hupp)
    (ENNReal.ofReal (lambda * Real.sqrt Q) ^ 3)
  rwa [heq, ← mul_assoc, hcancel, one_mul] at hb

end PoincareConjecture.M47
