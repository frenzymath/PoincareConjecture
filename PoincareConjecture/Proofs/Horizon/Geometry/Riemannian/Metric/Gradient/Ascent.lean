import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.InitialData
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

theorem exists_arbitrarily_close_ascent_of_lt_gradient_norm
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    {c : ℝ} (hc : 0 ≤ c) (hgrad : c < g.tangentNorm x (g.gradient f x)) :
    ∀ s : ℝ, 0 < s → ∃ z : M,
      g.edist x z < ENNReal.ofReal s ∧
        c * (g.edist x z).toReal < f z - f x := by
  classical
  obtain ⟨δ, hδ, _, γ, hγ, hp, hv⟩ :=
    g.exists_geodesic_initial_data x (g.gradient f x)
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := by constructor <;> linarith
  have hγd := (hγ.contMDiffOn.contMDiffAt (isOpen_Ioo.mem_nhds h0)).mdifferentiableAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)
  subst x
  let N : ℝ := g.tangentNorm (γ 0) (g.gradient f (γ 0))
  have hN : 0 < N := hc.trans_lt hgrad
  have hchart := mdifferentiableAt_extChartAt (I := 𝓡 n) (mem_chart_source _ (γ 0))
  have heq := congrArg (fun L => L 1) (mfderiv_comp 0 hchart hγd)
  rw [mfderiv_eq_fderiv] at heq
  change deriv (fun t => extChartAt (𝓡 n) (γ 0) (γ t)) 0 = _ at heq
  rw [hv.deriv, mfderiv_extChartAt_self] at heq
  change g.gradient f (γ 0) = mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1 at heq
  have hd := (hf.hasMFDerivAt.comp 0 hγd.hasMFDerivAt).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun t => f (γ t))
    (mvfderiv (𝓡 n) f (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1)) 0 at hd
  rw [← heq, ← g.inner_gradient] at hd
  have hnonneg : 0 ≤ g.inner (γ 0) (g.gradient f (γ 0)) (g.gradient f (γ 0)) := by
    by_cases hz : g.gradient f (γ 0) = 0
    · simp [hz]
    · exact (g.pos _ _ hz).le
  have hsq : N ^ 2 = g.inner (γ 0) (g.gradient f (γ 0)) (g.gradient f (γ 0)) :=
    Real.sq_sqrt hnonneg
  rw [← hsq] at hd
  have hmargin : c * N < N ^ 2 := by
    simpa only [pow_two] using mul_lt_mul_of_pos_right hgrad hN
  have hslopes : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      c * N < (f (γ t) - f (γ 0)) / t := by
    simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hd.tendsto_slope_zero_right.eventually_const_lt hmargin
  have hnorm := (hγ.tangentNorm_initial h0 rfl hv).symm
  rw [← heq] at hnorm
  intro s hs
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < min δ (s / N) :=
    (eventually_lt_nhds (lt_min hδ (div_pos hs hN))).filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, htsmall, htslope⟩ := (hpositive.and (hsmall.and hslopes)).exists
  have htδ : t ∈ Ioo (-δ) δ :=
    ⟨by linarith, htsmall.trans_le (min_le_left _ _)⟩
  have hlength : N * t < s := by
    have h := (lt_div_iff₀ hN).mp (htsmall.trans_le (min_le_right _ _))
    nlinarith only [h]
  have hdist := hγ.edist_le_initial_speed h0 rfl hv htδ
  rw [hnorm, abs_of_pos ht] at hdist
  have hdist' : g.edist (γ 0) (γ t) ≤ ENNReal.ofReal (N * t) := by
    rw [ENNReal.ofReal_mul hN.le]
    exact hdist
  refine ⟨γ t, hdist'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hs).mpr hlength), ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist'
  rw [ENNReal.toReal_ofReal (mul_nonneg hN.le ht.le)] at hreal
  calc
    c * (g.edist (γ 0) (γ t)).toReal ≤ c * (N * t) :=
      mul_le_mul_of_nonneg_left hreal hc
    _ < f (γ t) - f (γ 0) := by
      simpa only [mul_assoc] using (lt_div_iff₀ ht).mp htslope

end PoincareConjecture.RiemannianMetric
