import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.Convolution.Directional
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.MeanValue.UpperSupport








set_option autoImplicit false
open Set Filter ContinuousLinearMap MeasureTheory
open scoped Convolution NNReal ContDiff Topology

namespace Poincare


theorem exists_contDiff_hessian_directional_approx_of_lipschitzOn_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} {f : E → ℝ} {K : ℝ≥0} {C : ℝ}
    {x₀ : E} {r R : ℝ} (hrR : r < R)
    (hf : LipschitzOnWith K f (Metric.ball x₀ R))
    (hconc : ConcaveOn ℝ (Metric.ball x₀ R) (fun x => f x - C * ‖x‖ ^ 2 / 2))
    (v : ι → E → E) (lo hi : ι → E → ℝ)
    (hinc : ∀ i x, x ∈ Metric.ball x₀ r → ∀ y ∈ Metric.ball x₀ R,
      ∀ t : ℝ, 0 ≤ t → y + t • v i x ∈ Metric.ball x₀ R →
        t * lo i x ≤ f (y + t • v i x) - f y ∧
          f (y + t • v i x) - f y ≤ t * hi i x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x ∈ Metric.ball x₀ R, dist (u x) (f x) ≤ ε) ∧
      (∀ x ∈ Metric.ball x₀ r, ∀ w : E,
        fderiv ℝ (fderiv ℝ u) x w w ≤ C * ‖w‖ ^ 2) ∧
      ∀ i x, x ∈ Metric.ball x₀ r →
        lo i x ≤ fderiv ℝ u x (v i x) ∧ fderiv ℝ u x (v i x) ≤ hi i x := by
  borelize E
  let μ : Measure E := Measure.addHaar
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  have hcF : ConcaveOn ℝ (Metric.ball x₀ R)
      (fun x => F x - C * ‖x‖ ^ 2 / 2) :=
    hconc.congr (fun x hx => congrArg (fun z => z - C * ‖x‖ ^ 2 / 2) (heq hx))
  let ρ : ℝ := min ((R - r) / 2) (ε / (K + 1))
  have hρ : 0 < ρ := lt_min (half_pos (sub_pos.mpr hrR))
    (div_pos hε (by positivity))
  have hρR : ρ ≤ (R - r) / 2 := min_le_left _ _
  let φ : ContDiffBump (0 : E) := ⟨ρ / 2, ρ, half_pos hρ, half_lt_self hρ⟩
  let u := φ.normed μ ⋆[lsmul ℝ ℝ, μ] F
  have hu : ContDiff ℝ ∞ u := φ.hasCompactSupport_normed.contDiff_convolution_left _
    φ.contDiff_normed hF.continuous.locallyIntegrable
  have hnear : ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ Metric.ball x ρ,
      dist y x₀ < r + ρ := by
    intro x hx y hy
    exact (dist_triangle y x x₀).trans_lt (by
      have := Metric.mem_ball.mp hx
      have := Metric.mem_ball.mp hy
      linarith)
  have hnearR : ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ Metric.ball x ρ,
      y ∈ Metric.ball x₀ R := by
    intro x hx y hy
    exact (hnear x hx y hy).trans_le (by linarith)
  refine ⟨u, hu, lipschitzWith_normed_convolution μ hF φ, ?_, ?_, ?_⟩
  · intro x hx
    rw [heq hx]
    apply (dist_normed_convolution_le_radius μ hF φ x).trans
    change (K : ℝ) * ρ ≤ ε
    have hsmall : ρ ≤ ε / (K + 1) := min_le_right _ _
    have hbound := (le_div_iff₀ (show 0 < (K : ℝ) + 1 by positivity)).mp hsmall
    nlinarith [K.coe_nonneg]
  · have hc : ConcaveOn ℝ (Metric.ball x₀ r) (fun x => u x - C * ‖x‖ ^ 2 / 2) := by
      apply concaveOn_sub_norm_sq_normed_convolution_on μ (convex_ball x₀ r)
        hF.continuous hcF φ
      intro z hz x hx
      apply hnearR x hx
      simpa only [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left,
        norm_neg, sub_zero] using hz
    intro x hx w
    exact Analysis.fderiv_fderiv_le_of_concaveOn_sub_norm_sq
      Metric.isOpen_ball hu.contDiffOn hc hx w
  · intro i x hx
    let T : ℝ := (R - r) / (2 * (‖v i x‖ + 1))
    have hT : 0 < T := div_pos (sub_pos.mpr hrR) (by positivity)
    have hstep : ∀ t ∈ Ioo (0 : ℝ) T, ∀ y ∈ Metric.ball x ρ,
        ∀ w : E, ‖w‖ = ‖v i x‖ → y + t • w ∈ Metric.ball x₀ R := by
      intro t ht y hy w hw
      have htprod : t * (2 * (‖v i x‖ + 1)) < R - r :=
        (lt_div_iff₀ (by positivity)).mp ht.2
      have hn : ‖t • w‖ = t * ‖v i x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, hw]
      have hdist : dist (y + t • w) x₀ ≤ dist y x₀ + ‖t • w‖ := by
        simpa only [dist_eq_norm, add_sub_right_comm] using
          norm_add_le (y - x₀) (t • w)
      have hnnear := hnear x hx y hy
      rw [Metric.mem_ball]
      rw [hn] at hdist
      nlinarith [norm_nonneg (v i x)]
    have hupper : fderiv ℝ u x (v i x) ≤ hi i x := by
      apply fderiv_normed_convolution_apply_le_of_increment_bound μ hF.continuous φ hT
      intro t ht y hy
      have hyR := hnearR x hx y hy
      have hzR := hstep t ht y hy (v i x) rfl
      simpa only [heq hyR, heq hzR] using (hinc i x hx y hyR t ht.1.le hzR).2
    have hlower : fderiv ℝ u x (-v i x) ≤ -lo i x := by
      apply fderiv_normed_convolution_apply_le_of_increment_bound μ hF.continuous φ hT
      intro t ht y hy
      have hyR := hnearR x hx y hy
      have hzR := hstep t ht y hy (-v i x) (norm_neg _)
      have hz : y + t • (-v i x) + t • v i x = y := by
        simp only [smul_neg]
        abel
      have hb := (hinc i x hx (y + t • (-v i x)) hzR t ht.1.le
        (by simpa only [hz] using hyR)).1
      rw [hz] at hb
      rw [← heq hyR, ← heq hzR]
      nlinarith
    rw [map_neg] at hlower
    exact ⟨by linarith, hupper⟩


theorem exists_contDiff_hessian_directional_approx_of_upper_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} {f : E → ℝ} {K : ℝ≥0} {C : ℝ}
    {x₀ : E} {r R : ℝ} (hrR : r < R)
    (hf : LipschitzOnWith K f (Metric.ball x₀ R))
    (hconc : ConcaveOn ℝ (Metric.ball x₀ R) (fun x => f x - C * ‖x‖ ^ 2 / 2))
    (v : ι → E → E) (lo hi : ι → E → ℝ)
    (hsupport : ∀ i x, x ∈ Metric.ball x₀ r → ∀ y ∈ Metric.ball x₀ R,
      ∃ g : E → ℝ, DifferentiableAt ℝ g y ∧ g y = f y ∧
        (∀ᶠ z in 𝓝 y, f z ≤ g z) ∧
        lo i x ≤ fderiv ℝ g y (v i x) ∧ fderiv ℝ g y (v i x) ≤ hi i x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x ∈ Metric.ball x₀ R, dist (u x) (f x) ≤ ε) ∧
      (∀ x ∈ Metric.ball x₀ r, ∀ w : E,
        fderiv ℝ (fderiv ℝ u) x w w ≤ C * ‖w‖ ^ 2) ∧
      ∀ i x, x ∈ Metric.ball x₀ r →
        lo i x ≤ fderiv ℝ u x (v i x) ∧ fderiv ℝ u x (v i x) ≤ hi i x := by
  apply exists_contDiff_hessian_directional_approx_of_lipschitzOn_ball hrR hf hconc
    v lo hi ?_ hε
  intro i x hx y hy t ht hz
  exact Analysis.increment_bounds_of_fderiv_upper_support
    (convex_ball x₀ R) hf.continuousOn (hsupport i x hx) hy ht hz


theorem exists_contDiff_hessian_directional_approx_of_field_upper_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} {f : E → ℝ} {K : ℝ≥0} {C L η : ℝ}
    {x₀ : E} {r R : ℝ} (hrR : r < R)
    (hf : LipschitzOnWith K f (Metric.ball x₀ R))
    (hconc : ConcaveOn ℝ (Metric.ball x₀ R) (fun x => f x - C * ‖x‖ ^ 2 / 2))
    (v : ι → E → E) (B : ι → ℝ) (hL : 0 ≤ L)
    (hvariation : ∀ i x, x ∈ Metric.ball x₀ r → ∀ y ∈ Metric.ball x₀ R,
      ‖v i x - v i y‖ ≤ η)
    (hsupport : ∀ i y, y ∈ Metric.ball x₀ R →
      ∃ g : E → ℝ, DifferentiableAt ℝ g y ∧ g y = f y ∧
        (∀ᶠ z in 𝓝 y, f z ≤ g z) ∧ ‖fderiv ℝ g y‖ ≤ L ∧
        |fderiv ℝ g y (v i y)| ≤ B i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x ∈ Metric.ball x₀ R, dist (u x) (f x) ≤ ε) ∧
      (∀ x ∈ Metric.ball x₀ r, ∀ w : E,
        fderiv ℝ (fderiv ℝ u) x w w ≤ C * ‖w‖ ^ 2) ∧
      ∀ i x, x ∈ Metric.ball x₀ r →
        |fderiv ℝ u x (v i x)| ≤ B i + L * η := by
  have hfixed : ∀ i x, x ∈ Metric.ball x₀ r → ∀ y ∈ Metric.ball x₀ R,
      ∃ g : E → ℝ, DifferentiableAt ℝ g y ∧ g y = f y ∧
        (∀ᶠ z in 𝓝 y, f z ≤ g z) ∧
        -(B i + L * η) ≤ fderiv ℝ g y (v i x) ∧
          fderiv ℝ g y (v i x) ≤ B i + L * η := by
    intro i x hx y hy
    obtain ⟨g, hg, heq, hmajor, hnorm, hbound⟩ := hsupport i y hy
    refine ⟨g, hg, heq, hmajor, ?_⟩
    apply abs_le.mp
    calc
      |fderiv ℝ g y (v i x)| =
          |fderiv ℝ g y (v i y) + fderiv ℝ g y (v i x - v i y)| := by
        congr 1
        rw [map_sub]
        ring
      _ ≤ |fderiv ℝ g y (v i y)| + |fderiv ℝ g y (v i x - v i y)| := abs_add_le _ _
      _ ≤ B i + L * η := add_le_add hbound (by
        rw [← Real.norm_eq_abs]
        exact ((fderiv ℝ g y).le_opNorm _).trans
          (mul_le_mul hnorm (hvariation i x hx y hy) (norm_nonneg _) hL))
  obtain ⟨u, hu, hLip, herr, hess, hdir⟩ :=
    exists_contDiff_hessian_directional_approx_of_upper_support hrR hf hconc v
      (fun i _ => -(B i + L * η)) (fun i _ => B i + L * η) hfixed hε
  exact ⟨u, hu, hLip, herr, hess, fun i x hx => abs_le.mpr (hdir i x hx)⟩

end Poincare
