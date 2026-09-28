import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAverageDerivative











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Topology Convolution

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)





theorem suWeakGradient_holder_representative {m : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
    (hu : MemLp u 2 (volume.restrict (Metric.ball 0 2)))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball 0 2)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun y => p i y b) (fun y => u y b)
      (Metric.ball 0 2)) {K : ℝ} (hK : 0 ≤ K)
    (henergy : ∀ i : Fin 2, ∀ a ∈ Metric.closedBall (0 : Plane) 1,
      ∀ r ∈ Ioc (0 : ℝ) 1,
        (∫ y in Metric.ball a r, ‖p i y‖ ^ 2) ≤ K * Real.sqrt r) :
    ∃ U : Plane → EuclideanSpace ℝ (Fin m),
      ContinuousOn U (Metric.closedBall 0 (1 / 2)) ∧
      U =ᵐ[volume.restrict (Metric.ball 0 (1 / 2))] u ∧
      ∀ x ∈ Metric.closedBall (0 : Plane) (1 / 2),
        ∀ y ∈ Metric.closedBall (0 : Plane) (1 / 2),
        dist (U x) (U y) ≤ (640 * Real.sqrt Real.pi * Real.sqrt K / Real.pi) *
          Real.sqrt (Real.sqrt (dist x y)) := by
  let r : ℕ → ℝ := fun j => (1 / 16 : ℝ) ^ (j + 1)
  have hr (j : ℕ) : 0 < r j := pow_pos (by norm_num) _
  have hr1 (j : ℕ) : r j ≤ 1 / 16 := by
    dsimp only [r]
    rw [pow_succ]
    exact mul_le_of_le_one_left (by norm_num)
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num))
  have hrs (j : ℕ) : r (j + 1) ≤ r j := by
    change (1 / 16 : ℝ) ^ ((j + 1) + 1) ≤ (1 / 16 : ℝ) ^ (j + 1)
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (by norm_num)
  have hquarter (j : ℕ) : Real.sqrt (Real.sqrt (r j)) = (1 / 2 : ℝ) ^ (j + 1) := by
    have heq : r j = (((1 / 2 : ℝ) ^ (j + 1)) ^ 2) ^ 2 := by
      dsimp only [r]
      calc
        _ = ((1 / 2 : ℝ) ^ 4) ^ (j + 1) := by norm_num
        _ = _ := by simp only [← pow_mul]; congr 1; omega
    rw [heq, Real.sqrt_sq (sq_nonneg _), Real.sqrt_sq (pow_nonneg (by norm_num) _)]
  have hscale (j : ℕ) : Real.sqrt (Real.sqrt (r j)) / r j = (8 : ℝ) ^ (j + 1) := by
    rw [hquarter]
    change (1 / 2 : ℝ) ^ (j + 1) / (1 / 16 : ℝ) ^ (j + 1) = _
    rw [← div_pow]
    norm_num
  let U0 := (Metric.ball (0 : Plane) 2).indicator u
  have hU0 : LocallyIntegrable U0 volume := suDisk_indicator_locallyIntegrable hu
  let v : ℕ → Plane → EuclideanSpace ℝ (Fin m) := fun j =>
    mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] U0
  let C := 64 * Real.sqrt Real.pi * Real.sqrt K / Real.pi
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hv (j : ℕ) : ContDiff ℝ ∞ (v j) :=
    (mollifierEps_compactSupport (hr j)).contDiff_convolution_left (lsmul ℝ ℝ)
      (mollifierEps_smooth (hr j)) hU0
  have hd (j : ℕ) (x : Plane) (hx : x ∈ Metric.closedBall (0 : Plane) (3 / 4)) :
      ‖fderiv ℝ (v j) x‖ ≤ C * (8 : ℝ) ^ j := by
    have h := suMollifier_weak_gradient_bound hu hp hw hK henergy (hr j) (hr1 j) x hx
    change ‖fderiv ℝ (v j) x‖ ≤
      (8 * Real.sqrt Real.pi * Real.sqrt K / Real.pi) *
        Real.sqrt (Real.sqrt (r j)) / r j at h
    rw [mul_div_assoc, hscale, pow_succ] at h
    exact h.trans_eq (by dsimp only [C]; ring)
  have hlip (j : ℕ) (x : Plane) (hx : x ∈ Metric.closedBall (0 : Plane) (3 / 4))
      (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) (3 / 4)) :
      dist (v j x) (v j y) ≤ C * (8 : ℝ) ^ j * dist x y := by
    simpa only [dist_eq_norm] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hv j).differentiable (by simp) z) (hd j) (convex_closedBall _ _) hy hx
  have hstep (j : ℕ) (x : Plane) (hx : x ∈ Metric.closedBall (0 : Plane) (1 / 2)) :
      dist (v j x) (v (j + 1) x) ≤ C * (1 / 2 : ℝ) ^ j := by
    have h := suMollifier_successive_bound hU0 (hr j) (hr (j + 1)) (hrs j) (hr1 j)
      (by positivity : 0 ≤ C * (8 : ℝ) ^ j)
      (by positivity : 0 ≤ C * (8 : ℝ) ^ (j + 1)) (hlip j) (hlip (j + 1)) x hx
    have hprod : (8 : ℝ) ^ j * r j = (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ j := by
      dsimp only [r]
      rw [pow_succ, ← mul_assoc, ← mul_pow]
      norm_num
      ring
    have heq : (C * (8 : ℝ) ^ j + C * (8 : ℝ) ^ (j + 1)) * r j =
        (9 / 16 : ℝ) * C * (1 / 2 : ℝ) ^ j := by
      calc
        _ = 9 * C * ((8 : ℝ) ^ j * r j) := by rw [pow_succ]; ring
        _ = _ := by rw [hprod]; ring
    rw [heq] at h
    exact h.trans (by nlinarith [mul_nonneg hC (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) j)])
  have hhalf : Metric.closedBall (0 : Plane) (1 / 2) ⊆ Metric.closedBall 0 (3 / 4) :=
    Metric.closedBall_subset_closedBall (by norm_num)
  obtain ⟨U, hlim, hcont, -, hholder⟩ := suDyadic_holder_limit hC
    (fun j => (hv j).continuous.continuousOn) hstep
    (fun j x hx y hy => hlip j x (hhalf hx) y (hhalf hy))
  have hrzero : Tendsto r atTop (𝓝 0) := by
    simpa only [r, pow_succ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
        (by norm_num : (1 / 16 : ℝ) < 1)).mul_const (1 / 16)
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := fun j => mollifierBumpEps (hr j)) hrzero
    (Eventually.of_forall fun j =>
      (show r j ≤ 2 * (r j / 2) by linarith)) hU0
  refine ⟨U, hcont, ?_, ?_⟩
  · filter_upwards [hae.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hxlim hx
    have hlim' := hlim.tendsto_at (Metric.ball_subset_closedBall hx)
    change Tendsto (fun j => v j x) atTop (𝓝 (U0 x)) at hxlim
    have heq := tendsto_nhds_unique hlim' hxlim
    exact heq.trans (indicator_of_mem (Metric.ball_subset_ball (by norm_num) hx) u)
  · intro x hx y hy
    have hxy : dist x y ≤ 1 := by
      have hx' := Metric.mem_closedBall.mp hx
      have hy' := Metric.mem_closedBall.mp hy
      have ht := dist_triangle x (0 : Plane) y
      rw [dist_comm (0 : Plane) y] at ht
      linarith
    exact (hholder x hx y hy hxy).trans_eq (by dsimp only [C]; ring)

end PoincareConjecture.M60

end
