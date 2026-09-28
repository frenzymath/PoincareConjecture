import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyHolderAverages
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyHolderDyadic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Topology Convolution

namespace PoincareConjecture

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak M60

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem m64Morrey_holder_representative {m : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
    (hu : MemLp u 2 (volume.restrict (Metric.ball 0 2)))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball 0 2)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun y => p i y b) (fun y => u y b)
      (Metric.ball 0 2)) {K beta : ℝ} (hK : 0 ≤ K) (hbeta : 0 < beta)
    (henergy : ∀ i : Fin 2, ∀ a ∈ Metric.closedBall (0 : Plane) 1,
      ∀ r ∈ Ioc (0 : ℝ) 1,
        (∫ y in Metric.ball a r, ‖p i y‖ ^ 2) ≤ K * r ^ beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ U : Plane → EuclideanSpace ℝ (Fin m),
      ContinuousOn U (Metric.closedBall 0 (1 / 2)) ∧
      U =ᵐ[volume.restrict (Metric.ball 0 (1 / 2))] u ∧
      ∀ x ∈ Metric.closedBall (0 : Plane) (1 / 2),
        ∀ y ∈ Metric.closedBall (0 : Plane) (1 / 2),
        dist (U x) (U y) ≤ C * (dist x y) ^ (beta / 2) := by
  let alpha := beta / 2
  have halpha : 0 < alpha := half_pos hbeta
  let q : ℝ := (1 / 16 : ℝ) ^ alpha
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 16) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) halpha
  let b : ℝ := 16 * q
  have hb : 0 ≤ b := by dsimp only [b]; positivity
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
  have hpower (j : ℕ) : (r j) ^ alpha = q ^ (j + 1) :=
    (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 16) alpha (j + 1)).symm
  have hscale (j : ℕ) : (r j) ^ alpha / r j = b ^ (j + 1) := by
    rw [hpower]
    change q ^ (j + 1) / (1 / 16 : ℝ) ^ (j + 1) = _
    rw [← div_pow]
    congr 1
    dsimp only [b]
    ring
  let U0 := (Metric.ball (0 : Plane) 2).indicator u
  have hU0 : LocallyIntegrable U0 volume := suDisk_indicator_locallyIntegrable hu
  let v : ℕ → Plane → EuclideanSpace ℝ (Fin m) := fun j =>
    mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] U0
  let D := 8 * Real.sqrt Real.pi * Real.sqrt K / Real.pi
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let C0 := D * b
  have hC0 : 0 ≤ C0 := mul_nonneg hD hb
  have hv (j : ℕ) : ContDiff ℝ ∞ (v j) :=
    (mollifierEps_compactSupport (hr j)).contDiff_convolution_left (lsmul ℝ ℝ)
      (mollifierEps_smooth (hr j)) hU0
  have hd (j : ℕ) (x : Plane) (hx : x ∈ Metric.closedBall (0 : Plane) (3 / 4)) :
      ‖fderiv ℝ (v j) x‖ ≤ C0 * b ^ j := by
    have hh := m64Morrey_mollifier_gradient_bound hu hp hw hK henergy
      (hr j) (hr1 j) x hx
    change ‖fderiv ℝ (v j) x‖ ≤ D * (r j) ^ alpha / r j at hh
    rw [mul_div_assoc, hscale, pow_succ] at hh
    exact hh.trans_eq (by dsimp only [C0]; ring)
  have hlip (j : ℕ) (x : Plane) (hx : x ∈ Metric.closedBall (0 : Plane) (3 / 4))
      (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) (3 / 4)) :
      dist (v j x) (v j y) ≤ C0 * b ^ j * dist x y := by
    simpa only [dist_eq_norm] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hv j).differentiable (by simp) z) (hd j) (convex_closedBall _ _) hy hx
  have hstep (j : ℕ) (x : Plane) (hx : x ∈ Metric.closedBall (0 : Plane) (1 / 2)) :
      dist (v j x) (v (j + 1) x) ≤ 2 * C0 * q ^ j := by
    have hh := suMollifier_successive_bound hU0 (hr j) (hr (j + 1)) (hrs j) (hr1 j)
      (by positivity : 0 ≤ C0 * b ^ j) (by positivity : 0 ≤ C0 * b ^ (j + 1))
      (hlip j) (hlip (j + 1)) x hx
    have hprod : b ^ j * r j = (1 / 16 : ℝ) * q ^ j := by
      dsimp only [r]
      rw [pow_succ, ← mul_assoc, ← mul_pow]
      have hmul : b * (1 / 16 : ℝ) = q := by dsimp only [b]; ring
      rw [hmul]
      ring
    have heq : (C0 * b ^ j + C0 * b ^ (j + 1)) * r j =
        (1 / 16 + q) * C0 * q ^ j := by
      calc
        _ = C0 * (1 + b) * (b ^ j * r j) := by rw [pow_succ]; ring
        _ = _ := by rw [hprod]; dsimp only [b]; ring
    rw [heq] at hh
    exact hh.trans (by nlinarith [mul_nonneg hC0 (pow_nonneg hq.le j)])
  have hhalf : Metric.closedBall (0 : Plane) (1 / 2) ⊆ Metric.closedBall 0 (3 / 4) :=
    Metric.closedBall_subset_closedBall (by norm_num)
  have hlip' (j : ℕ) (x : Plane) (hx : x ∈ Metric.closedBall (0 : Plane) (1 / 2))
      (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) (1 / 2)) :
      dist (v j x) (v j y) ≤ (2 * C0) * (16 * (1 / 16 : ℝ) ^ alpha) ^ j * dist x y := by
    exact (hlip j x (hhalf hx) y (hhalf hy)).trans (by
      change C0 * b ^ j * dist x y ≤ 2 * C0 * b ^ j * dist x y
      nlinarith [mul_nonneg (mul_nonneg hC0 (pow_nonneg hb j)) (dist_nonneg (x := x) (y := y))])
  obtain ⟨U, hlim, hcont, -, hholder⟩ := m64Morrey_dyadic_holder_limit
    (by positivity : 0 ≤ 2 * C0) halpha (fun j => (hv j).continuous.continuousOn)
    hstep hlip'
  have hrzero : Tendsto r atTop (𝓝 0) := by
    simpa only [r, pow_succ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
        (by norm_num : (1 / 16 : ℝ) < 1)).mul_const (1 / 16)
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := fun j => mollifierBumpEps (hr j)) hrzero
    (Eventually.of_forall fun j => (show r j ≤ 2 * (r j / 2) by linarith)) hU0
  refine ⟨(2 * (2 * C0) / (1 - q) + 2 * C0) / q, by positivity, U, hcont, ?_, ?_⟩
  · filter_upwards [hae.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hxlim hx
    have hlim' := hlim.tendsto_at (Metric.ball_subset_closedBall hx)
    change Tendsto (fun j => v j x) atTop (𝓝 (U0 x)) at hxlim
    exact (tendsto_nhds_unique hlim' hxlim).trans
      (indicator_of_mem (Metric.ball_subset_ball (by norm_num) hx) u)
  · intro x hx y hy
    have hxy : dist x y ≤ 1 := by
      have hx' := Metric.mem_closedBall.mp hx
      have hy' := Metric.mem_closedBall.mp hy
      have ht := dist_triangle x (0 : Plane) y
      rw [dist_comm (0 : Plane) y] at ht
      linarith
    exact hholder x hx y hy hxy

end PoincareConjecture
