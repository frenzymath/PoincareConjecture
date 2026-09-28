import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.FieldEntropy
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.EntropyFunction
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem metric_quadratic_contDiff (g : RiemannianMetric n V) :
    ContDiff ℝ ∞ (fun p : V × V => g.inner p.1 p.2 p.2) :=
  (((contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).comp contDiff_fst).clm_apply
    contDiff_snd).clm_apply contDiff_snd

theorem exists_metric_quadratic_lower_bound (g : RiemannianMetric n V)
    {K : Set V} (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ z : V, c * ‖z‖ ^ 2 ≤ g.inner x z z := by
  let S : Set (V × V) := K ×ˢ Metric.sphere (0 : V) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hp : ∀ p ∈ S, 0 < g.inner p.1 p.2 p.2 := by
    intro p hp
    apply g.pos p.1 p.2
    intro hz
    have hn : ‖p.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp.2
    simp only [hz, norm_zero, zero_ne_one] at hn
  obtain ⟨c, hc, hb⟩ := hS.exists_forall_le'
    (metric_quadratic_contDiff g).continuous.continuousOn hp
  refine ⟨c, hc, ?_⟩
  intro x hx z
  by_cases hz : z = 0
  · simp [hz]
  let w : V := ‖z‖⁻¹ • z
  have hw : w ∈ Metric.sphere (0 : V) 1 := by
    simpa only [w, Metric.mem_sphere, dist_zero_right, RCLike.ofReal_real_eq_id, id_eq] using
      (norm_smul_inv_norm (𝕜 := ℝ) hz)
  have he : ‖z‖ • w = z := smul_inv_smul₀ (norm_ne_zero_iff.mpr hz) z
  have hh : g.inner x z z = ‖z‖ ^ 2 * g.inner x w w := by
    calc
      _ = g.inner x (‖z‖ • w) (‖z‖ • w) := by rw [he]
      _ = _ := by simp only [map_smul, smul_apply, smul_eq_mul]; ring
  rw [hh, mul_comm (‖z‖ ^ 2)]
  exact mul_le_mul_of_nonneg_right (hb (x, w) ⟨hx, hw⟩) (sq_nonneg _)

def metricEntropyLinear (g : RiemannianMetric n V) (η : V → ℝ) (e : V)
    (x : V) : V →L[ℝ] ℝ :=
  η x • ((2 * g.pullbackVolumeDensity id x) • g.euclideanCoefficients x e)

def metricEntropyTest (g : RiemannianMetric n V) (η : V → ℝ) (C : ℝ) (e : V)
    (p : V × V) : ℝ :=
  Real.smoothTransition (g.inner p.1 p.2 p.2 - C) * metricEntropyLinear g η e p.1 p.2

def metricEntropyRemainder (g : RiemannianMetric n V) (η : V → ℝ) (C : ℝ) (e : V)
    (p : V × V) : ℝ :=
  (Real.smoothTransition (g.inner p.1 p.2 p.2 - C) - 1) * metricEntropyLinear g η e p.1 p.2

theorem metricEntropyLinear_contDiff (g : RiemannianMetric n V) {η : V → ℝ}
    (hη : ContDiff ℝ ∞ η) (e : V) : ContDiff ℝ ∞ (metricEntropyLinear g η e) :=
  hη.smul ((contDiff_const.mul (raw_volumeDensity_contDiff g)).smul
    ((contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).clm_apply contDiff_const))

theorem metricEntropyLinear_hasCompactSupport (g : RiemannianMetric n V) {η : V → ℝ}
    (hη : HasCompactSupport η) (e : V) : HasCompactSupport (metricEntropyLinear g η e) :=
  hη.smul_right

theorem metricEntropyTest_contDiff (g : RiemannianMetric n V) {η : V → ℝ}
    (hη : ContDiff ℝ ∞ η) (C : ℝ) (e : V) : ContDiff ℝ ∞ (metricEntropyTest g η C e) :=
  (Real.smoothTransition.contDiff.comp ((metric_quadratic_contDiff g).sub contDiff_const)).mul
    (((metricEntropyLinear_contDiff g hη e).comp contDiff_fst).clm_apply contDiff_snd)

theorem metricEntropyRemainder_contDiff (g : RiemannianMetric n V) {η : V → ℝ}
    (hη : ContDiff ℝ ∞ η) (C : ℝ) (e : V) : ContDiff ℝ ∞ (metricEntropyRemainder g η C e) :=
  ((Real.smoothTransition.contDiff.comp ((metric_quadratic_contDiff g).sub contDiff_const)).sub
    contDiff_const).mul
      (((metricEntropyLinear_contDiff g hη e).comp contDiff_fst).clm_apply contDiff_snd)

theorem metricEntropyTest_zero (g : RiemannianMetric n V) (η : V → ℝ) (C : ℝ) (e x : V) :
    metricEntropyTest g η C e (x, 0) = 0 := by
  simp only [metricEntropyTest, map_zero, mul_zero]

theorem metricEntropyTest_eq_linear_add (g : RiemannianMetric n V)
    (η : V → ℝ) (C : ℝ) (e : V) (p : V × V) :
    metricEntropyTest g η C e p =
      metricEntropyRemainder g η C e p + metricEntropyLinear g η e p.1 p.2 := by
  unfold metricEntropyTest metricEntropyRemainder
  ring

theorem metricEntropyRemainder_hasCompactSupport (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : HasCompactSupport η) (C : ℝ) (e : V) :
    HasCompactSupport (metricEntropyRemainder g η C e) := by
  obtain ⟨c, hc, hb⟩ := exists_metric_quadratic_lower_bound g hη
  let R : ℝ := 1 + (|C| + 1) / c
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [div_nonneg (show 0 ≤ |C| + 1 by positivity) hc.le]
  have hRbound : C + 1 ≤ c * R ^ 2 := by
    have h₁ : |C| + 1 ≤ c * R := by dsimp [R]; field_simp; nlinarith [le_abs_self C]
    have h₂ : c * R ≤ c * R ^ 2 := by nlinarith only [hc, hR, sq_nonneg (R - 1)]
    exact (add_le_add (le_abs_self C) (le_rfl : (1 : ℝ) ≤ 1)).trans (h₁.trans h₂)
  apply (hη.prod (isCompact_closedBall (0 : V) R)).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ ((isClosed_tsupport η).prod Metric.isClosed_closedBall)
  rintro ⟨x, z⟩ hp
  by_contra hn
  apply hp
  by_cases hx : x ∈ tsupport η
  · have hz : R < ‖z‖ := by
      by_contra h
      exact hn ⟨hx, by simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_not_gt h⟩
    have hq : C + 1 ≤ g.inner x z z :=
      hRbound.trans ((mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity : 0 ≤ R) hz.le 2) hc.le).trans (hb x hx z))
    simp only [metricEntropyRemainder,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ g.inner x z z - C),
      sub_self, zero_mul]
  · simp only [metricEntropyRemainder, metricEntropyLinear,
      image_eq_zero_of_notMem_tsupport hx, zero_smul, zero_apply, mul_zero]

end PoincareConjecture.M35.Uniqueness.Heat
