import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Cutoffs
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CompactSlices

noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Filter Set
open scoped ContDiff Topology

namespace Poincare.Parabolic.Interior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E]

def cylinderCutoff (center : E) (r T : ℝ) (p : E × ℝ) : ℝ :=
  rescaledCutoff (unitSpatialBump (E := E)) center r p.1 * timeCutoff T p.2

theorem contDiff_cylinderCutoff (center : E) (r T : ℝ) :
    ContDiff ℝ ∞ (cylinderCutoff center r T) :=
  ((contDiff_rescaledCutoff unitSpatialBump.contDiff center r).comp contDiff_fst).mul
    ((contDiff_timeCutoff T).comp contDiff_snd)

theorem cylinderCutoff_mem_Icc (center : E) (r T : ℝ) (p : E × ℝ) :
    cylinderCutoff center r T p ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hx, hx'⟩ := rescaled_unit_cutoff_mem_Icc center r p.1
  obtain ⟨ht, ht'⟩ := timeCutoff_mem_Icc T p.2
  exact ⟨mul_nonneg hx ht, (mul_le_mul hx' ht' ht (by norm_num)).trans (by norm_num)⟩

theorem cylinderCutoff_zero_time (center x : E) (r : ℝ) {T : ℝ} (hT : 0 < T) :
    cylinderCutoff center r T (x, 0) = 0 := by
  simp [cylinderCutoff, timeCutoff_zero hT]

theorem cylinderCutoff_eventuallyEq_one (center : E) {r T : ℝ}
    (hr : 0 < r) (hT : 0 < T) :
    cylinderCutoff center r T =ᶠ[𝓝 (center, T)] fun _ => 1 := by
  have hx := (rescaled_unit_cutoff_eventuallyEq_one hr center
    (x := center) (by simpa using half_pos hr)).comp_tendsto
    (continuous_fst.tendsto (center, T))
  have ht := (timeCutoff_eventuallyEq_one hT (s := T) (by linarith) le_rfl).comp_tendsto
    (continuous_snd.tendsto (center, T))
  filter_upwards [hx, ht] with p hp hq
  dsimp only [Function.comp_def] at hp hq
  simp [cylinderCutoff, hp, hq]

theorem tsupport_cylinderCutoff_subset (center : E) {r T : ℝ}
    (hr : 0 < r) (hT : 0 < T) :
    tsupport (cylinderCutoff center r T) ⊆
      Metric.closedBall center r ×ˢ Metric.closedBall T T := by
  apply closure_minimal _ (Metric.isClosed_closedBall.prod Metric.isClosed_closedBall)
  intro p hp
  have hs : rescaledCutoff (unitSpatialBump (E := E)) center r p.1 ≠ 0 := by
    intro hz
    exact hp (by simp [cylinderCutoff, hz])
  have ht : timeCutoff T p.2 ≠ 0 := by
    intro hz
    exact hp (by simp [cylinderCutoff, hz])
  exact ⟨tsupport_rescaled_unit_cutoff_subset hr center (subset_closure hs),
    tsupport_rescaled_unit_cutoff_subset hT T (subset_closure ht)⟩

theorem hasCompactSupport_cylinderCutoff [FiniteDimensional ℝ E] (center : E) {r T : ℝ}
    (hr : 0 < r) (hT : 0 < T) : HasCompactSupport (cylinderCutoff center r T) :=
  ((isCompact_closedBall center r).prod (isCompact_closedBall T T)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_cylinderCutoff_subset center hr hT)

theorem spatialDerivative_cylinderCutoff (center x : E) (r T s : ℝ) :
    spatialDerivative (cylinderCutoff center r T) (x, s) =
      timeCutoff T s • fderiv ℝ (rescaledCutoff (unitSpatialBump (E := E)) center r) x := by
  rw [← fderiv_spatialSlice (contDiff_cylinderCutoff center r T)]
  have heq : (fun y => cylinderCutoff center r T (y, s)) =
      fun y => timeCutoff T s • rescaledCutoff (unitSpatialBump (E := E)) center r y := by
    funext y
    simp [cylinderCutoff, mul_comm]
  rw [heq]
  exact fderiv_const_smul
    (((contDiff_rescaledCutoff unitSpatialBump.contDiff center r).differentiable (by simp)) x)
    (timeCutoff T s)

theorem spatialDerivative_spatialDerivative_cylinderCutoff (center x : E) (r T s : ℝ) :
    spatialDerivative (spatialDerivative (cylinderCutoff center r T)) (x, s) =
      timeCutoff T s •
        fderiv ℝ (fderiv ℝ (rescaledCutoff (unitSpatialBump (E := E)) center r)) x := by
  rw [← fderiv_spatialSlice (contDiff_spatialDerivative (contDiff_cylinderCutoff center r T))]
  simp only [spatialDerivative_cylinderCutoff]
  exact fderiv_const_smul
    ((((contDiff_rescaledCutoff unitSpatialBump.contDiff center r).fderiv_right
      (by simp : ∞ + 1 ≤ (∞ : WithTop ℕ∞))).differentiable (by simp)) x) (timeCutoff T s)

theorem timeDerivative_cylinderCutoff (center x : E) (r T s : ℝ) :
    timeDerivative (cylinderCutoff center r T) (x, s) =
      rescaledCutoff (unitSpatialBump (E := E)) center r x * deriv (timeCutoff T) s := by
  have h := hasDerivAt_timeSlice ((contDiff_cylinderCutoff center r T).differentiable (by simp)) x s
  have hd := (((contDiff_timeCutoff T).differentiable (by simp)) s).hasDerivAt.const_mul
    (rescaledCutoff (unitSpatialBump (E := E)) center r x)
  exact h.unique hd

theorem norm_spatialDerivative_cylinderCutoff_le {C r : ℝ} (hr : 0 < r)
    (hb : ∀ x : E, ‖fderiv ℝ (unitSpatialBump (E := E) : E → ℝ) x‖ ≤ C)
    (center x : E) (T s : ℝ) :
    ‖spatialDerivative (cylinderCutoff center r T) (x, s)‖ ≤ C / r := by
  rw [spatialDerivative_cylinderCutoff, norm_smul,
    Real.norm_of_nonneg (timeCutoff_mem_Icc T s).1]
  calc
    _ ≤ 1 * (C / r) := mul_le_mul (timeCutoff_mem_Icc T s).2
      (norm_fderiv_rescaledCutoff_le unitSpatialBump.contDiff hr hb center x)
      (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem norm_spatialDerivative_spatialDerivative_cylinderCutoff_le {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 < r)
    (hb : ∀ x : E, ‖fderiv ℝ (fderiv ℝ (unitSpatialBump (E := E) : E → ℝ)) x‖ ≤ C)
    (center x : E) (T s : ℝ) :
    ‖spatialDerivative (spatialDerivative (cylinderCutoff center r T)) (x, s)‖ ≤ C / r ^ 2 := by
  rw [spatialDerivative_spatialDerivative_cylinderCutoff, norm_smul,
    Real.norm_of_nonneg (timeCutoff_mem_Icc T s).1]
  calc
    _ ≤ 1 * (C / r ^ 2) := mul_le_mul (timeCutoff_mem_Icc T s).2
      (norm_fderiv_fderiv_rescaledCutoff_le unitSpatialBump.contDiff hC hr hb center x)
      (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem norm_timeDerivative_cylinderCutoff_le {C T : ℝ} (hT : 0 < T)
    (hb : ∀ s : ℝ, ‖fderiv ℝ (unitSpatialBump (E := ℝ) : ℝ → ℝ) s‖ ≤ C)
    (center x : E) (r s : ℝ) :
    ‖timeDerivative (cylinderCutoff center r T) (x, s)‖ ≤ C / T := by
  rw [timeDerivative_cylinderCutoff, norm_mul,
    Real.norm_of_nonneg (rescaled_unit_cutoff_mem_Icc center r x).1]
  calc
    _ ≤ 1 * (C / T) := mul_le_mul (rescaled_unit_cutoff_mem_Icc center r x).2
      (norm_deriv_timeCutoff_le hT hb s) (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem timeDerivative_cylinderCutoff_eq_zero (center x : E) (r : ℝ) {T s : ℝ}
    (hT : 0 < T) (hs : T / 2 < s) (hsT : s ≤ T) :
    timeDerivative (cylinderCutoff center r T) (x, s) = 0 := by
  rw [timeDerivative_cylinderCutoff, deriv_timeCutoff_eq_zero hT hs hsT, mul_zero]

theorem rescaled_unit_cutoff_eventuallyEq_zero (center : E) {r : ℝ} (hr : 0 < r)
    {x : E} (hx : r < ‖x - center‖) :
    rescaledCutoff (unitSpatialBump (E := E)) center r =ᶠ[𝓝 x] fun _ => 0 := by
  have h := ((continuous_id.sub continuous_const).norm.continuousAt (x := x)).eventually
    (eventually_gt_nhds hx)
  filter_upwards [h] with y hy
  exact rescaled_unit_cutoff_eq_zero hr center y hy.le

theorem spatialDerivative_cylinderCutoff_eq_zero (center : E) {r : ℝ} (hr : 0 < r)
    {x : E} (hx : r < ‖x - center‖) (T s : ℝ) :
    spatialDerivative (cylinderCutoff center r T) (x, s) = 0 := by
  rw [spatialDerivative_cylinderCutoff,
    (rescaled_unit_cutoff_eventuallyEq_zero center hr hx).fderiv_eq]
  simp

theorem spatialDerivative_spatialDerivative_cylinderCutoff_eq_zero (center : E)
    {r : ℝ} (hr : 0 < r) {x : E} (hx : r < ‖x - center‖) (T s : ℝ) :
    spatialDerivative (spatialDerivative (cylinderCutoff center r T)) (x, s) = 0 := by
  rw [spatialDerivative_spatialDerivative_cylinderCutoff,
    ((rescaled_unit_cutoff_eventuallyEq_zero center hr hx).fderiv).fderiv_eq]
  simp

theorem spatialDerivative_cylinderCutoff_eq_zero_of_mem_half_ball (center : E)
    {r : ℝ} (hr : 0 < r) {x : E} (hx : ‖x - center‖ < r / 2) (T s : ℝ) :
    spatialDerivative (cylinderCutoff center r T) (x, s) = 0 := by
  rw [spatialDerivative_cylinderCutoff,
    (rescaled_unit_cutoff_eventuallyEq_one hr center hx).fderiv_eq]
  simp

theorem spatialDerivative_spatialDerivative_cylinderCutoff_eq_zero_of_mem_half_ball
    (center : E) {r : ℝ} (hr : 0 < r) {x : E}
    (hx : ‖x - center‖ < r / 2) (T s : ℝ) :
    spatialDerivative (spatialDerivative (cylinderCutoff center r T)) (x, s) = 0 := by
  rw [spatialDerivative_spatialDerivative_cylinderCutoff,
    ((rescaled_unit_cutoff_eventuallyEq_one hr center hx).fderiv).fderiv_eq]
  simp

theorem cylinderCutoff_eventuallyEq_one_of_mem (center : E) {r T s : ℝ}
    (hr : 0 < r) (hT : 0 < T) {x : E} (hx : ‖x - center‖ < r / 2)
    (hs : T / 2 < s) (hsT : s ≤ T) :
    cylinderCutoff center r T =ᶠ[𝓝 (x, s)] fun _ => 1 := by
  have hspace := (rescaled_unit_cutoff_eventuallyEq_one hr center hx).comp_tendsto
    (continuous_fst.tendsto (x, s))
  have htime := (timeCutoff_eventuallyEq_one hT hs hsT).comp_tendsto
    (continuous_snd.tendsto (x, s))
  filter_upwards [hspace, htime] with p hp hq
  dsimp only [Function.comp_def] at hp hq
  simp [cylinderCutoff, hp, hq]

end Poincare.Parabolic.Interior
