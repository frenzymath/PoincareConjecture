import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryLiftAlgebra
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.UnrestrictedLabels
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false

open Set Function Filter
open scoped Topology ContDiff NNReal

namespace PoincareConjecture.M64

theorem smooth_periodic_target_variation
    {theta : ℝ → ℝ} (hregular : ContDiff ℝ ∞ theta)
    (hperiod : Function.Periodic theta curvePeriod) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, |t| < delta →
      ∃ T : M64PeriodicDegreeOneLift,
        (∀ x, T.map x = x + t * theta x) ∧ StrictMono T.map ∧
        Surjective T.map ∧ ContDiff ℝ ∞ T.map ∧ ∀ x, 0 < deriv T.map x := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hd := hregular.differentiable (by simp)
  have hdperiod : Function.Periodic (deriv theta) curvePeriod := by
    intro x
    have heq : (fun y => theta (y + curvePeriod)) = theta := funext hperiod
    have he := congrArg (fun f : ℝ → ℝ => deriv f x) heq
    simpa only [deriv_comp_add_const] using he
  have hnperiod : Function.Periodic (fun x => ‖deriv theta x‖) curvePeriod :=
    fun x => congrArg norm (hdperiod x)
  obtain ⟨B, hB⟩ :=
    (hnperiod.compact_of_continuous hP.ne'
      (hregular.continuous_deriv (by simp)).norm).bddAbove
  let C : ℝ≥0 := ⟨max B 0 + 1, by positivity⟩
  have hC : (0 : ℝ) < C := by
    change 0 < max B 0 + 1
    linarith [le_max_right B 0]
  have hderiv (x : ℝ) : ‖deriv theta x‖ ≤ C :=
    (hB (mem_range_self x)).trans (by
      change B ≤ max B 0 + 1
      linarith [le_max_left B 0])
  have hLip : LipschitzWith C theta := lipschitzWith_of_nnnorm_deriv_le hd
    (fun x => by exact_mod_cast hderiv x)
  refine ⟨1 / ((C : ℝ) + 1), by positivity, ?_⟩
  intro t ht
  have htC : |t| * (C : ℝ) < 1 := by
    have hh := (lt_div_iff₀ (show (0 : ℝ) < C + 1 by positivity)).mp ht
    nlinarith [abs_nonneg t]
  let f : ℝ → ℝ := fun x => x + t * theta x
  have hf : ContDiff ℝ ∞ f := contDiff_id.add (contDiff_const.mul hregular)
  have hstrict : StrictMono f := by
    intro x y hxy
    have htheta : |theta y - theta x| ≤ (C : ℝ) * (y - x) := by
      have hh := hLip.dist_le_mul y x
      simpa only [Real.dist_eq, abs_of_pos (sub_pos.mpr hxy)] using hh
    have hprod : |t * (theta y - theta x)| ≤ |t| * (C : ℝ) * (y - x) := by
      rw [abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left htheta (abs_nonneg t)
    have hneg := (abs_le.mp hprod).1
    have hgap := mul_pos (sub_pos.mpr htC) (sub_pos.mpr hxy)
    change x + t * theta x < y + t * theta y
    nlinarith
  let V := (LipschitzDegreeOneLabel.ofMonotone M64PeriodicDegreeOneLift.identity).addPeriodic
    theta hperiod hLip t
  let T : M64PeriodicDegreeOneLift := {
    map := f
    monotone := hstrict.monotone
    period_shift := by intro x; dsimp [f]; rw [hperiod x]; ring
    lipschitz_constant := V.constant
    lipschitz_nonnegative := V.constant.coe_nonneg
    lipschitz_on := fun x y => by
      simpa only [V, LipschitzDegreeOneLabel.addPeriodic,
        LipschitzDegreeOneLabel.ofMonotone, M64PeriodicDegreeOneLift.identity,
        id_eq, f, Real.dist_eq] using V.lipschitz.dist_le_mul x y }
  have hint (k : ℤ) : f ((k : ℝ) * curvePeriod) =
      (k : ℝ) * curvePeriod + t * theta 0 := by
    simp only [f, hperiod.int_mul_eq k]
  have hsurj : Surjective f := by
    intro y
    let k : ℤ := ⌊(y - t * theta 0) / curvePeriod⌋
    have hlo : (k : ℝ) * curvePeriod ≤ y - t * theta 0 :=
      (le_div_iff₀ hP).mp (Int.floor_le _)
    have hhi : y - t * theta 0 < ((k : ℝ) + 1) * curvePeriod :=
      (div_lt_iff₀ hP).mp (Int.lt_floor_add_one _)
    apply intermediate_value_univ ((k : ℝ) * curvePeriod)
      (((k + 1 : ℤ) : ℝ) * curvePeriod) hf.continuous
    rw [hint k, hint (k + 1)]
    norm_cast at hhi ⊢
    constructor <;> linarith
  refine ⟨T, fun _ => rfl, hstrict, hsurj, hf, ?_⟩
  intro x
  have hfd : HasDerivAt f (1 + t * deriv theta x) x :=
    (hasDerivAt_id x).add ((hd x).hasDerivAt.const_mul t)
  change 0 < deriv f x
  rw [hfd.deriv]
  have hb : |t * deriv theta x| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hderiv x)
      (abs_nonneg t)).trans_lt htC
  linarith [(abs_lt.mp hb).1]

theorem smooth_periodic_target_variation_preserves_labels
    {theta : ℝ → ℝ} (hregular : ContDiff ℝ ∞ theta)
    (hperiod : Function.Periodic theta curvePeriod) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, |t| < delta →
      ∀ sigma : M64PeriodicDegreeOneLift,
        ∃ S : M64PeriodicDegreeOneLift,
          ∀ x, S.map x = sigma.map x + t * theta (sigma.map x) := by
  obtain ⟨delta, hdelta, hvar⟩ := smooth_periodic_target_variation hregular hperiod
  refine ⟨delta, hdelta, ?_⟩
  intro t ht sigma
  obtain ⟨T, hT, -⟩ := hvar t ht
  exact ⟨T.comp sigma, fun x => hT (sigma.map x)⟩

theorem monotone_label_variation_velocity_eq_on_fiber
    {v : ℝ → ℝ → ℝ} {x y vx vy : ℝ} (hxy : x ≤ y)
    (hmono : ∀ᶠ t : ℝ in 𝓝 0, Monotone (v t))
    (hcenter : v 0 x = v 0 y)
    (hx : HasDerivAt (fun t => v t x) vx 0)
    (hy : HasDerivAt (fun t => v t y) vy 0) : vx = vy := by
  have hmin : IsLocalMin (fun t => v t y - v t x) 0 := by
    filter_upwards [hmono] with t ht
    simpa only [hcenter, sub_self] using sub_nonneg.mpr (ht hxy)
  exact (sub_eq_zero.mp (hmin.hasDerivAt_eq_zero (hy.sub hx))).symm

end PoincareConjecture.M64
