import PoincareConjecture.Proofs.Horizon.Analysis.Heat.GaussianEvolution
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ContDiff

namespace Poincare.Analysis.Heat

theorem integrable_lipschitz_gaussianReal {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (m : ℝ) (v : ℝ≥0) : Integrable f (gaussianReal m v) := by
  have hi : Integrable (fun z : ℝ ↦ |z|) (gaussianReal m v) := by
    simpa only [id_eq, Real.norm_eq_abs] using
      (memLp_id_gaussianReal (μ := m) (v := v) 1).integrable (by norm_num) |>.norm
  apply ((integrable_const |f 0|).add (hi.const_mul (L : ℝ))).mono'
    hf.continuous.aestronglyMeasurable
  filter_upwards [] with z
  have h := hf.dist_le_mul z 0
  simp only [Real.dist_eq, sub_zero] at h
  have htri := abs_add_le (f 0) (f z - f 0)
  simp only [add_sub_cancel] at htri
  exact htri.trans (add_le_add_right h _)

theorem gaussianAverage_eq_integral_gaussianReal {f : ℝ → ℝ}
    (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    gaussianAverage f t x = ∫ z, f (x + z) ∂gaussianReal 0 ⟨2 * t, by positivity⟩ := by
  have hmap : (gaussianReal 0 1).map (fun z ↦ Real.sqrt (2 * t) * z) =
      gaussianReal 0 ⟨2 * t, by positivity⟩ := by
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    congr 1
    apply Subtype.ext
    exact Real.sq_sqrt (by positivity)
  have hc : Continuous (fun z ↦ f (x + z)) := hf.comp (by fun_prop)
  rw [← hmap, integral_map (by fun_prop) hc.aestronglyMeasurable]
  rfl

theorem gaussianAverage_semigroup {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : ℝ) :
    gaussianAverage (gaussianAverage f t) s x = gaussianAverage f (s + t) x := by
  let vs : ℝ≥0 := ⟨2 * s, by positivity⟩
  let vt : ℝ≥0 := ⟨2 * t, by positivity⟩
  have hfc : LipschitzWith L (fun z ↦ f (x + z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [Real.dist_eq, add_sub_add_left_eq_sub] using hf.dist_le_mul (x + z) (x + w)
  have hi : Integrable (fun z ↦ f (x + z)) ((gaussianReal 0 vs) ∗ (gaussianReal 0 vt)) := by
    rw [gaussianReal_conv_gaussianReal]
    exact integrable_lipschitz_gaussianReal hfc _ _
  calc
    gaussianAverage (gaussianAverage f t) s x =
        ∫ z, gaussianAverage f t (x + z) ∂gaussianReal 0 vs :=
      gaussianAverage_eq_integral_gaussianReal (lipschitzWith_gaussianAverage hf t).continuous hs x
    _ = ∫ z, ∫ w, f (x + (z + w)) ∂gaussianReal 0 vt ∂gaussianReal 0 vs := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [gaussianAverage_eq_integral_gaussianReal hf.continuous ht]
      simp only [add_assoc, vt]
    _ = ∫ z, f (x + z) ∂((gaussianReal 0 vs) ∗ (gaussianReal 0 vt)) := (integral_conv hi).symm
    _ = gaussianAverage f (s + t) x := by
      rw [gaussianReal_conv_gaussianReal, zero_add,
        gaussianAverage_eq_integral_gaussianReal hf.continuous (add_nonneg hs ht)]
      congr 2
      apply Subtype.ext
      change 2 * s + 2 * t = 2 * (s + t)
      ring

theorem contDiff_gaussianAverage {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hdf : Differentiable ℝ f)
    {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (gaussianAverage f t) := by
  have hn (n : ℕ) : ∀ {L : ℝ≥0} {f : ℝ → ℝ}, LipschitzWith L f →
      Differentiable ℝ f → ∀ {t : ℝ}, 0 < t → ContDiff ℝ n (gaussianAverage f t) := by
    intro L f hf hdf t ht
    induction n generalizing L f t with
    | zero => exact contDiff_zero.mpr (lipschitzWith_gaussianAverage hf t).continuous
    | succ n ih =>
      have hh : 0 < t / 2 := by positivity
      have hd : Differentiable ℝ (gaussianAverage f (t / 2)) :=
        fun x ↦ (hasDerivAt_gaussianAverage hf hdf _ x).differentiableAt
      have hdd : Differentiable ℝ (deriv (gaussianAverage f (t / 2))) :=
        fun x ↦ (hasDerivAt_gaussianAverage_twice hf hdf hh x).differentiableAt
      have heq : deriv (gaussianAverage f t) =
          gaussianAverage (deriv (gaussianAverage f (t / 2))) (t / 2) := by
        have hsplit : gaussianAverage f t =
            gaussianAverage (gaussianAverage f (t / 2)) (t / 2) := by
          funext x
          rw [gaussianAverage_semigroup hf hh.le hh.le, add_halves]
        rw [hsplit]
        funext x
        exact (hasDerivAt_gaussianAverage (lipschitzWith_gaussianAverage hf _) hd _ x).deriv
      rw [Nat.cast_add, Nat.cast_one]
      apply contDiff_succ_iff_deriv.mpr
      refine ⟨fun x ↦ (hasDerivAt_gaussianAverage hf hdf t x).differentiableAt, ?_, ?_⟩
      · simp
      · rw [heq]
        exact ih (lipschitzWith_deriv_gaussianAverage hf hdf hh) hdd hh
  exact contDiff_infty.mpr fun n ↦ hn n hf hdf ht

theorem exists_lipschitzWith_iterate_deriv_gaussianAverage (k : ℕ)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) (hdf : Differentiable ℝ f)
    {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ≥0, LipschitzWith C (deriv^[k] (gaussianAverage f t)) := by
  induction k generalizing L f t with
  | zero => exact ⟨L, lipschitzWith_gaussianAverage hf t⟩
  | succ k ih =>
    have hh : 0 < t / 2 := by positivity
    have hd : Differentiable ℝ (gaussianAverage f (t / 2)) :=
      fun x ↦ (hasDerivAt_gaussianAverage hf hdf _ x).differentiableAt
    have hdd : Differentiable ℝ (deriv (gaussianAverage f (t / 2))) :=
      fun x ↦ (hasDerivAt_gaussianAverage_twice hf hdf hh x).differentiableAt
    have heq : deriv (gaussianAverage f t) =
        gaussianAverage (deriv (gaussianAverage f (t / 2))) (t / 2) := by
      have hsplit : gaussianAverage f t =
          gaussianAverage (gaussianAverage f (t / 2)) (t / 2) := by
        funext x
        rw [gaussianAverage_semigroup hf hh.le hh.le, add_halves]
      rw [hsplit]
      funext x
      exact (hasDerivAt_gaussianAverage (lipschitzWith_gaussianAverage hf _) hd _ x).deriv
    rw [Function.iterate_succ_apply, heq]
    exact ih (lipschitzWith_deriv_gaussianAverage hf hdf hh) hdd hh

end Poincare.Analysis.Heat
