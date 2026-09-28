import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set Filter MeasureTheory intervalIntegral Metric
open scoped Topology ContDiff

noncomputable section

namespace PoincareConjecture.CoordinateExponential

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def radialWeightedIntegral (k : ℕ) (f : E → F) (x : E) : F :=
  ∫ t in (0 : ℝ)..1, t ^ k • f (t • x)

omit [CompleteSpace F] in
theorem norm_radialWeightedIntegral_le (k : ℕ) {f : E → F} {x : E} {C : ℝ}
    (_hC : 0 ≤ C) (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (t • x)‖ ≤ C) :
    ‖radialWeightedIntegral k f x‖ ≤ C / (k + 1) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (f := fun t => t ^ k • f (t • x))
    (g := fun t : ℝ => t ^ k * C) (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (by
      filter_upwards [] with t ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1.le k)]
      exact mul_le_mul_of_nonneg_left (hbound t ⟨ht.1.le, ht.2⟩) (pow_nonneg ht.1.le k))
    (((continuous_id.pow k).mul_const C).intervalIntegrable 0 1)
  simpa [radialWeightedIntegral, intervalIntegral.integral_mul_const, integral_pow, div_eq_mul_inv,
    mul_comm] using h

omit [CompleteSpace F] in
theorem hasFDerivAt_radialWeightedIntegral [FiniteDimensional ℝ E]
    (k : ℕ) {f : E → F} {r : ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball 0 r)) {x : E}
    (hx : x ∈ Metric.ball 0 r) :
    HasFDerivAt (radialWeightedIntegral k f)
      (radialWeightedIntegral (k + 1) (fderiv ℝ f) x) x := by
  have hxr : ‖x‖ < r := by simpa using hx
  obtain ⟨a, hxa, har⟩ := exists_between hxr
  have ha : 0 < a := (norm_nonneg x).trans_lt hxa
  have hseg {y : E} (hy : ‖y‖ ≤ a) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      t • y ∈ Metric.closedBall 0 a := by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left hy ht.1).trans
      ((mul_le_mul_of_nonneg_right ht.2 ha.le).trans_eq (one_mul a))
  have hsub : Metric.closedBall (0 : E) a ⊆ Metric.ball 0 r :=
    Metric.closedBall_subset_ball har
  have hDf := hf.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : E) a).exists_bound_of_continuousOn
    (hDf.mono hsub)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans
    (hD 0 (by simpa using ha.le))
  have hcont (y : E) (hy : ‖y‖ ≤ a) :
      ContinuousOn (fun t : ℝ => f (t • y)) (Icc 0 1) :=
    hf.continuousOn.comp (continuous_id.smul continuous_const).continuousOn
      (fun t ht => hsub (hseg hy ht))
  have hcontD (y : E) (hy : ‖y‖ ≤ a) :
      ContinuousOn (fun t : ℝ => fderiv ℝ f (t • y)) (Icc 0 1) :=
    hDf.comp (continuous_id.smul continuous_const).continuousOn
      (fun t ht => hsub (hseg hy ht))
  have hint (y : E) (hy : ‖y‖ ≤ a) :
      IntervalIntegrable (fun t : ℝ => t ^ k • f (t • y)) volume 0 1 :=
    (((continuous_id.pow k).continuousOn).smul (hcont y hy)).intervalIntegrable_of_Icc
      (by norm_num)
  have hintD : IntervalIntegrable
      (fun t : ℝ => t ^ (k + 1) • fderiv ℝ f (t • x)) volume 0 1 :=
    (((continuous_id.pow (k + 1)).continuousOn).smul (hcontD x hxa.le)).intervalIntegrable_of_Icc
      (by norm_num)
  have hs : Metric.ball (0 : E) a ∈ 𝓝 x := isOpen_ball.mem_nhds (by simpa using hxa)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (s := Metric.ball (0 : E) a)
    (bound := fun _ => D) hs
  · filter_upwards [hs] with y hy
    exact (hint y (by simpa using (Metric.mem_ball.mp hy).le)).aestronglyMeasurable_restrict_uIoc
  · exact hint x hxa.le
  · exact hintD.aestronglyMeasurable_restrict_uIoc
  · rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [] with t ht y hy
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      have ht0 : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
      exact Ioc_subset_Icc_self ht0
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht'.1 _)]
    have hy' : ‖y‖ ≤ a := by simpa using (Metric.mem_ball.mp hy).le
    exact (mul_le_mul_of_nonneg_left (hD _ (hseg hy' ht')) (pow_nonneg ht'.1 _)).trans
      ((mul_le_mul_of_nonneg_right (pow_le_one₀ ht'.1 ht'.2) hD0).trans_eq (one_mul D))
  · exact intervalIntegrable_const
  · rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [] with t ht y hy
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      have ht0 : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
      exact Ioc_subset_Icc_self ht0
    have hy' : ‖y‖ ≤ a := by simpa using (Metric.mem_ball.mp hy).le
    have hfy := (hf.differentiableOn (by simp) _ (hsub (hseg hy' ht'))).differentiableAt
      (isOpen_ball.mem_nhds (hsub (hseg hy' ht')))
    convert (hfy.hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul t)).const_smul (t ^ k)
      using 1 <;> try rfl
    ext z
    simp [pow_succ, mul_smul]

section HigherDerivatives

variable [FiniteDimensional ℝ E] {G : Type u}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem contDiffOn_radialWeightedIntegral (k : ℕ) {f : E → G} {r : ℝ}
    (hf : ContDiffOn ℝ ∞ f (ball 0 r)) :
    ContDiffOn ℝ ∞ (radialWeightedIntegral k f) (ball 0 r) := by
  suffices h : ∀ n : ℕ, ∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
      [CompleteSpace G], ∀ (k : ℕ) (f : E → G),
      ContDiffOn ℝ ∞ f (ball 0 r) →
        ContDiffOn ℝ n (radialWeightedIntegral k f) (ball 0 r) by
    exact contDiffOn_infty.mpr (fun n => h n G k f hf)
  intro n
  induction n with
  | zero =>
    intro G _ _ _ k f hf
    rw [Nat.cast_zero, contDiffOn_zero]
    intro x hx
    exact (hasFDerivAt_radialWeightedIntegral k (hf.of_le (by simp)) hx).continuousAt.continuousWithinAt
  | succ n ih =>
    intro G _ _ _ k f hf
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    refine ⟨fun x hx =>
      (hasFDerivAt_radialWeightedIntegral k (hf.of_le (by simp)) hx).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) (ball 0 r) :=
      (contDiffOn_infty_iff_fderiv_of_isOpen isOpen_ball).mp hf |>.2
    exact (ih (E →L[ℝ] G) (k + 1) (fderiv ℝ f) hDf).congr
      (fun x hx => (hasFDerivAt_radialWeightedIntegral k (hf.of_le (by simp)) hx).fderiv)

theorem norm_iteratedFDeriv_radialWeightedIntegral_le
    (m k : ℕ) {f : E → G} {r C : ℝ}
    (hf : ContDiffOn ℝ ∞ f (ball 0 r)) {x : E} (hx : x ∈ ball 0 r)
    (hC : 0 ≤ C) (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ m f (t • x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (radialWeightedIntegral k f) x‖ ≤ C / (k + m + 1) := by
  induction m generalizing G k with
  | zero =>
    simpa only [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero] using
      norm_radialWeightedIntegral_le k hC
        (fun t ht => by simpa only [norm_iteratedFDeriv_zero] using hbound t ht)
  | succ m ih =>
    have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) (ball 0 r) :=
      (contDiffOn_infty_iff_fderiv_of_isOpen isOpen_ball).mp hf |>.2
    have heq : fderiv ℝ (radialWeightedIntegral k f) =ᶠ[𝓝 x]
        radialWeightedIntegral (k + 1) (fderiv ℝ f) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hasFDerivAt_radialWeightedIntegral k (hf.of_le (by simp)) hy).fderiv
    rw [← norm_iteratedFDeriv_fderiv,
      (heq.iteratedFDeriv ℝ m).eq_of_nhds]
    have h := ih (k + 1) hDf (fun t ht => by
      rw [norm_iteratedFDeriv_fderiv]
      exact hbound t ht)
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using h

end HigherDerivatives

end PoincareConjecture.CoordinateExponential
