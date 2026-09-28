import PoincareConjecture.Proofs.Horizon.Analysis.Heat.GaussianSemigroup
import Mathlib.Analysis.Normed.Operator.Prod








set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ContDiff

namespace Poincare.Analysis.Heat

private noncomputable def weightedAverage (m : ℕ) (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ z, z ^ m * f (p.2 + p.1 * z) ∂gaussianReal 0 1

private theorem integrable_abs_pow (m : ℕ) :
    Integrable (fun z : ℝ ↦ |z| ^ m) (gaussianReal 0 1) := by
  by_cases hm : m = 0
  · simp [hm]
  · simpa only [id_eq, Real.norm_eq_abs] using
      (memLp_id_gaussianReal (μ := 0) (v := 1) m).integrable_norm_pow (by positivity)

private theorem integrable_weighted_of_lipschitz {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (m : ℕ) (p : ℝ × ℝ) :
    Integrable (fun z ↦ z ^ m * f (p.2 + p.1 * z)) (gaussianReal 0 1) := by
  apply (((integrable_abs_pow m).mul_const |f p.2|).add
    ((integrable_abs_pow (m + 1)).const_mul ((L : ℝ) * |p.1|))).mono'
      (continuous_id.pow m |>.mul (hf.continuous.comp (by fun_prop))).aestronglyMeasurable
  filter_upwards [] with z
  have h := hf.dist_le_mul (p.2 + p.1 * z) p.2
  simp only [Real.dist_eq, add_sub_cancel_left, abs_mul] at h
  have htri := abs_add_le (f p.2) (f (p.2 + p.1 * z) - f p.2)
  simp only [add_sub_cancel] at htri
  simp only [Pi.add_apply, Real.norm_eq_abs, Pi.mul_apply, Pi.pow_apply,
    Function.comp_apply, id_eq, abs_mul, abs_pow]
  calc
    _ ≤ |z| ^ m * (|f p.2| + (L : ℝ) * (|p.1| * |z|)) :=
      mul_le_mul_of_nonneg_left (htri.trans (add_le_add_right h _)) (by positivity)
    _ = _ := by rw [pow_succ]; ring

private theorem integrable_weighted_deriv {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (m : ℕ) (p : ℝ × ℝ) :
    Integrable (fun z ↦ z ^ m * deriv f (p.2 + p.1 * z)) (gaussianReal 0 1) := by
  apply ((integrable_abs_pow m).mul_const (L : ℝ)).mono'
    ((measurable_id.pow_const m).mul ((measurable_deriv f).comp (by fun_prop))).aestronglyMeasurable
  filter_upwards [] with z
  simp only [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply, id_eq, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hf) (by positivity)

private theorem hasFDerivAt_weightedAverage {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hdf : Differentiable ℝ f) (m : ℕ) (p : ℝ × ℝ) :
    HasFDerivAt (weightedAverage m f)
      (weightedAverage (m + 1) (deriv f) p • ContinuousLinearMap.fst ℝ ℝ ℝ +
        weightedAverage m (deriv f) p • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  let F' (q : ℝ × ℝ) (z : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
    (z ^ (m + 1) * deriv f (q.2 + q.1 * z)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (z ^ m * deriv f (q.2 + q.1 * z)) • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hi (q : ℝ × ℝ) : Integrable (F' q) (gaussianReal 0 1) := by
    exact ((integrable_weighted_deriv hf (m + 1) q).smul_const
      (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
        ((integrable_weighted_deriv hf m q).smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := gaussianReal 0 1) (s := Set.univ)
    (F := fun q z ↦ z ^ m * f (q.2 + q.1 * z)) (F' := F') (x₀ := p)
    (bound := fun z : ℝ ↦ |z| ^ (m + 1) * (L : ℝ) + |z| ^ m * (L : ℝ))
    univ_mem ?_ (integrable_weighted_of_lipschitz hf m p) (hi p).aestronglyMeasurable
    ?_ ?_ ?_
  · convert! h using 1
    simp only [F', integral_add
      ((integrable_weighted_deriv hf (m + 1) p).smul_const _)
      ((integrable_weighted_deriv hf m p).smul_const _), integral_smul_const,
      weightedAverage]
  · exact Eventually.of_forall fun q ↦ (integrable_weighted_of_lipschitz hf m q).aestronglyMeasurable
  · filter_upwards [] with z
    intro q _
    dsimp only [F']
    apply (norm_add_le _ _).trans
    simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow,
      ContinuousLinearMap.norm_fst, ContinuousLinearMap.norm_snd, mul_one]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hf) (by positivity))
      (mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hf) (by positivity))
  · exact ((integrable_abs_pow (m + 1)).mul_const _).add
      ((integrable_abs_pow m).mul_const _)
  · filter_upwards [] with z
    intro q _
    have hd := (hdf _).hasDerivAt.comp_hasFDerivAt q
      ((hasFDerivAt_snd (𝕜 := ℝ)).add ((hasFDerivAt_fst (𝕜 := ℝ)).mul_const z))
    convert! hd.const_mul (z ^ m) using 1
    apply ContinuousLinearMap.ext
    intro v
    change z ^ (m + 1) * deriv f (q.2 + q.1 * z) * v.1 +
        z ^ m * deriv f (q.2 + q.1 * z) * v.2 =
      z ^ m * (deriv f (q.2 + q.1 * z) * (v.2 + z * v.1))
    rw [pow_succ]
    ring

private theorem contDiff_weightedAverage (m : ℕ) (f : ℝ → ℝ)
    (hD : ∀ k : ℕ, Differentiable ℝ (deriv^[k] f))
    (hL : ∀ k : ℕ, ∃ C : ℝ≥0, LipschitzWith C (deriv^[k] f)) :
    ContDiff ℝ ∞ (weightedAverage m f) := by
  have hn (n : ℕ) : ∀ (m : ℕ) (f : ℝ → ℝ),
      (∀ k : ℕ, Differentiable ℝ (deriv^[k] f)) →
      (∀ k : ℕ, ∃ C : ℝ≥0, LipschitzWith C (deriv^[k] f)) →
      ContDiff ℝ n (weightedAverage m f) := by
    induction n with
    | zero =>
      intro m f hD hL
      obtain ⟨C, hC⟩ := hL 0
      apply contDiff_zero.mpr
      exact Differentiable.continuous
        (fun p ↦ (hasFDerivAt_weightedAverage hC (hD 0) m p).differentiableAt)
    | succ n ih =>
      intro m f hD hL
      obtain ⟨C, hC⟩ := hL 0
      have hD' : ∀ k : ℕ, Differentiable ℝ (deriv^[k] (deriv f)) := by
        intro k
        simpa only [Function.iterate_succ_apply] using hD (k + 1)
      have hL' : ∀ k : ℕ, ∃ C : ℝ≥0, LipschitzWith C (deriv^[k] (deriv f)) := by
        intro k
        simpa only [Function.iterate_succ_apply] using hL (k + 1)
      rw [Nat.cast_add, Nat.cast_one]
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun p ↦ weightedAverage (m + 1) (deriv f) p • ContinuousLinearMap.fst ℝ ℝ ℝ +
        weightedAverage m (deriv f) p • ContinuousLinearMap.snd ℝ ℝ ℝ, ?_, ?_⟩
      · exact ((ih (m + 1) (deriv f) hD' hL').smul contDiff_const).add
          ((ih m (deriv f) hD' hL').smul contDiff_const)
      · exact hasFDerivAt_weightedAverage hC (hD 0) m
  exact contDiff_infty.mpr fun n ↦ hn n m f hD hL

theorem contDiffOn_gaussianAverage {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hdf : Differentiable ℝ f) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ gaussianAverage f p.1 p.2)
      {p : ℝ × ℝ | 0 < p.1} := by
  intro p hp
  have hp0 : 0 < p.1 := hp
  have hh : 0 < p.1 / 2 := by positivity
  have hg : ContDiff ℝ ∞ (weightedAverage 0 (gaussianAverage f (p.1 / 2))) := by
    apply contDiff_weightedAverage
    · intro k
      exact ((contDiff_gaussianAverage hf hdf hh).iterate_deriv k).differentiable (by simp)
    · exact fun k ↦ exists_lipschitzWith_iterate_deriv_gaussianAverage k hf hdf hh
  have hparam : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ ↦ (Real.sqrt (2 * (q.1 - p.1 / 2)), q.2)) p := by
    apply ContDiffAt.prodMk
    · apply ContDiffAt.sqrt
      · fun_prop
      · nlinarith
    · fun_prop
  have hc := hg.contDiffAt.comp p hparam
  apply ContDiffAt.contDiffWithinAt
  apply hc.congr_of_eventuallyEq
  have he : ∀ᶠ q : ℝ × ℝ in 𝓝 p, p.1 / 2 < q.1 :=
    (continuous_fst.tendsto p).eventually (Ioi_mem_nhds (by linarith))
  filter_upwards [he] with q hq
  change gaussianAverage f q.1 q.2 =
    ∫ z, z ^ 0 * gaussianAverage f (p.1 / 2)
      (q.2 + Real.sqrt (2 * (q.1 - p.1 / 2)) * z) ∂gaussianReal 0 1
  simp only [pow_zero, one_mul]
  change gaussianAverage f q.1 q.2 =
    gaussianAverage (gaussianAverage f (p.1 / 2)) (q.1 - p.1 / 2) q.2
  rw [gaussianAverage_semigroup hf (by linarith) hh.le, sub_add_cancel]

end Poincare.Analysis.Heat
