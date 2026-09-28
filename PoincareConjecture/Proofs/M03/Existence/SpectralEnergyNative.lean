import PoincareConjecture.Proofs.M03.Existence.SpectralHeatNative
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace PoincareConjecture.SpectralHeatNative

variable {iota : Type*}

def squareSum (a : iota → ℝ) : ENNReal :=
  ∑' i, ENNReal.ofReal (a i ^ 2)

theorem squareSum_state (x : State iota) :
    squareSum x = ENNReal.ofReal (‖x‖ ^ 2) := by
  have hs : Summable (fun i => x i ^ 2) := by
    simpa using (lp.memℓp x).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
  rw [norm_sq_eq_tsum]
  simpa only [squareSum, sq_abs] using
    (ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg (x i)) hs).symm

theorem memℓp_two_of_squareSum_ne_top {a : iota → ℝ}
    (ha : squareSum a ≠ ∞) : Memℓp a 2 := by
  have hs := ENNReal.summable_toReal ha
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofNat,
    Real.rpow_two, Real.norm_eq_abs, sq_abs] using hs

theorem squareSum_ne_top_iff {a : iota → ℝ} :
    squareSum a ≠ ∞ ↔ Memℓp a 2 := by
  refine ⟨memℓp_two_of_squareSum_ne_top, fun ha => ?_⟩
  have h := squareSum_state (⟨a, ha⟩ : State iota)
  change squareSum a = _ at h
  rw [h]
  exact ENNReal.ofReal_ne_top

def stateOfCoeffs (a : iota → ℝ) : State iota := by
  classical
  exact if ha : Memℓp a 2 then ⟨a, ha⟩ else 0

@[simp] theorem stateOfCoeffs_apply {a : iota → ℝ} (ha : Memℓp a 2)
    (i : iota) : stateOfCoeffs a i = a i := by
  simp only [stateOfCoeffs, dif_pos ha]

theorem squareSum_stateOfCoeffs {a : iota → ℝ} (ha : Memℓp a 2) :
    ENNReal.ofReal (‖stateOfCoeffs a‖ ^ 2) = squareSum a := by
  rw [← squareSum_state]
  congr 1
  funext i
  exact stateOfCoeffs_apply ha i

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem aemeasurable_squareSum [Countable iota] {a : α → iota → ℝ}
    (ha : ∀ i, AEStronglyMeasurable (fun t => a t i) μ) :
    AEMeasurable (fun t => squareSum (a t)) μ := by
  exact AEMeasurable.tsum (fun i => ((ha i).aemeasurable.pow_const 2).ennreal_ofReal)

theorem ae_memℓp_of_lintegral_squareSum_lt_top [Countable iota]
    {a : α → iota → ℝ}
    (ha : ∀ i, AEStronglyMeasurable (fun t => a t i) μ)
    (henergy : (∫⁻ t, squareSum (a t) ∂μ) < ∞) :
    ∀ᵐ t ∂μ, Memℓp (a t) 2 := by
  filter_upwards [ae_lt_top' (aemeasurable_squareSum ha) henergy.ne] with t ht
  exact memℓp_two_of_squareSum_ne_top ht.ne

theorem aestronglyMeasurable_stateOfCoeffs [Countable iota]
    {a : α → iota → ℝ}
    (ha : ∀ i, AEStronglyMeasurable (fun t => a t i) μ)
    (hmem : ∀ᵐ t ∂μ, Memℓp (a t) 2) :
    AEStronglyMeasurable (fun t => stateOfCoeffs (a t)) μ := by
  classical
  let approximant : Finset iota → α → State iota :=
    fun s t => ∑ i ∈ s, lp.single 2 i (a t i)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset iota))
    (f := approximant)
  · intro s
    apply Finset.aestronglyMeasurable_fun_sum
    intro i hi
    exact (lp.singleContinuousLinearMap ℝ (fun _ : iota => ℝ) 2 i).continuous.comp_aestronglyMeasurable
      (ha i)
  · filter_upwards [hmem] with t ht
    have h := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ∞)
      (stateOfCoeffs (a t))
    simpa only [HasSum, SummationFilter.unconditional, approximant,
      stateOfCoeffs_apply ht] using h

theorem lintegral_sq_norm_stateOfCoeffs [Countable iota]
    {a : α → iota → ℝ} (hmem : ∀ᵐ t ∂μ, Memℓp (a t) 2) :
    (∫⁻ t, ENNReal.ofReal (‖stateOfCoeffs (a t)‖ ^ 2) ∂μ) =
      ∫⁻ t, squareSum (a t) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [hmem] with t ht
  exact squareSum_stateOfCoeffs ht

theorem memLp_stateOfCoeffs [Countable iota] {a : α → iota → ℝ}
    (ha : ∀ i, AEStronglyMeasurable (fun t => a t i) μ)
    (henergy : (∫⁻ t, squareSum (a t) ∂μ) < ∞) :
    MemLp (fun t => stateOfCoeffs (a t)) 2 μ := by
  have hm := ae_memℓp_of_lintegral_squareSum_lt_top ha henergy
  have hsm := aestronglyMeasurable_stateOfCoeffs ha hm
  apply (memLp_two_iff_integrable_sq_norm hsm).mpr
  refine ⟨hsm.norm.pow 2, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun t => sq_nonneg ‖stateOfCoeffs (a t)‖))).mpr
  rwa [lintegral_sq_norm_stateOfCoeffs hm]

theorem integral_sq_norm_stateOfCoeffs [Countable iota]
    {a : α → iota → ℝ}
    (ha : ∀ i, AEStronglyMeasurable (fun t => a t i) μ)
    (henergy : (∫⁻ t, squareSum (a t) ∂μ) < ∞) :
    (∫ t, ‖stateOfCoeffs (a t)‖ ^ 2 ∂μ) =
      (∫⁻ t, squareSum (a t) ∂μ).toReal := by
  have hm := ae_memℓp_of_lintegral_squareSum_lt_top ha henergy
  have hsm := aestronglyMeasurable_stateOfCoeffs ha hm
  have hi := (memLp_two_iff_integrable_sq_norm hsm).mp
    (memLp_stateOfCoeffs ha henergy)
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun t => sq_nonneg ‖stateOfCoeffs (a t)‖))
  rw [lintegral_sq_norm_stateOfCoeffs hm] at he
  have hn : 0 ≤ ∫ t, ‖stateOfCoeffs (a t)‖ ^ 2 ∂μ :=
    integral_nonneg (fun t => sq_nonneg _)
  simpa only [ENNReal.toReal_ofReal hn] using congrArg ENNReal.toReal he

def finiteWeightedEnergy (lambda : iota → NNReal) (s : Finset iota)
    (k : ℕ) (u : iota → ℝ) : ℝ :=
  ∑ i ∈ s, (1 + (lambda i : ℝ)) ^ k * u i ^ 2

theorem finiteWeightedEnergy_nonneg (lambda : iota → NNReal) (s : Finset iota)
    (k : ℕ) (u : iota → ℝ) : 0 ≤ finiteWeightedEnergy lambda s k u :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (sq_nonneg _))

theorem finiteWeightedEnergy_continuousOn (lambda : iota → NNReal) (s : Finset iota)
    (k : ℕ) {u : ℝ → iota → ℝ} {J : Set ℝ}
    (hu : ∀ i ∈ s, ContinuousOn (fun t => u t i) J) :
    ContinuousOn (fun t => finiteWeightedEnergy lambda s k (u t)) J := by
  exact continuousOn_finsetSum s (fun i hi => continuousOn_const.mul ((hu i hi).pow 2))

theorem finiteWeightedEnergy_hasDerivWithinAt (lambda : iota → NNReal)
    (s : Finset iota) (k : ℕ) {u : ℝ → iota → ℝ} {F : iota → ℝ}
    {J : Set ℝ} {t : ℝ}
    (hu : ∀ i ∈ s, HasDerivWithinAt (fun r => u r i)
      (F i - (lambda i : ℝ) * u t i) J t) :
    HasDerivWithinAt (fun r => finiteWeightedEnergy lambda s k (u r))
      (-2 * finiteWeightedEnergy lambda s (k + 1) (u t) +
        2 * finiteWeightedEnergy lambda s k (u t) +
        2 * ∑ i ∈ s, (1 + (lambda i : ℝ)) ^ k * u t i * F i) J t := by
  have hd : HasDerivWithinAt (fun r => finiteWeightedEnergy lambda s k (u r))
      (∑ i ∈ s, (1 + (lambda i : ℝ)) ^ k *
        (2 * u t i * (F i - (lambda i : ℝ) * u t i))) J t := by
    apply HasDerivWithinAt.fun_sum
    intro i hi
    simpa only [show (2 : ℕ) - 1 = 1 by omega, pow_one, Nat.cast_ofNat] using
      ((hu i hi).fun_pow 2).const_mul ((1 + (lambda i : ℝ)) ^ k)
  convert hd using 1
  simp only [finiteWeightedEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_succ]
  ring

theorem finiteWeightedPairing_cross_le (lambda : iota → NNReal)
    (s : Finset iota) (k : ℕ) (u v : iota → ℝ) :
    2 * ∑ i ∈ s, (1 + (lambda i : ℝ)) ^ (k + 1) * u i * v i ≤
      finiteWeightedEnergy lambda s (k + 2) u + finiteWeightedEnergy lambda s k v := by
  rw [finiteWeightedEnergy, finiteWeightedEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_nonneg (show 0 ≤ (1 + (lambda i : ℝ)) ^ k by positivity)
    (sq_nonneg ((1 + (lambda i : ℝ)) * u i - v i))
  simp only [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  nlinarith only [h]

theorem finiteWeightedPairing_same_le (lambda : iota → NNReal)
    (s : Finset iota) (k : ℕ) (u v : iota → ℝ) :
    2 * ∑ i ∈ s, (1 + (lambda i : ℝ)) ^ k * u i * v i ≤
      finiteWeightedEnergy lambda s k u + finiteWeightedEnergy lambda s k v := by
  rw [finiteWeightedEnergy, finiteWeightedEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  nlinarith only [mul_nonneg (show 0 ≤ (1 + (lambda i : ℝ)) ^ k by positivity)
    (sq_nonneg (u i - v i))]

theorem finiteWeightedEnergy_rate_le (lambda : iota → NNReal)
    (s : Finset iota) (k : ℕ) (u F b : iota → ℝ) {theta A S : ℝ}
    (hrem : finiteWeightedEnergy lambda s k (fun i => F i - b i) ≤
      theta * finiteWeightedEnergy lambda s (k + 2) u +
        A * finiteWeightedEnergy lambda s (k + 1) u)
    (hseed : finiteWeightedEnergy lambda s (k + 1) b ≤ S) :
    -2 * finiteWeightedEnergy lambda s (k + 2) u +
        2 * finiteWeightedEnergy lambda s (k + 1) u +
        2 * ∑ i ∈ s, (1 + (lambda i : ℝ)) ^ (k + 1) * u i * F i ≤
      -(1 - theta) * finiteWeightedEnergy lambda s (k + 2) u +
        (3 + A) * finiteWeightedEnergy lambda s (k + 1) u + S := by
  have hc := finiteWeightedPairing_cross_le lambda s k u (fun i => F i - b i)
  have hb := finiteWeightedPairing_same_le lambda s (k + 1) u b
  have hsplit : (∑ i ∈ s, (1 + (lambda i : ℝ)) ^ (k + 1) * u i * F i) =
      (∑ i ∈ s, (1 + (lambda i : ℝ)) ^ (k + 1) * u i * (F i - b i)) +
        ∑ i ∈ s, (1 + (lambda i : ℝ)) ^ (k + 1) * u i * b i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsplit]
  linarith

theorem sq_tame_split {d C x y : ℝ} (hd : 0 ≤ d) (hd1 : d < 1) :
    (d * x + C * y) ^ 2 ≤
      ((1 + d ^ 2) / 2) * x ^ 2 +
        (C ^ 2 + (d * C) ^ 2 / ((1 - d ^ 2) / 2)) * y ^ 2 := by
  have he : 0 < (1 - d ^ 2) / 2 := by nlinarith
  have hs := sq_nonneg (((1 - d ^ 2) / 2) * x - d * C * y)
  have hy : 2 * (d * x) * (C * y) ≤ ((1 - d ^ 2) / 2) * x ^ 2 +
      ((d * C) ^ 2 / ((1 - d ^ 2) / 2)) * y ^ 2 := by
    apply (mul_le_mul_iff_right₀ he).mp
    have hi : ((1 - d ^ 2) / 2) *
        (((d * C) ^ 2 / ((1 - d ^ 2) / 2)) * y ^ 2) = (d * C) ^ 2 * y ^ 2 := by
      rw [← mul_assoc, mul_div_cancel₀ _ he.ne']
    nlinarith only [hs, hi]
  nlinarith only [hy]

theorem finiteWeightedEnergy_le_gronwall (lambda : iota → NNReal)
    (s : Finset iota) (k : ℕ) {T theta A S B : ℝ} (hT : 0 ≤ T)
    (htheta : theta ≤ 1) (hA : 0 ≤ A) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (u F : ℝ → iota → ℝ) (b : iota → ℝ)
    (hcont : ∀ i ∈ s, ContinuousOn (fun t => u t i) (Icc (0 : ℝ) T))
    (hode : ∀ t ∈ Ico (0 : ℝ) T, ∀ i ∈ s,
      HasDerivWithinAt (fun r => u r i) (F t i - (lambda i : ℝ) * u t i) (Ici t) t)
    (hrem : ∀ t ∈ Ico (0 : ℝ) T,
      finiteWeightedEnergy lambda s k (fun i => F t i - b i) ≤
        theta * finiteWeightedEnergy lambda s (k + 2) (u t) +
          A * finiteWeightedEnergy lambda s (k + 1) (u t))
    (hseed : finiteWeightedEnergy lambda s (k + 1) b ≤ S)
    (hinit : finiteWeightedEnergy lambda s (k + 1) (u 0) ≤ B) :
    ∀ t ∈ Icc (0 : ℝ) T,
      finiteWeightedEnergy lambda s (k + 1) (u t) ≤ gronwallBound B (3 + A) S T := by
  let E : ℝ → ℝ := fun t => finiteWeightedEnergy lambda s (k + 1) (u t)
  let D : ℝ → ℝ := fun t => -2 * finiteWeightedEnergy lambda s (k + 2) (u t) +
    2 * E t + 2 * ∑ i ∈ s, (1 + (lambda i : ℝ)) ^ (k + 1) * u t i * F t i
  have hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt E (D t) (Ici t) t := by
    intro t ht
    simpa only [E, D, show k + 1 + 1 = k + 2 by omega] using
      finiteWeightedEnergy_hasDerivWithinAt lambda s (k + 1) (hode t ht)
  have hbound : ∀ t ∈ Ico (0 : ℝ) T, D t ≤ (3 + A) * E t + S := by
    intro t ht
    have hr := finiteWeightedEnergy_rate_le lambda s k (u t) (F t) b (hrem t ht) hseed
    have hd := mul_nonneg (sub_nonneg.mpr htheta)
      (finiteWeightedEnergy_nonneg lambda s (k + 2) (u t))
    dsimp only [D, E]
    linarith
  have hg := le_gronwallBound_of_liminf_deriv_right_le
    (finiteWeightedEnergy_continuousOn lambda s (k + 1) hcont)
    (f' := D) (fun t ht r hr => by
      simpa only [slope_def_field, div_eq_inv_mul] using
        (hderiv t ht).liminf_right_slope_le hr) hinit hbound
  intro t ht
  exact (hg t ht).trans (gronwallBound_mono hB hS (by linarith)
    (by simpa only [sub_zero] using ht.2))

theorem summable_weighted_sq_of_finite_limit (lambda : iota → NNReal) (k : ℕ)
    (s : ℕ → Finset iota) (hs : Tendsto s atTop atTop)
    (u : ℕ → iota → ℝ) (v : iota → ℝ)
    (hu : ∀ i, Tendsto (fun N => u N i) atTop (𝓝 (v i)))
    {B : ℝ} (hB : ∀ N, finiteWeightedEnergy lambda (s N) k (u N) ≤ B) :
    Summable (fun i => (1 + (lambda i : ℝ)) ^ k * v i ^ 2) ∧
      (∑' i, (1 + (lambda i : ℝ)) ^ k * v i ^ 2) ≤ B := by
  have hpartial : ∀ q : Finset iota, finiteWeightedEnergy lambda q k v ≤ B := by
    intro q
    have hconv : Tendsto (fun N => finiteWeightedEnergy lambda q k (u N)) atTop
        (𝓝 (finiteWeightedEnergy lambda q k v)) :=
      tendsto_finset_sum q (fun i hi => tendsto_const_nhds.mul ((hu i).pow 2))
    apply le_of_tendsto hconv
    filter_upwards [hs.eventually (eventually_ge_atTop q)] with N hN
    exact (Finset.sum_le_sum_of_subset_of_nonneg hN
      (fun i hi hni => mul_nonneg (by positivity) (sq_nonneg _))).trans (hB N)
  have hnonneg : 0 ≤ (fun i => (1 + (lambda i : ℝ)) ^ k * v i ^ 2) :=
    fun i => mul_nonneg (by positivity) (sq_nonneg _)
  exact ⟨summable_of_sum_le hnonneg hpartial, Real.tsum_le_of_sum_le hnonneg hpartial⟩

theorem weighted_sq_mass_le_of_galerkin (lambda : iota → NNReal)
    (s : ℕ → Finset iota) (hs : Tendsto s atTop atTop) (k : ℕ)
    {T theta A S B : ℝ} (hT : 0 ≤ T) (htheta : theta ≤ 1)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (u F : ℕ → ℝ → iota → ℝ) (b : iota → ℝ) (v : ℝ → iota → ℝ)
    (hcont : ∀ N, ∀ i ∈ s N, ContinuousOn (fun t => u N t i) (Icc (0 : ℝ) T))
    (hode : ∀ N, ∀ t ∈ Ico (0 : ℝ) T, ∀ i ∈ s N,
      HasDerivWithinAt (fun r => u N r i)
        (F N t i - (lambda i : ℝ) * u N t i) (Ici t) t)
    (hrem : ∀ N, ∀ t ∈ Ico (0 : ℝ) T,
      finiteWeightedEnergy lambda (s N) k (fun i => F N t i - b i) ≤
        theta * finiteWeightedEnergy lambda (s N) (k + 2) (u N t) +
          A * finiteWeightedEnergy lambda (s N) (k + 1) (u N t))
    (hseed : ∀ N, finiteWeightedEnergy lambda (s N) (k + 1) b ≤ S)
    (hinit : ∀ N, finiteWeightedEnergy lambda (s N) (k + 1) (u N 0) ≤ B)
    (hlim : ∀ t ∈ Icc (0 : ℝ) T, ∀ i,
      Tendsto (fun N => u N t i) atTop (𝓝 (v t i))) :
    ∀ t ∈ Icc (0 : ℝ) T,
      Summable (fun i => (1 + (lambda i : ℝ)) ^ (k + 1) * v t i ^ 2) ∧
        (∑' i, (1 + (lambda i : ℝ)) ^ (k + 1) * v t i ^ 2) ≤
          gronwallBound B (3 + A) S T := by
  intro t ht
  apply summable_weighted_sq_of_finite_limit lambda (k + 1) s hs
    (fun N => u N t) (v t) (hlim t ht)
  intro N
  exact finiteWeightedEnergy_le_gronwall lambda (s N) k hT htheta hA hS hB
    (u N) (F N) b (hcont N) (hode N) (hrem N) (hseed N) (hinit N) t ht

end PoincareConjecture.SpectralHeatNative
