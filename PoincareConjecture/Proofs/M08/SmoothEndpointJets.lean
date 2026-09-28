import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M08

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def endpointJetCutoff : ContDiffBump (0 : ℝ) := default

def endpointJetPolynomial (k : ℕ) (A : E) (x : ℝ) : E :=
  (x ^ k / (k.factorial : ℝ)) • A

theorem endpointJetPolynomial_contDiff (k : ℕ) (A : E) :
    ContDiff ℝ ∞ (endpointJetPolynomial k A) :=
  ((contDiff_id.pow k).div_const _).smul_const A

theorem endpointJetPolynomial_deriv (k m : ℕ) (A : E) :
    iteratedDeriv m (endpointJetPolynomial k A) 0 = if m = k then A else 0 := by
  unfold endpointJetPolynomial
  have hp : ContDiffAt ℝ m (fun x : ℝ ↦ x ^ k / (k.factorial : ℝ)) 0 := by fun_prop
  rw [iteratedDeriv_smul_const hp A, iteratedDeriv_div_const,
    iteratedDeriv_fun_pow_zero]
  by_cases h : m = k <;> simp [h, Nat.factorial_ne_zero]

def endpointJetBase (k : ℕ) (A : E) (x : ℝ) : E :=
  endpointJetCutoff x • endpointJetPolynomial k A x

theorem endpointJetBase_contDiff (k : ℕ) (A : E) :
    ContDiff ℝ ∞ (endpointJetBase k A) :=
  endpointJetCutoff.contDiff.smul (endpointJetPolynomial_contDiff k A)

theorem endpointJetBase_hasCompactSupport (k : ℕ) (A : E) :
    HasCompactSupport (endpointJetBase k A) :=
  endpointJetCutoff.hasCompactSupport.smul_right

theorem endpointJetBase_eventually_eq (k : ℕ) (A : E) :
    endpointJetBase k A =ᶠ[𝓝 0] endpointJetPolynomial k A := by
  filter_upwards [endpointJetCutoff.eventuallyEq_one] with x hx
  simp only [endpointJetBase, hx, Pi.one_apply, one_smul]

theorem endpointJetBase_deriv (k m : ℕ) (A : E) :
    iteratedDeriv m (endpointJetBase k A) 0 = if m = k then A else 0 := by
  rw [(endpointJetBase_eventually_eq k A).iteratedDeriv_eq m,
    endpointJetPolynomial_deriv]

theorem exists_small_endpointJet (k : ℕ) (A : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → E, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ m < k, ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ ε) ∧
      (∀ m, iteratedDeriv m f 0 = if m = k then A else 0) := by
  let φ := endpointJetBase k A
  have hφ : ContDiff ℝ ∞ φ := endpointJetBase_contDiff k A
  have hsupp : HasCompactSupport φ := endpointJetBase_hasCompactSupport k A
  choose B hB using fun m : ℕ ↦
    (hsupp.iteratedFDeriv m).exists_bound_of_continuous
      ((hφ.of_le (show (m : ℕ∞ω) ≤ ∞ from
        WithTop.coe_le_coe.mpr le_top)).continuous_iteratedFDeriv')
  let C := 1 + ∑ m ∈ Finset.range k, max 0 (B m)
  have hsum : 0 ≤ ∑ m ∈ Finset.range k, max 0 (B m) :=
    Finset.sum_nonneg (fun m _ ↦ le_max_left _ _)
  have hC : 0 < C := by dsimp only [C]; linarith
  have hBC (m : ℕ) (hm : m < k) : B m ≤ C := by
    have h := Finset.single_le_sum (s := Finset.range k) (f := fun i ↦ max 0 (B i))
      (fun i _ ↦ le_max_left 0 (B i)) (Finset.mem_range.mpr hm)
    dsimp only [C]
    linarith [le_max_right 0 (B m)]
  let r := min 1 (ε / C)
  have hr : 0 < r := lt_min zero_lt_one (div_pos hε hC)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrC : r * C ≤ ε := (le_div_iff₀ hC).mp (min_le_right 1 (ε / C))
  let f : ℝ → E := fun x ↦ r ^ k • φ (r⁻¹ * x)
  have hf : ContDiff ℝ ∞ f :=
    (hφ.comp (contDiff_const.mul contDiff_id)).const_smul (r ^ k)
  have hfsupp : HasCompactSupport f := by
    exact (hsupp.comp_smul (inv_ne_zero hr.ne')).smul_left
  have hderiv (m : ℕ) (x : ℝ) :
      iteratedFDeriv ℝ m f x =
        (r ^ k * (r⁻¹) ^ m) • iteratedFDeriv ℝ m φ (r⁻¹ * x) := by
    have hm : (m : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hc : ContDiff ℝ ∞ (fun y : ℝ ↦ φ (r⁻¹ • y)) :=
      hφ.comp ((contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)).const_smul r⁻¹)
    rw [show f = fun x ↦ r ^ k • φ (r⁻¹ • x) from rfl]
    rw [iteratedFDeriv_const_smul_apply' (i := m) (a := r ^ k)
      (hc.of_le hm).contDiffAt]
    rw [iteratedFDeriv_comp_const_smul r⁻¹ (hφ.of_le hm)]
    simp only [smul_smul, smul_eq_mul]
  have hsmall (m : ℕ) (hm : m < k) (x : ℝ) : ‖iteratedFDeriv ℝ m f x‖ ≤ ε := by
    have hfactor : r ^ k * (r⁻¹) ^ m = r ^ (k - m) := by
      rw [pow_sub₀ r hr.ne' hm.le, inv_pow]
    have hpow : r ^ (k - m) ≤ r := by
      simpa only [pow_one] using
        pow_le_pow_of_le_one hr.le hr1 (show 1 ≤ k - m by omega)
    rw [hderiv, hfactor, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hr.le _)]
    calc
      r ^ (k - m) * ‖iteratedFDeriv ℝ m φ (r⁻¹ * x)‖ ≤ r ^ (k - m) * C :=
        mul_le_mul_of_nonneg_left ((hB m _).trans (hBC m hm)) (pow_nonneg hr.le _)
      _ ≤ r * C := mul_le_mul_of_nonneg_right hpow hC.le
      _ ≤ ε := hrC
  have hnear : f =ᶠ[𝓝 0] endpointJetPolynomial k A := by
    have hc : Tendsto (fun x : ℝ ↦ r⁻¹ * x) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun x : ℝ ↦ r⁻¹ * x) :=
        continuous_const.mul continuous_id
      simpa only [ContinuousAt, mul_zero] using
        hc.continuousAt (x := (0 : ℝ))
    filter_upwards [hc.eventually (endpointJetBase_eventually_eq k A)] with x hx
    change r ^ k • endpointJetBase k A (r⁻¹ * x) = endpointJetPolynomial k A x
    rw [hx]
    unfold endpointJetPolynomial
    rw [smul_smul]
    congr 1
    rw [mul_pow, ← mul_div_assoc, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hr.ne', one_pow, one_mul]
  exact ⟨f, hf, hfsupp, hsmall, fun m ↦
    (hnear.iteratedDeriv_eq m).trans (endpointJetPolynomial_deriv k m A)⟩

variable [FiniteDimensional ℝ E]

theorem exists_smooth_endpoint_jets (A : ℕ → E) :
    ∃ f : ℝ → E, ContDiff ℝ ∞ f ∧ ∀ m, iteratedDeriv m f 0 = A m := by
  choose f hf hsupp hsmall hjet using fun k : ℕ ↦
    exists_small_endpointJet k (A k) (ε := (1 / 2 : ℝ) ^ k) (by positivity)
  have hgeom : Summable (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  choose B hB using fun m k : ℕ ↦
    ((hsupp k).iteratedFDeriv m).exists_bound_of_continuous
      (((hf k).of_le (show (m : ℕ∞ω) ≤ ∞ from
        WithTop.coe_le_coe.mpr le_top)).continuous_iteratedFDeriv')
  let C : ℕ → ℕ → ℝ := fun m k ↦ if m < k then (1 / 2 : ℝ) ^ k else B m k
  have hCsummable (m : ℕ) : Summable (C m) := by
    apply hgeom.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_gt_atTop m] with k hk
    simp only [C, if_pos hk]
  have hbound (m k : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ m (f k) x‖ ≤ C m k := by
    by_cases h : m < k
    · simpa only [C, if_pos h] using hsmall k m h x
    · simpa only [C, if_neg h] using hB m k x
  let g : ℝ → E := fun x ↦ ∑' k, f k x
  have hg : ContDiff ℝ ∞ g :=
    contDiff_tsum hf (fun m _ ↦ hCsummable m) (fun m k x _ ↦ hbound m k x)
  refine ⟨g, hg, ?_⟩
  intro m
  have hd : iteratedFDeriv ℝ m g 0 = ∑' k, iteratedFDeriv ℝ m (f k) 0 :=
    iteratedFDeriv_tsum_apply hf (fun j _ ↦ hCsummable j)
      (fun j k x _ ↦ hbound j k x) (by simp) 0
  have hj : iteratedDeriv m g 0 = ∑' k, iteratedDeriv m (f k) 0 := by
    simp only [iteratedDeriv_eq_equiv_comp, Function.comp_apply]
    rw [hd]
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) E).symm.toContinuousLinearEquiv.map_tsum
  rw [hj]
  simp only [hjet]
  simpa only [eq_comm] using (tsum_ite_eq m (fun k ↦ A k))

end PoincareConjecture.M08
