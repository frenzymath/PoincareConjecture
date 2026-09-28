import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.L2








noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Poincare.Analysis.Spectral.Counting

variable {H K X ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]


theorem sum_inner_map_sq_le (A : H →L[ℝ] K) {b : ι → H}
    (hb : Orthonormal ℝ b) (s : Finset ι) (k : K) :
    ∑ i ∈ s, (inner ℝ k (A (b i))) ^ 2 ≤ ‖A‖ ^ 2 * ‖k‖ ^ 2 := by
  calc
    ∑ i ∈ s, (inner ℝ k (A (b i))) ^ 2
        = ∑ i ∈ s, ‖inner ℝ (b i) (A.adjoint k)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [A.adjoint_inner_right, real_inner_comm]
          simp
    _ ≤ ‖A.adjoint k‖ ^ 2 := hb.sum_inner_products_le _
    _ ≤ (‖A.adjoint‖ * ‖k‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) (A.adjoint.le_opNorm k) 2
    _ = ‖A‖ ^ 2 * ‖k‖ ^ 2 := by simp [mul_pow]

variable [MeasurableSpace X] {ν : Measure X}


theorem sum_integral_inner_map_sq_le (A : H →L[ℝ] K) {b : ι → H}
    (hb : Orthonormal ℝ b) (s : Finset ι) (k : X → K)
    (hk : Integrable (fun x => ‖k x‖ ^ 2) ν)
    (hi : ∀ i ∈ s, Integrable (fun x => (inner ℝ (k x) (A (b i))) ^ 2) ν) :
    ∑ i ∈ s, ∫ x, (inner ℝ (k x) (A (b i))) ^ 2 ∂ν ≤
      ‖A‖ ^ 2 * ∫ x, ‖k x‖ ^ 2 ∂ν := by
  rw [← integral_finsetSum s hi, ← integral_const_mul]
  exact integral_mono (integrable_finsetSum _ hi) (hk.const_mul _)
    (fun x => sum_inner_map_sq_le A hb s (k x))



theorem sum_integral_inner_map_sq_le_const [IsFiniteMeasure ν]
    (A : H →L[ℝ] K) {b : ι → H} (hb : Orthonormal ℝ b)
    (s : Finset ι) (k : X → K) {C : ℝ}
    (hk : ∀ x, ‖k x‖ ^ 2 ≤ C)
    (hi : ∀ i ∈ s, Integrable (fun x => (inner ℝ (k x) (A (b i))) ^ 2) ν) :
    ∑ i ∈ s, ∫ x, (inner ℝ (k x) (A (b i))) ^ 2 ∂ν ≤
      ν.real Set.univ * (‖A‖ ^ 2 * C) := by
  rw [← integral_finsetSum s hi]
  change _ ≤ ν.real Set.univ • (‖A‖ ^ 2 * C)
  rw [← integral_const]
  apply integral_mono (integrable_finsetSum _ hi) (integrable_const _)
  intro x
  exact (sum_inner_map_sq_le A hb s (k x)).trans
    (mul_le_mul_of_nonneg_left (hk x) (sq_nonneg _))

section KernelOperator

variable (S : Set X) (hS : MeasurableSet S) (hνS : ν S ≠ ∞)
  (k : X → K) (hk : ∀ u : K, AEStronglyMeasurable (fun x => inner ℝ (k x) u) ν)
  (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖k x‖ ≤ C)

include hS hνS hk hC hbound

omit [CompleteSpace K] hC in
theorem kernelOn_memLp (u : K) :
    MemLp (S.indicator fun x => inner ℝ (k x) u) 2 ν := by
  rw [memLp_indicator_iff_restrict hS]
  let : IsFiniteMeasure (ν.restrict S) := ⟨by simpa using hνS.lt_top⟩
  apply MemLp.of_bound ((hk u).mono_measure Measure.restrict_le_self) (C * ‖u‖)
  exact Filter.Eventually.of_forall fun x =>
    (norm_inner_le_norm (k x) u).trans (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

private def kernelOnLinear : K →ₗ[ℝ] Lp ℝ 2 ν where
  toFun u := (kernelOn_memLp S hS hνS k hk C hbound u).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(kernelOn_memLp S hS hνS k hk C hbound (u + v)).coeFn_toLp,
      (kernelOn_memLp S hS hνS k hk C hbound u).coeFn_toLp,
      (kernelOn_memLp S hS hνS k hk C hbound v).coeFn_toLp,
      Lp.coeFn_add
        ((kernelOn_memLp S hS hνS k hk C hbound u).toLp _)
        ((kernelOn_memLp S hS hνS k hk C hbound v).toLp _)] with x huv hu hv ha
    rw [huv, ha, Pi.add_apply, hu, hv]
    simp [inner_add_right, Set.indicator_add]
  map_smul' a u := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(kernelOn_memLp S hS hνS k hk C hbound (a • u)).coeFn_toLp,
      (kernelOn_memLp S hS hνS k hk C hbound u).coeFn_toLp,
      Lp.coeFn_smul a ((kernelOn_memLp S hS hνS k hk C hbound u).toLp _)]
      with x hau hu ha
    rw [hau, ha, Pi.smul_apply, hu]
    by_cases hx : x ∈ S <;> simp [inner_smul_right, hx]

omit [CompleteSpace K] hC in
private theorem norm_kernelOnLinear_sq_le (u : K) :
    ‖kernelOnLinear S hS hνS k hk C hbound u‖ ^ 2 ≤
      ν.real S * C ^ 2 * ‖u‖ ^ 2 := by
  rw [kernelOnLinear, LinearMap.coe_mk, AddHom.coe_mk,
    Poincare.Analysis.Sobolev.norm_toLp_sq_eq_integral]
  have h_ind : (fun x => (S.indicator (fun y => inner ℝ (k y) u) x) ^ 2) =
      S.indicator (fun x => (inner ℝ (k x) u) ^ 2) := by
    ext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [h_ind, integral_indicator hS]
  let : IsFiniteMeasure (ν.restrict S) := ⟨by simpa using hνS.lt_top⟩
  have hm : MemLp (fun x => inner ℝ (k x) u) 2 (ν.restrict S) :=
    (memLp_indicator_iff_restrict hS).mp (kernelOn_memLp S hS hνS k hk C hbound u)
  have hi := hm.integrable_sq
  calc
    (∫ x in S, (inner ℝ (k x) u) ^ 2 ∂ν) ≤
        ∫ _ in S, C ^ 2 * ‖u‖ ^ 2 ∂ν := by
      apply integral_mono hi (integrable_const _)
      intro x
      have hb := (norm_inner_le_norm (𝕜 := ℝ) (k x) u).trans
        (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))
      simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = ν.real S * C ^ 2 * ‖u‖ ^ 2 := by
      simp [Measure.real, mul_assoc]



def kernelOn : K →L[ℝ] Lp ℝ 2 ν :=
  (kernelOnLinear S hS hνS k hk C hbound).mkContinuous
    (Real.sqrt (ν.real S) * C) fun u => by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      have h := norm_kernelOnLinear_sq_le S hS hνS k hk C hbound u
      simpa [mul_pow, Real.sq_sqrt (measureReal_nonneg : 0 ≤ ν.real S), mul_assoc] using h

omit [CompleteSpace K] in
theorem kernelOn_coeFn (u : K) :
    ⇑(kernelOn S hS hνS k hk C hC hbound u) =ᵐ[ν]
      S.indicator (fun x => inner ℝ (k x) u) :=
  (kernelOn_memLp S hS hνS k hk C hbound u).coeFn_toLp

omit [CompleteSpace K] in
theorem norm_kernelOn_sq_eq_integral (u : K) :
    ‖kernelOn S hS hνS k hk C hC hbound u‖ ^ 2 =
      ∫ x in S, (inner ℝ (k x) u) ^ 2 ∂ν := by
  change ‖(kernelOn_memLp S hS hνS k hk C hbound u).toLp _‖ ^ 2 = _
  rw [Poincare.Analysis.Sobolev.norm_toLp_sq_eq_integral]
  have h_ind : (fun x => (S.indicator (fun y => inner ℝ (k y) u) x) ^ 2) =
      S.indicator (fun x => (inner ℝ (k x) u) ^ 2) := by
    ext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [h_ind, integral_indicator hS]


theorem sum_norm_kernelOn_map_sq_le (A : H →L[ℝ] K) {b : ι → H}
    (hb : Orthonormal ℝ b) (s : Finset ι) {B : ℝ}
    (hB : ∀ x, ‖k x‖ ^ 2 ≤ B) :
    ∑ i ∈ s, ‖kernelOn S hS hνS k hk C hC hbound (A (b i))‖ ^ 2 ≤
      ν.real S * (‖A‖ ^ 2 * B) := by
  simp_rw [norm_kernelOn_sq_eq_integral]
  let : IsFiniteMeasure (ν.restrict S) := ⟨by simpa using hνS.lt_top⟩
  have hi (i : ι) : Integrable (fun x => (inner ℝ (k x) (A (b i))) ^ 2)
      (ν.restrict S) := by
    have hm := (memLp_indicator_iff_restrict hS).mp
      (kernelOn_memLp S hS hνS k hk C hbound (A (b i)))
    exact hm.integrable_sq
  simpa [Measure.real] using
    sum_integral_inner_map_sq_le_const (ν := ν.restrict S) A hb s k hB (fun i _ => hi i)

end KernelOperator

end Poincare.Analysis.Spectral.Counting
