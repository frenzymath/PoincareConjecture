import PoincareConjecture.Proofs.M76.Mathlib.BarycentricCoreComplex

set_option autoImplicit false

open Set
open scoped BigOperators

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in

theorem projectToFace_zero_apply (s : Finset ι) (q : ι → ℝ) (i : ι) :
    projectToFace s 0 q i = if i ∈ s then q i / (∑ j ∈ s, q j) else 0 := by
  simp only [projectToFace, residualMass, sub_zero, mul_zero, sub_zero,
    zero_add, mul_one]

theorem projectToFace_zero_mem (s : Finset ι) {q : ι → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hm : 0 < ∑ i ∈ s, q i) :
    projectToFace s 0 q ∈ barycentricFace s := by
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · rw [projectToFace_zero_apply]
    split_ifs
    · exact div_nonneg (hq i) hm.le
    · exact le_refl _
  · have he : (∑ i, projectToFace s 0 q i) = ∑ i ∈ s, projectToFace s 0 q i := by
      symm
      apply Fintype.sum_subset
      intro i hi
      by_contra his
      exact hi (by simp [projectToFace_zero_apply, his])
    rw [he]
    exact sum_projectToFace s 0 q (by simpa [residualMass] using hm.ne')
  · intro i hi
    simp [projectToFace_zero_apply, hi]

omit [Fintype ι] in

theorem projectToFace_zero_support (s : Finset ι) {q : ι → ℝ} {i : ι}
    (hi : q i = 0) : projectToFace s 0 q i = 0 := by
  simp [projectToFace_zero_apply, hi]

theorem projectToFace_zero_mem_of_mem {s t : Finset ι} {q : ι → ℝ}
    (hq : q ∈ barycentricFace t) (hm : 0 < ∑ i ∈ s, q i) :
    projectToFace s 0 q ∈ barycentricFace t :=
  ⟨(projectToFace_zero_mem s hq.1.1 hm).1,
    fun i hi => projectToFace_zero_support s (hq.2 i hi)⟩

omit [Fintype ι] in

theorem continuousOn_projectToFace_zero (s : Finset ι) :
    ContinuousOn (projectToFace s 0) {q | (∑ i ∈ s, q i) ≠ 0} := by
  apply continuousOn_pi.mpr
  intro i
  by_cases hi : i ∈ s
  · simp only [projectToFace_zero_apply, if_pos hi]
    exact (continuous_apply i).continuousOn.div
      (continuous_finsetSum s (fun j _ => continuous_apply j)).continuousOn (fun _ h => h)
  · simp only [projectToFace_zero_apply, if_neg hi]
    exact continuousOn_const

theorem sum_mix_on_face {s : Finset ι} {u v : ι → ℝ}
    (hu : u ∈ barycentricFace s) (hv : v ∈ barycentricFace sᶜ) (t : ℝ) :
    (∑ i ∈ s, ((1 - t) • u + t • v) i) = 1 - t := by
  have husum : ∑ i ∈ s, u i = 1 := by
    rw [Fintype.sum_subset (fun i hi => by_contra fun hn => hi (hu.2 i hn))]
    exact hu.1.2
  have hvsum : ∑ i ∈ s, v i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hv.2 i (by simpa using hi)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, husum, hvsum, mul_one, mul_zero, add_zero]

theorem projectToFace_zero_mix {s : Finset ι} {u v : ι → ℝ}
    (hu : u ∈ barycentricFace s) (hv : v ∈ barycentricFace sᶜ)
    {t : ℝ} (ht : t ≠ 1) :
    projectToFace s 0 ((1 - t) • u + t • v) = u := by
  ext i
  rw [projectToFace_zero_apply, sum_mix_on_face hu hv]
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    have hvi : v i = 0 := hv.2 i (by simpa using hi)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hvi, mul_zero, add_zero]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr (Ne.symm ht))
  · rw [if_neg hi, hu.2 i hi]

theorem mix_projectToFace_zero {s : Finset ι} {q : ι → ℝ}
    (hq : q ∈ stdSimplex ℝ ι)
    (hm : (∑ i ∈ s, q i) ≠ 0) (hn : (∑ i ∈ sᶜ, q i) ≠ 0) :
    (1 - ∑ i ∈ sᶜ, q i) • projectToFace s 0 q +
      (∑ i ∈ sᶜ, q i) • projectToFace sᶜ 0 q = q := by
  have hsum : (∑ i ∈ s, q i) + ∑ i ∈ sᶜ, q i = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact hq.2
  have he : 1 - (∑ i ∈ sᶜ, q i) = ∑ i ∈ s, q i := by linarith
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, projectToFace_zero_apply, he]
  by_cases hi : i ∈ s
  · simp only [hi, Finset.mem_compl, not_true_eq_false, if_true, if_false,
      mul_zero, add_zero]
    exact mul_div_cancel₀ _ hm
  · simp only [hi, Finset.mem_compl, not_false_eq_true, if_true, if_false,
      mul_zero, zero_add]
    exact mul_div_cancel₀ _ hn

end StdSimplexCore
