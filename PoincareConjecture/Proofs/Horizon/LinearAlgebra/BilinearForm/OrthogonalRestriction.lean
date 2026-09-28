import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic









set_option autoImplicit false

open scoped BigOperators

namespace Poincare.LinearAlgebra

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma sum_inner_sq (b : OrthonormalBasis ι ℝ E) (v : E) :
    (∑ i, (inner ℝ v (b i)) ^ 2) = inner ℝ v v := by
  simpa only [real_inner_comm (b _), pow_two] using b.sum_inner_mul_inner v v

private lemma sum_inner_project_sq (b : OrthonormalBasis ι ℝ E)
    (u v : E) (hu : inner ℝ u u = 1) :
    (∑ i, (inner ℝ v (b i - (inner ℝ u (b i)) • u)) ^ 2) =
      inner ℝ v v - (inner ℝ v u) ^ 2 := by
  have hcross : (∑ i, inner ℝ v (b i) * inner ℝ u (b i)) = inner ℝ v u := by
    simpa only [real_inner_comm (b _)] using b.sum_inner_mul_inner v u
  simp only [inner_sub_right, inner_smul_right]
  simp_rw [show ∀ a c d : ℝ, (a - c * d) ^ 2 = a ^ 2 - 2 * d * (a * c) + d ^ 2 * c ^ 2
    from fun a c d => by ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, sum_inner_sq, hcross, hu]
  ring



lemma sum_sq_orthogonal_restriction (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] E) (hA : ∀ v w, inner ℝ (A v) w = inner ℝ v (A w))
    (u : E) (hu : inner ℝ u u = 1) :
    (∑ i, ∑ j, (inner ℝ
      (A (b i - (inner ℝ u (b i)) • u))
      (b j - (inner ℝ u (b j)) • u)) ^ 2) =
      (∑ i, ∑ j, (inner ℝ (A (b i)) (b j)) ^ 2) -
        2 * inner ℝ (A u) (A u) + (inner ℝ (A u) u) ^ 2 := by
  have hcross : (∑ i, inner ℝ u (b i) * inner ℝ (A (b i)) (A u)) =
      inner ℝ (A u) (A u) := by
    simp_rw [hA]
    rw [b.sum_inner_mul_inner]
  have hnorm : (∑ i, inner ℝ (A (b i - (inner ℝ u (b i)) • u))
      (A (b i - (inner ℝ u (b i)) • u))) =
        (∑ i, inner ℝ (A (b i)) (A (b i))) - inner ℝ (A u) (A u) := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    conv_lhs =>
      arg 2
      ext i
      rw [real_inner_comm (A (b i)) (A u)]
    have heq (i : ι) :
        inner ℝ (A (b i)) (A (b i)) - inner ℝ u (b i) * inner ℝ (A (b i)) (A u) -
          (inner ℝ u (b i) * inner ℝ (A (b i)) (A u) -
            inner ℝ u (b i) * (inner ℝ u (b i) * inner ℝ (A u) (A u))) =
        inner ℝ (A (b i)) (A (b i)) -
          2 * (inner ℝ u (b i) * inner ℝ (A (b i)) (A u)) +
            inner ℝ (A u) (A u) * (inner ℝ u (b i)) ^ 2 := by ring
    simp_rw [heq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum, hcross, sum_inner_sq, hu]
    ring
  simp_rw [sum_inner_project_sq b u _ hu]
  rw [Finset.sum_sub_distrib, hnorm]
  have hnormal (i : ι) :
      inner ℝ (A (b i - (inner ℝ u (b i)) • u)) u =
        inner ℝ (A u) (b i - (inner ℝ u (b i)) • u) := by
    rw [hA, real_inner_comm]
  simp_rw [hnormal, sum_inner_project_sq b u (A u) hu, sum_inner_sq]
  ring


lemma trace_orthogonal_restriction (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] E) (hA : ∀ v w, inner ℝ (A v) w = inner ℝ v (A w))
    (u : E) (hu : inner ℝ u u = 1) :
    (∑ i, inner ℝ (A (b i - (inner ℝ u (b i)) • u))
      (b i - (inner ℝ u (b i)) • u)) =
        (∑ i, inner ℝ (A (b i)) (b i)) - inner ℝ (A u) u := by
  have hc : (∑ i, inner ℝ u (b i) * inner ℝ (A (b i)) u) = inner ℝ (A u) u := by
    simp_rw [hA]
    rw [b.sum_inner_mul_inner]
  have heq (i : ι) :
      inner ℝ (A (b i - (inner ℝ u (b i)) • u))
        (b i - (inner ℝ u (b i)) • u) =
      inner ℝ (A (b i)) (b i) - 2 * (inner ℝ u (b i) * inner ℝ (A (b i)) u) +
        inner ℝ (A u) u * (inner ℝ u (b i)) ^ 2 := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [hA (b i) u, real_inner_comm (A u) (b i)]
    ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, hc, sum_inner_sq, hu]
  ring


lemma gauss_term_orthogonal_restriction (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] E) (hA : ∀ v w, inner ℝ (A v) w = inner ℝ v (A w))
    (u : E) (hu : inner ℝ u u = 1) :
    (∑ i, inner ℝ (A (b i - (inner ℝ u (b i)) • u))
      (b i - (inner ℝ u (b i)) • u)) ^ 2 -
      (∑ i, ∑ j, (inner ℝ (A (b i - (inner ℝ u (b i)) • u))
        (b j - (inner ℝ u (b j)) • u)) ^ 2) =
    (∑ i, inner ℝ (A (b i)) (b i)) ^ 2 -
      (∑ i, ∑ j, (inner ℝ (A (b i)) (b j)) ^ 2) -
      2 * (∑ i, inner ℝ (A (b i)) (b i)) * inner ℝ (A u) u +
      2 * inner ℝ (A u) (A u) := by
  rw [trace_orthogonal_restriction b A hA u hu, sum_sq_orthogonal_restriction b A hA u hu]
  ring

end Poincare.LinearAlgebra
