import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Region
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Spectrum

namespace Poincare.HamiltonIvey

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem diagonal_rayleigh_eq_sum
    {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (e : OrthonormalBasis (Fin 3) ℝ E) {d : Fin 3 → ℝ}
    (hd : ∀ i, A (e i) = d i • e i) (v : E) :
    inner ℝ v (A v) = ∑ i, d i * (inner ℝ (e i) v) ^ 2 := by
  have hcoord : ∀ i, e.repr (A v) i = d i * e.repr v i := by
    intro i
    rw [e.repr_apply_apply, e.repr_apply_apply, ← hA, hd, inner_smul_left]
    simp
  rw [← e.repr.inner_map_map v (A v), EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial, hcoord, e.repr_apply_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

omit [FiniteDimensional ℝ E] in
theorem diagonal_rayleigh_ge_least
    {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (e : OrthonormalBasis (Fin 3) ℝ E) {d : Fin 3 → ℝ}
    (hd : ∀ i, A (e i) = d i • e i) (horder : Antitone d)
    {v : E} (hv : ‖v‖ = 1) :
    d 2 ≤ inner ℝ v (A v) := by
  have hsq : ∑ i, (inner ℝ (e i) v) ^ 2 = 1 := by
    simpa [hv] using e.sum_sq_inner_right v
  rw [diagonal_rayleigh_eq_sum hA e hd]
  calc
    d 2 = ∑ i, d 2 * (inner ℝ (e i) v) ^ 2 := by
      rw [← Finset.mul_sum, hsq, mul_one]
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (horder (by omega)) (sq_nonneg _)

theorem diagonal_least_eigenvalue
    (hn : Module.finrank ℝ E = 3) {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (e : OrthonormalBasis (Fin 3) ℝ E) {d : Fin 3 → ℝ}
    (hd : ∀ i, A (e i) = d i • e i) (horder : Antitone d) :
    hA.eigenvalues hn 2 = d 2 := by
  apply le_antisymm
  · have h := Poincare.symmetric_three_rayleigh_ge_least hA hn (e.orthonormal.1 2)
    simpa [hd, inner_smul_right, e.orthonormal.1 2] using h
  · obtain ⟨v, hv, heq⟩ := Poincare.symmetric_three_rayleigh_attains_least hA hn
    rw [← heq]
    exact diagonal_rayleigh_ge_least hA e hd horder hv

omit [FiniteDimensional ℝ E] in
theorem diagonal_trace
    {A : E →ₗ[ℝ] E} (e : OrthonormalBasis (Fin 3) ℝ E) {d : Fin 3 → ℝ}
    (hd : ∀ i, A (e i) = d i • e i) :
    LinearMap.trace ℝ E A = ∑ i, d i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ e.toBasis]
  simp [Matrix.trace, LinearMap.toMatrix_apply, hd]

theorem mem_region_iff_diagonal
    (hn : Module.finrank ℝ E = 3) {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (e : OrthonormalBasis (Fin 3) ℝ E) {d : Fin 3 → ℝ}
    (hd : ∀ i, A (e i) = d i • e i) (horder : Antitone d) (t : ℝ) :
    A ∈ region hn t ↔ (∑ i, d i, max (-d 2) 0) ∈ scalarRegion t := by
  constructor
  · rintro ⟨h, hm⟩
    simpa only [diagonal_trace e hd, diagonal_least_eigenvalue hn h e hd horder] using hm
  · intro hm
    refine ⟨hA, ?_⟩
    simpa only [diagonal_trace e hd, diagonal_least_eigenvalue hn hA e hd horder] using hm

end Poincare.HamiltonIvey
