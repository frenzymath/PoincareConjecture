import Mathlib

namespace Poincare

abbrev ThreeVector := Fin 3 → ℝ

def diagonalSpectrum (k₁ k₂ k₃ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![k₁, k₂, k₃]

def rayleighValue (A : Matrix (Fin 3) (Fin 3) ℝ) (v : ThreeVector) : ℝ :=
  dotProduct v (Matrix.mulVec A v)

def frobeniusSq (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

theorem diagonalSpectrum_isSymm (k₁ k₂ k₃ : ℝ) :
    (diagonalSpectrum k₁ k₂ k₃).IsSymm := by
  simp [diagonalSpectrum, Matrix.IsSymm]

theorem diagonalSpectrum_trace (k₁ k₂ k₃ : ℝ) :
    Matrix.trace (diagonalSpectrum k₁ k₂ k₃) = k₁ + k₂ + k₃ := by
  rw [Matrix.trace_fin_three]
  simp [diagonalSpectrum]

theorem diagonalSpectrum_frobeniusSq (k₁ k₂ k₃ : ℝ) :
    frobeniusSq (diagonalSpectrum k₁ k₂ k₃) =
      k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 := by
  simp [frobeniusSq, diagonalSpectrum, Fin.sum_univ_succ]
  ring_nf

theorem diagonalSpectrum_rayleigh (k₁ k₂ k₃ : ℝ) (v : ThreeVector) :
    rayleighValue (diagonalSpectrum k₁ k₂ k₃) v =
      k₁ * v 0 ^ 2 + k₂ * v 1 ^ 2 + k₃ * v 2 ^ 2 := by
  simp [rayleighValue, diagonalSpectrum, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  ring

theorem diagonalSpectrum_rayleigh_ge_least
    {k₁ k₂ k₃ : ℝ} (h₁₂ : k₂ ≤ k₁) (h₂₃ : k₃ ≤ k₂)
    {v : ThreeVector} (hv : dotProduct v v = 1) :
    k₃ ≤ rayleighValue (diagonalSpectrum k₁ k₂ k₃) v := by
  have hsq₀ : 0 ≤ v 0 ^ 2 := sq_nonneg _
  have hsq₁ : 0 ≤ v 1 ^ 2 := sq_nonneg _
  have hsq₂ : 0 ≤ v 2 ^ 2 := sq_nonneg _
  have hv' : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_succ, pow_two, add_assoc] using hv
  rw [diagonalSpectrum_rayleigh]
  have hd₁ : 0 ≤ (k₁ - k₃) * v 0 ^ 2 :=
    mul_nonneg (by linarith) hsq₀
  have hd₂ : 0 ≤ (k₂ - k₃) * v 1 ^ 2 :=
    mul_nonneg (by linarith) hsq₁
  calc
    k₃ ≤ k₃ * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by simp [hv']
    _ ≤ k₁ * v 0 ^ 2 + k₂ * v 1 ^ 2 + k₃ * v 2 ^ 2 := by nlinarith

theorem diagonalSpectrum_rayleigh_attains_least {k₁ k₂ k₃ : ℝ} :
    ∃ v : ThreeVector,
      dotProduct v v = 1 ∧
        rayleighValue (diagonalSpectrum k₁ k₂ k₃) v = k₃ := by
  refine ⟨![0, 0, 1], ?_, ?_⟩
  · simp [dotProduct, Fin.sum_univ_succ]
  · simp [rayleighValue, diagonalSpectrum, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem diagonalSpectrum_isLeastRayleigh
    {k₁ k₂ k₃ : ℝ} (h₁₂ : k₂ ≤ k₁) (h₂₃ : k₃ ≤ k₂) :
    (∀ v : ThreeVector, dotProduct v v = 1 →
      k₃ ≤ rayleighValue (diagonalSpectrum k₁ k₂ k₃) v) ∧
    (∃ v : ThreeVector, dotProduct v v = 1 ∧
      rayleighValue (diagonalSpectrum k₁ k₂ k₃) v = k₃) := by
  constructor
  · intro v hv
    exact diagonalSpectrum_rayleigh_ge_least h₁₂ h₂₃ hv
  · exact diagonalSpectrum_rayleigh_attains_least

section SymmetricEndomorphism

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem symmetric_rayleigh_eq_sum_eigenvalues
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
  {n : ℕ} (hn : Module.finrank ℝ E = n) (v : E) :
    inner ℝ v (T v) =
      ∑ i, hT.eigenvalues hn i * (inner ℝ ((hT.eigenvectorBasis hn) i) v) ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.inner_map_map v (T v)]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial,
    hT.eigenvectorBasis_apply_self_apply hn]
  simp only [(hT.eigenvectorBasis hn).repr_apply_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

theorem symmetric_unit_coordinates_sum_sq
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) {v : E} (hv : ‖v‖ = 1) :
    ∑ i, (inner ℝ ((hT.eigenvectorBasis hn) i) v) ^ 2 = 1 := by
  simpa [hv] using (hT.eigenvectorBasis hn).sum_sq_inner_right v

theorem symmetric_eigenbasis_energy
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) :
    (∑ i, ‖T ((hT.eigenvectorBasis hn) i)‖ ^ 2) =
      ∑ i, (hT.eigenvalues hn i) ^ 2 := by
  simp_rw [hT.apply_eigenvectorBasis hn, norm_smul]
  simp

theorem symmetric_three_rayleigh_ge_least
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = 3) {v : E} (hv : ‖v‖ = 1) :
    hT.eigenvalues hn 2 ≤ inner ℝ v (T v) := by
  have hsq := symmetric_unit_coordinates_sum_sq hT hn hv
  rw [symmetric_rayleigh_eq_sum_eigenvalues hT hn]
  calc
    hT.eigenvalues hn 2 =
        ∑ i, hT.eigenvalues hn 2 * (inner ℝ ((hT.eigenvectorBasis hn) i) v) ^ 2 := by
      rw [← Finset.mul_sum, hsq, mul_one]
    _ ≤ ∑ i, hT.eigenvalues hn i * (inner ℝ ((hT.eigenvectorBasis hn) i) v) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (hT.eigenvalues_antitone hn (by omega)) (sq_nonneg _)

theorem symmetric_three_rayleigh_attains_least
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = 3) :
    ∃ v : E, ‖v‖ = 1 ∧ inner ℝ v (T v) = hT.eigenvalues hn 2 := by
  refine ⟨hT.eigenvectorBasis hn 2, (hT.eigenvectorBasis hn).orthonormal.1 2, ?_⟩
  rw [hT.apply_eigenvectorBasis hn 2, inner_smul_right]
  simp [(hT.eigenvectorBasis hn).orthonormal.1 2]

end SymmetricEndomorphism

end Poincare
