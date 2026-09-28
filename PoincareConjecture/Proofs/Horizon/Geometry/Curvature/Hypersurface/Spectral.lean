import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Algebra

set_option autoImplicit false

open scoped BigOperators InnerProductSpace

namespace Poincare.Geometry.Curvature.Hypersurface

theorem symmetric_operator_extrinsic_determinant_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ} (hn : Module.finrank ℝ E = m + 1)
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (β : ℝ)
    (hupper : ∀ i, hA.eigenvalues hn i ≤ β) (hβ : 0 ≤ β)
    (u v : E) (hu : ⟪u, u⟫_ℝ = 1) (hv : ⟪v, v⟫_ℝ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) :
    -(negativePart (A.trace ℝ E) + (m : ℝ) * β) * β ≤
      ⟪A u, u⟫_ℝ * ⟪A v, v⟫_ℝ - ⟪A u, v⟫_ℝ ^ 2 := by
  let b := hA.eigenvectorBasis hn
  have hinner (x y : E) :
      ⟪x, y⟫_ℝ = ∑ i, b.repr x i * b.repr y i := by
    have heq := b.repr.inner_map_map x y
    rw [PiLp.inner_apply] at heq
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using heq.symm
  have happly (x y : E) :
      ⟪A x, y⟫_ℝ = ∑ i, hA.eigenvalues hn i * b.repr x i * b.repr y i := by
    rw [hinner]
    simp only [b, hA.eigenvectorBasis_apply_self_apply, RCLike.ofReal_real_eq_id, id_eq]
  have hsq (x : E) :
      ⟪A x, x⟫_ℝ = ∑ i, hA.eigenvalues hn i * (b.repr x i) ^ 2 := by
    rw [happly]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsq, hsq, happly]
  apply diagonal_extrinsic_determinant_lower_bound_of_card
    (hA.eigenvalues hn) (fun i => b.repr u i) (fun i => b.repr v i)
    (A.trace ℝ E) β (hA.trace_eq_sum_eigenvalues hn) hupper hβ
  · simpa only [hinner, pow_two] using hu
  · simpa only [hinner, pow_two] using hv
  · simpa only [hinner] using huv

end Poincare.Geometry.Curvature.Hypersurface
