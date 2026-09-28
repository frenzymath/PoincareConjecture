import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

set_option autoImplicit false

open scoped BigOperators RealInnerProductSpace

namespace PoincareConjecture.Homothety

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem sum_sq_linear_basis_eq (L : E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, (L (b i)) ^ 2) = ∑ j, (L (c j)) ^ 2 := by
  let v := (InnerProductSpace.toDual ℝ E).symm L.toContinuousLinearMap
  have hv (x : E) : inner ℝ v x = L x := InnerProductSpace.toDual_symm_apply
  calc
    (∑ i, (L (b i)) ^ 2) = ‖v‖ ^ 2 := by
      simpa only [hv] using b.sum_sq_inner_left v
    _ = ∑ j, (L (c j)) ^ 2 := by
      simpa only [hv] using (c.sum_sq_inner_left v).symm

theorem sum_bilinear_diagonal_basis_eq (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, B (b i) (b i)) = ∑ j, B (c j) (c j) := by
  let v (j : κ) := (InnerProductSpace.toDual ℝ E).symm
    (B.toContinuousBilinearMap (c j))
  have hv (j : κ) (x : E) : inner ℝ (v j) x = B (c j) x :=
    InnerProductSpace.toDual_symm_apply
  calc
    (∑ i, B (b i) (b i)) = ∑ i, ∑ j, inner ℝ (c j) (b i) * B (c j) (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        B (b i) (b i) = B (∑ j, inner ℝ (c j) (b i) • c j) (b i) :=
          congrArg (fun y ↦ B y (b i)) (c.sum_repr' (b i)).symm
        _ = _ := by simp only [map_sum, map_smul, LinearMap.sum_apply,
          LinearMap.smul_apply, smul_eq_mul]
    _ = ∑ j, ∑ i, inner ℝ (c j) (b i) * B (c j) (b i) := Finset.sum_comm
    _ = ∑ j, B (c j) (c j) := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        (∑ i, inner ℝ (c j) (b i) * B (c j) (b i)) =
            ∑ i, inner ℝ (c j) (b i) * inner ℝ (b i) (v j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← hv j (b i), real_inner_comm (v j) (b i)]
        _ = inner ℝ (c j) (v j) := b.sum_inner_mul_inner _ _
        _ = B (c j) (c j) := (real_inner_comm _ _).trans (hv j (c j))

theorem sum_sq_bilinear_basis_eq (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, ∑ j, (B (b i) (b j)) ^ 2) = ∑ i, ∑ j, (B (c i) (c j)) ^ 2 := by
  calc
    (∑ i, ∑ j, (B (b i) (b j)) ^ 2) = ∑ i, ∑ j, (B (b i) (c j)) ^ 2 :=
      Finset.sum_congr rfl (fun i _ ↦ sum_sq_linear_basis_eq (B (b i)) b c)
    _ = ∑ j, ∑ i, (B (b i) (c j)) ^ 2 := Finset.sum_comm
    _ = ∑ j, ∑ i, (B (c i) (c j)) ^ 2 :=
      Finset.sum_congr rfl (fun j _ ↦ sum_sq_linear_basis_eq (B.flip (c j)) b c)
    _ = ∑ i, ∑ j, (B (c i) (c j)) ^ 2 := Finset.sum_comm

def fourLinearFirstTwo (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (w z : E) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v ↦ T u v w z)
    (fun u u' v ↦ by simp)
    (fun a u v ↦ by simp)
    (fun u v v' ↦ by simp)
    (fun a u v ↦ by simp)

omit [FiniteDimensional ℝ E] in
theorem fourLinearFirstTwo_apply (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (u v w z : E) : fourLinearFirstTwo T w z u v = T u v w z := rfl

theorem sum_four_swap_pairs {μ ν : Type*} [Fintype μ] [Fintype ν]
    (F : ι → κ → μ → ν → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
  calc
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ k, ∑ j, ∑ l, F i j k l :=
      Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_comm)
    _ = ∑ k, ∑ i, ∑ j, ∑ l, F i j k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, F i j k l :=
      Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_comm))
    _ = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l :=
      Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_comm)

theorem sum_sq_fourlinear_basis_eq
    (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, ∑ j, ∑ k, ∑ l, (T (b i) (b j) (b k) (b l)) ^ 2) =
      ∑ i, ∑ j, ∑ k, ∑ l, (T (c i) (c j) (c k) (c l)) ^ 2 := by
  calc
    (∑ i, ∑ j, ∑ k, ∑ l, (T (b i) (b j) (b k) (b l)) ^ 2) =
        ∑ i, ∑ j, ∑ k, ∑ l, (T (b i) (b j) (c k) (c l)) ^ 2 :=
      Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl
        (fun j _ ↦ sum_sq_bilinear_basis_eq (T (b i) (b j)) b c))
    _ = ∑ k, ∑ l, ∑ i, ∑ j, (T (b i) (b j) (c k) (c l)) ^ 2 :=
      sum_four_swap_pairs _
    _ = ∑ k, ∑ l, ∑ i, ∑ j, (T (c i) (c j) (c k) (c l)) ^ 2 :=
      Finset.sum_congr rfl (fun k _ ↦ Finset.sum_congr rfl
        (fun l _ ↦ sum_sq_bilinear_basis_eq (fourLinearFirstTwo T (c k) (c l)) b c))
    _ = ∑ i, ∑ j, ∑ k, ∑ l, (T (c i) (c j) (c k) (c l)) ^ 2 :=
      (sum_four_swap_pairs _).symm

end PoincareConjecture.Homothety
