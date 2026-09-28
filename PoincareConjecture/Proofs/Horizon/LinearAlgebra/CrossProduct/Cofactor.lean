import PoincareConjecture.Proofs.Horizon.LinearAlgebra.CrossProduct.Orthonormal
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin








open Matrix

namespace Poincare.LinearAlgebra


theorem adjugate_transpose_mulVec_crossProduct
    (A : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    A.adjugate.transpose *ᵥ (u ⨯₃ v) = (A *ᵥ u) ⨯₃ (A *ᵥ v) := by
  rw [adjugate_fin_three]
  ext i
  fin_cases i <;>
    simp [cross_apply, mulVec, vec3_dotProduct, transpose_apply] <;> ring


noncomputable def cofactorNormal
    (A : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (LinearMap.toMatrix' A).adjugate.transpose *ᵥ p


theorem cofactorNormal_dot_apply_eq_zero
    (A : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (p v : Fin 3 → ℝ)
    (hv : p ⬝ᵥ v = 0) : cofactorNormal A p ⬝ᵥ A v = 0 := by
  rw [cofactorNormal, dotProduct_comm, dotProduct_transpose_mulVec,
    ← LinearMap.toMatrix'_mulVec A v, mulVec_mulVec, adjugate_mul,
    smul_mulVec, one_mulVec, dotProduct_smul, hv, smul_zero]


theorem cofactorNormal_ne_zero
    (A : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (p : Fin 3 → ℝ)
    (hp : p ⬝ᵥ p = 1)
    (hA : Set.InjOn A {v | p ⬝ᵥ v = 0}) : cofactorNormal A p ≠ 0 := by
  obtain ⟨u, v, hu, hv, huv, huv_eq⟩ := exists_orthonormal_crossProduct_coordinates p hp
  have hpu : p ⬝ᵥ u = 0 := by rw [← huv_eq, dotProduct_comm, dot_self_cross]
  have hpv : p ⬝ᵥ v = 0 := by rw [← huv_eq, dotProduct_comm, dot_cross_self]
  have hcross : cofactorNormal A p = A u ⨯₃ A v := by
    rw [cofactorNormal, ← huv_eq, adjugate_transpose_mulVec_crossProduct]
    simp only [LinearMap.toMatrix'_mulVec]
  rw [hcross, crossProduct_ne_zero_iff_linearIndependent, LinearIndependent.pair_iff]
  intro a b hab
  have hpre : a • u + b • v = 0 := by
    apply hA
    · simp only [Set.mem_ofPred_eq, dotProduct_add, dotProduct_smul, hpu, hpv,
        smul_zero, add_zero]
    · simp
    · simpa using hab
  have ha := congrArg (fun w => u ⬝ᵥ w) hpre
  have hb := congrArg (fun w => v ⬝ᵥ w) hpre
  have hvu : v ⬝ᵥ u = 0 := by rwa [dotProduct_comm]
  simpa [dotProduct_add, dotProduct_smul, hu, hv, huv, hvu] using And.intro ha hb


theorem injective_tangent_add_cofactorNormal
    (A : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (p : Fin 3 → ℝ)
    (hp : p ⬝ᵥ p = 1)
    (hA : Set.InjOn A {v | p ⬝ᵥ v = 0}) :
    Function.Injective fun v =>
      A (v - (p ⬝ᵥ v) • p) + (p ⬝ᵥ v) • cofactorNormal A p := by
  have hproj (v : Fin 3 → ℝ) : p ⬝ᵥ (v - (p ⬝ᵥ v) • p) = 0 := by
    simp [dotProduct_sub, dotProduct_smul, hp]
  have hnormal (v : Fin 3 → ℝ) :
      cofactorNormal A p ⬝ᵥ A (v - (p ⬝ᵥ v) • p) = 0 :=
    cofactorNormal_dot_apply_eq_zero A p _ (hproj v)
  have hnn : cofactorNormal A p ⬝ᵥ cofactorNormal A p ≠ 0 := by
    simpa only [ne_eq, dotProduct_self_eq_zero] using cofactorNormal_ne_zero A p hp hA
  intro u v huv
  dsimp only at huv
  have hdot := congrArg (fun w => cofactorNormal A p ⬝ᵥ w) huv
  simp only [dotProduct_add, dotProduct_smul, hnormal, zero_add, smul_eq_mul] at hdot
  have huv' : p ⬝ᵥ u = p ⬝ᵥ v := mul_right_cancel₀ hnn hdot
  have hproj_eq : u - (p ⬝ᵥ u) • p = v - (p ⬝ᵥ v) • p := by
    apply hA (hproj u) (hproj v)
    exact add_right_cancel (huv.trans (by rw [huv']))
  rwa [huv', sub_left_inj] at hproj_eq


noncomputable def euclideanCoordinateLinearMap
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap.comp
    (A.toLinearMap.comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap)

@[simp]
theorem euclideanCoordinateLinearMap_apply
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) (v : Fin 3 → ℝ) :
    euclideanCoordinateLinearMap A v = (A (WithLp.toLp 2 v)).ofLp := rfl


noncomputable def euclideanCofactorNormal
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (p : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (cofactorNormal (euclideanCoordinateLinearMap A) p)

private theorem inner_eq_dotProduct (p v : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ p v = p ⬝ᵥ v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]


theorem inner_euclideanCofactorNormal_apply_eq_zero
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (p v : EuclideanSpace ℝ (Fin 3)) (hv : inner ℝ p v = 0) :
    inner ℝ (euclideanCofactorNormal A p) (A v) = 0 := by
  simp only [inner_eq_dotProduct] at hv ⊢
  exact cofactorNormal_dot_apply_eq_zero (euclideanCoordinateLinearMap A) p v hv


theorem euclideanCofactorNormal_ne_zero
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (p : EuclideanSpace ℝ (Fin 3)) (hp : inner ℝ p p = 1)
    (hA : Set.InjOn A {v | inner ℝ p v = 0}) : euclideanCofactorNormal A p ≠ 0 := by
  have hAc : Set.InjOn (euclideanCoordinateLinearMap A) {v | p ⬝ᵥ v = 0} := by
    intro u hu v hv huv
    have h := hA (x₁ := WithLp.toLp 2 u) (x₂ := WithLp.toLp 2 v)
      (by simpa only [Set.mem_ofPred_eq, inner_eq_dotProduct, WithLp.ofLp_toLp] using hu)
      (by simpa only [Set.mem_ofPred_eq, inner_eq_dotProduct, WithLp.ofLp_toLp] using hv)
      (WithLp.ofLp_injective 2 huv)
    exact congrArg WithLp.ofLp h
  have hpc : p ⬝ᵥ p = 1 := by
    simpa only [inner_eq_dotProduct] using hp
  intro h
  exact cofactorNormal_ne_zero _ _ hpc hAc (congrArg WithLp.ofLp h)


theorem injective_tangent_add_euclideanCofactorNormal
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (p : EuclideanSpace ℝ (Fin 3)) (hp : inner ℝ p p = 1)
    (hA : Set.InjOn A {v | inner ℝ p v = 0}) :
    Function.Injective fun v =>
      A (v - (inner ℝ p v) • p) + (inner ℝ p v) • euclideanCofactorNormal A p := by
  have hAc : Set.InjOn (euclideanCoordinateLinearMap A) {v | p ⬝ᵥ v = 0} := by
    intro u hu v hv huv
    have h := hA (x₁ := WithLp.toLp 2 u) (x₂ := WithLp.toLp 2 v)
      (by simpa only [Set.mem_ofPred_eq, inner_eq_dotProduct, WithLp.ofLp_toLp] using hu)
      (by simpa only [Set.mem_ofPred_eq, inner_eq_dotProduct, WithLp.ofLp_toLp] using hv)
      (WithLp.ofLp_injective 2 huv)
    exact congrArg WithLp.ofLp h
  have hpc : p ⬝ᵥ p = 1 := by
    simpa only [inner_eq_dotProduct] using hp
  intro u v huv
  apply WithLp.ofLp_injective
  apply injective_tangent_add_cofactorNormal _ _ hpc hAc
  simpa only [inner_eq_dotProduct, euclideanCoordinateLinearMap_apply, euclideanCofactorNormal,
    WithLp.ofLp_add, WithLp.ofLp_smul,
    WithLp.toLp_sub, WithLp.toLp_smul, WithLp.toLp_ofLp, WithLp.ofLp_toLp] using
    congrArg WithLp.ofLp huv



theorem orthogonal_tangent_iff_smul_euclideanCofactorNormal
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (p w : EuclideanSpace ℝ (Fin 3)) (hp : inner ℝ p p = 1)
    (hA : Set.InjOn A {v | inner ℝ p v = 0}) :
    (∀ v, inner ℝ p v = 0 → inner ℝ w (A v) = 0) ↔
      ∃ c : ℝ, w = c • euclideanCofactorNormal A p := by
  let N := euclideanCofactorNormal A p
  let B : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    A.toLinearMap.comp (LinearMap.id - (innerSL ℝ p).toLinearMap.smulRight p) +
      (innerSL ℝ p).toLinearMap.smulRight N
  have hB (v) : B v = A (v - inner ℝ p v • p) + inner ℝ p v • N := rfl
  constructor
  · intro hw
    have hi : Function.Injective B := injective_tangent_add_euclideanCofactorNormal A p hp hA
    obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hi) w
    have ht : inner ℝ p (v - inner ℝ p v • p) = 0 := by
      simp only [inner_sub_right, inner_smul_right, hp, mul_one, sub_self]
    have hz := hw (v - inner ℝ p v • p) ht
    rw [← hv, hB, inner_add_left, inner_smul_left,
      inner_euclideanCofactorNormal_apply_eq_zero A p _ ht, mul_zero, add_zero] at hz
    have hzero := inner_self_eq_zero.mp hz
    refine ⟨inner ℝ p v, ?_⟩
    rw [← hv, hB, hzero, zero_add]
  · rintro ⟨c, rfl⟩ v hv
    rw [inner_smul_left, inner_euclideanCofactorNormal_apply_eq_zero A p v hv, mul_zero]

end Poincare.LinearAlgebra
