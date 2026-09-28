
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.HilbertFiber











set_option autoImplicit false

open scoped InnerProductSpace

namespace PoincareConjecture

namespace TensorFiber

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]


noncomputable def operatorTensor (A : E →ₗ[ℝ] E) : TensorFiber E 2 :=
  toMultilinear.symm (MultilinearMap.mk'
    (fun v => ⟪v 0, A (v 1)⟫_ℝ)
    (by
      intros m i x y
      fin_cases i <;> simp [Function.update, inner_add_left, inner_add_right])
    (by
      intros m i c x
      fin_cases i <;> simp [Function.update, inner_smul_left, inner_smul_right]))

@[simp] theorem operatorTensor_apply (A : E →ₗ[ℝ] E) (v w : E) :
    operatorTensor A ![v, w] = ⟪v, A w⟫_ℝ := by
  rfl


noncomputable def operatorTensorLinear :
    (E →ₗ[ℝ] E) →ₗ[ℝ] TensorFiber E 2 where
  toFun := operatorTensor
  map_add' A B := by
    apply TensorFiber.ext
    intro v
    change _ = _
    simp [operatorTensor, LinearMap.add_apply, inner_add_right]
  map_smul' c A := by
    apply TensorFiber.ext
    intro v
    change _ = _
    simp [operatorTensor, LinearMap.smul_apply, inner_smul_right]

@[simp] theorem operatorTensorLinear_apply (A : E →ₗ[ℝ] E) :
    operatorTensorLinear A = operatorTensor A := rfl

theorem operatorTensor_injective : Function.Injective (operatorTensor (E := E)) := by
  intro A B h
  apply LinearMap.ext
  intro w
  apply (InnerProductSpace.toDualMap ℝ E).injective
  ext v
  have hv := congrArg (fun T : TensorFiber E 2 => T ![v, w]) h
  simpa only [operatorTensor_apply, InnerProductSpace.toDualMap_apply_apply,
    real_inner_comm] using hv



noncomputable def operatorTensorEquiv : (E →L[ℝ] E) ≃L[ℝ] TensorFiber E 2 :=
  (LinearMap.toContinuousLinearMap.symm.trans
    (LinearEquiv.ofInjectiveOfFinrankEq operatorTensorLinear operatorTensor_injective (by
      rw [Module.finrank_linearMap, toMultilinear.finrank_eq]
      let b := Basis.multilinearMap (fun _ : Fin 2 => (stdOrthonormalBasis ℝ E).toBasis)
        (Module.Basis.singleton Unit ℝ)
      rw [Module.finrank_eq_card_basis b]
      simp [pow_two]))).toContinuousLinearEquiv

@[simp] theorem operatorTensorEquiv_apply (A : E →L[ℝ] E) :
    operatorTensorEquiv A = operatorTensor A.toLinearMap := rfl

@[simp] theorem operatorTensorEquiv_symm_apply (A : E →L[ℝ] E) :
    operatorTensorEquiv.symm (operatorTensor A.toLinearMap) = A := by
  rw [← operatorTensorEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]



theorem transport_operatorTensor (e : E ≃ₗᵢ[ℝ] F) (A : E →ₗ[ℝ] E)
    (v w : F) :
    TensorFiber.transport e 2 (operatorTensor A) ![v, w] =
      ⟪v, (e.toLinearEquiv.conj A) w⟫_ℝ := by
  rw [TensorFiber.transport_apply]
  change ⟪e.symm v, A (e.symm w)⟫_ℝ = _
  rw [← e.inner_map_map (e.symm v) (A (e.symm w))]
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, e.apply_symm_apply]
  rfl


theorem transport_operatorTensor_eq (e : E ≃ₗᵢ[ℝ] F) (A : E →ₗ[ℝ] E) :
    TensorFiber.transport e 2 (operatorTensor A) =
      operatorTensor (e.toLinearEquiv.conj A) := by
  apply TensorFiber.ext
  intro v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, transport_operatorTensor, operatorTensor_apply]

end TensorFiber

end PoincareConjecture
