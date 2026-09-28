import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.ReactionSupport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.TensorReaction










set_option autoImplicit false

noncomputable section

open Set PoincareConjecture TensorFiber
open Poincare.HamiltonIvey
open scoped InnerProductSpace NNReal

namespace PoincareConjecture.AncientKappaRoundness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


def tensorPinchingCone (c : ℝ) : Set (TensorFiber E 2) :=
  operatorTensorEquiv.symm ⁻¹' pinchingCone c

@[simp] theorem operatorTensor_mem_tensorPinchingCone (c : ℝ) (A : E →ₗ[ℝ] E) :
    operatorTensor A ∈ tensorPinchingCone c ↔ A.toContinuousLinearMap ∈ pinchingCone c := by
  change operatorTensorEquiv.symm (operatorTensor A) ∈ pinchingCone c ↔ _
  have hA := operatorTensorEquiv_symm_apply A.toContinuousLinearMap
  simp only [LinearMap.coe_toContinuousLinearMap] at hA
  rw [hA]

theorem tensorPinchingCone_nonempty (c : ℝ) : (tensorPinchingCone (E := E) c).Nonempty := by
  refine ⟨0, ?_⟩
  change operatorTensorEquiv.symm 0 ∈ pinchingCone c
  simpa using zero_mem_pinchingCone (E := E) c

theorem isClosed_tensorPinchingCone (c : ℝ) : IsClosed (tensorPinchingCone (E := E) c) :=
  (isClosed_pinchingCone c).preimage operatorTensorEquiv.symm.continuous

theorem convex_tensorPinchingCone (c : ℝ) : Convex ℝ (tensorPinchingCone (E := E) c) :=
  (convex_pinchingCone c).linear_preimage operatorTensorEquiv.symm.toLinearMap

theorem tensorPinchingCone_transport_iff
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (e : E ≃ₗᵢ[ℝ] F) (c : ℝ) (T : TensorFiber E 2) :
    transport e 2 T ∈ tensorPinchingCone c ↔ T ∈ tensorPinchingCone c := by
  obtain ⟨A, rfl⟩ := operatorTensorEquiv.surjective T
  rw [operatorTensorEquiv_apply, transport_operatorTensor_eq,
    operatorTensor_mem_tensorPinchingCone, operatorTensor_mem_tensorPinchingCone]
  exact pinchingCone_conj_iff e c A.toLinearMap

theorem tensorPinchingCone_transport_image
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (e : E ≃ₗᵢ[ℝ] F) (c : ℝ) :
    transport e 2 '' tensorPinchingCone c = tensorPinchingCone c := by
  ext T
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact (tensorPinchingCone_transport_iff e c S).mpr hS
  · intro hT
    obtain ⟨S, rfl⟩ := (transport e 2).surjective T
    exact ⟨S, (tensorPinchingCone_transport_iff e c S).mp hT, rfl⟩


theorem tensorReaction_support_nonpos (hn : Module.finrank ℝ E = 3)
    {c : ℝ} (hc : 1 ≤ c) {T : TensorFiber E 2} (hT : T ∈ tensorPinchingCone c)
    (l : TensorFiber E 2 →L[ℝ] ℝ)
    (hsupport : ∀ S ∈ tensorPinchingCone c, l (S - T) ≤ 0) :
    l (tensorReaction T) ≤ 0 := by
  let A : E →L[ℝ] E := operatorTensorEquiv.symm T
  let l' : (E →L[ℝ] E) →L[ℝ] ℝ := l.comp operatorTensorEquiv.toContinuousLinearMap
  have hsupport' : ∀ B ∈ pinchingCone c, l' (B - A) ≤ 0 := by
    intro B hB
    have hmem : operatorTensorEquiv B ∈ tensorPinchingCone c := by
      change operatorTensorEquiv.symm (operatorTensorEquiv B) ∈ pinchingCone c
      simpa using hB
    change l (operatorTensorEquiv (B - A)) ≤ 0
    rw [map_sub]
    simpa only [A, ContinuousLinearEquiv.apply_symm_apply] using hsupport _ hmem
  exact reaction_support_nonpos hn hc hT l' hsupport'


theorem tensorReaction_inner_nonpos (hn : Module.finrank ℝ E = 3)
    {c : ℝ} (hc : 1 ≤ c) {q : TensorFiber E 2 × TensorFiber E 2}
    (hq : q ∈ Poincare.Parabolic.unitSupportSet (tensorPinchingCone c)) :
    ⟪q.2, tensorReaction q.1⟫_ℝ ≤ 0 :=
  tensorReaction_support_nonpos hn hc hq.1 (innerSL ℝ q.2) hq.2.2

end PoincareConjecture.AncientKappaRoundness
