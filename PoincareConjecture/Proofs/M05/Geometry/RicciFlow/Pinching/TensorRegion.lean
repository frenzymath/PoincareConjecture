import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.RegionTopology
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.OperatorFiber

set_option autoImplicit false

open PoincareConjecture TensorFiber

namespace Poincare.HamiltonIvey

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def tensorRegion (hn : Module.finrank ℝ E = 3) (t : ℝ) : Set (TensorFiber E 2) :=
  operatorTensorEquiv.symm ⁻¹' continuousRegion hn t

@[simp] theorem operatorTensor_mem_tensorRegion (hn : Module.finrank ℝ E = 3)
    (t : ℝ) (A : E →ₗ[ℝ] E) :
    operatorTensor A ∈ tensorRegion hn t ↔ A ∈ region hn t := by
  change operatorTensorEquiv.symm (operatorTensor A) ∈ continuousRegion hn t ↔ _
  have hA := operatorTensorEquiv_symm_apply (LinearMap.toContinuousLinearMap A)
  simp only [LinearMap.coe_toContinuousLinearMap] at hA
  rw [hA]
  rfl

theorem tensorRegion_eq_image (hn : Module.finrank ℝ E = 3) (t : ℝ) :
    tensorRegion hn t = operatorTensorEquiv '' continuousRegion hn t := by
  ext T
  constructor
  · intro hT
    exact ⟨operatorTensorEquiv.symm T, hT, operatorTensorEquiv.apply_symm_apply T⟩
  · rintro ⟨A, hA, rfl⟩
    simpa only [tensorRegion, Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hA

theorem isClosed_tensorRegion (hn : Module.finrank ℝ E = 3)
    {t : ℝ} (ht : 0 ≤ t) : IsClosed (tensorRegion hn t) :=
  (isClosed_continuousRegion hn ht).preimage operatorTensorEquiv.symm.continuous

theorem convex_tensorRegion (hn : Module.finrank ℝ E = 3)
    {t : ℝ} (ht : 0 ≤ t) : Convex ℝ (tensorRegion hn t) :=
  (convex_continuousRegion hn ht).linear_preimage operatorTensorEquiv.symm.toLinearMap

theorem tensorRegion_nonempty (hn : Module.finrank ℝ E = 3)
    {t : ℝ} (ht : 0 ≤ t) : (tensorRegion hn t).Nonempty := by
  rw [tensorRegion_eq_image]
  exact (continuousRegion_nonempty hn ht).image _

theorem isClosed_tensorRegion_spacetime (hn : Module.finrank ℝ E = 3) :
    IsClosed {p : ℝ × TensorFiber E 2 | 0 ≤ p.1 ∧ p.2 ∈ tensorRegion hn p.1} :=
  (isClosed_continuousRegion_spacetime hn).preimage
    (continuous_fst.prodMk (operatorTensorEquiv.symm.continuous.comp continuous_snd))

theorem tensorRegion_transport_equiv_iff
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hn : Module.finrank ℝ E = 3)
    (hm : Module.finrank ℝ F = 3) (e : E ≃ₗᵢ[ℝ] F)
    {t : ℝ} (ht : 0 ≤ t) (T : TensorFiber E 2) :
    TensorFiber.transport e 2 T ∈ tensorRegion hm t ↔ T ∈ tensorRegion hn t := by
  obtain ⟨A, rfl⟩ := operatorTensorEquiv.surjective T
  rw [operatorTensorEquiv_apply, transport_operatorTensor_eq,
    operatorTensor_mem_tensorRegion, operatorTensor_mem_tensorRegion]
  exact region_conj_equiv_iff hn hm e ht A.toLinearMap

theorem tensorRegion_transport_iff (hn : Module.finrank ℝ E = 3)
    (e : E ≃ₗᵢ[ℝ] E) {t : ℝ} (ht : 0 ≤ t) (T : TensorFiber E 2) :
    TensorFiber.transport e 2 T ∈ tensorRegion hn t ↔ T ∈ tensorRegion hn t :=
  tensorRegion_transport_equiv_iff hn hn e ht T

theorem tensorRegion_transport_image
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hn : Module.finrank ℝ E = 3)
    (hm : Module.finrank ℝ F = 3) (e : E ≃ₗᵢ[ℝ] F)
    {t : ℝ} (ht : 0 ≤ t) :
    TensorFiber.transport e 2 '' tensorRegion hn t = tensorRegion hm t := by
  ext T
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact (tensorRegion_transport_equiv_iff hn hm e ht S).mpr hS
  · intro hT
    obtain ⟨S, rfl⟩ := (TensorFiber.transport e 2).surjective T
    exact ⟨S, (tensorRegion_transport_equiv_iff hn hm e ht S).mp hT, rfl⟩

theorem tensorRegion_scale_iff (hn : Module.finrank ℝ E = 3)
    {t : ℝ} (ht : 0 ≤ t) (T : TensorFiber E 2) :
    T ∈ tensorRegion hn t ↔ (1 + t) • T ∈ tensorRegion hn 0 := by
  change operatorTensorEquiv.symm T ∈ continuousRegion hn t ↔
    operatorTensorEquiv.symm ((1 + t) • T) ∈ continuousRegion hn 0
  rw [map_smul]
  exact region_scale_iff hn ht (operatorTensorEquiv.symm T).toLinearMap

end Poincare.HamiltonIvey
