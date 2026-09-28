import PoincareConjecture.Proofs.M03.Existence.HilbertEigenbasisNative
import PoincareConjecture.Proofs.M03.Existence.SpectralShiftedNative









set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace PoincareConjecture.HilbertResolventNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def formEigenvector (J : V →L[ℝ] H) (hc : IsCompactOperator J) (i : EigenIndex J) : V :=
  (Real.sqrt i.1.val)⁻¹ • J.adjoint (eigenvector J hc i)

theorem formEigenvector_pairing (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (i : EigenIndex J) (v : V) :
    inner ℝ (formEigenvector J hc i) v =
      (Real.sqrt i.1.val)⁻¹ * inner ℝ (eigenvector J hc i) (J v) := by
  rw [formEigenvector, real_inner_smul_left, J.adjoint_inner_left]

theorem inner_formEigenvector (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (i j : EigenIndex J) :
    inner ℝ (formEigenvector J hc i) (formEigenvector J hc j) =
      if i = j then 1 else 0 := by
  classical
  simp only [formEigenvector, real_inner_smul_left, real_inner_smul_right]
  rw [← inner_operator_right, operator_eigenvector, real_inner_smul_right]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, real_inner_self_eq_norm_sq, (eigenvector_orthonormal J hc).norm_eq_one]
    have hpos := eigenparameter_pos J hc hd i
    have hsqrt := Real.sq_sqrt hpos.le
    have hnz := (Real.sqrt_pos.mpr hpos).ne'
    field_simp
    nlinarith
  · rw [if_neg hij, (eigenvector_orthonormal J hc).inner_eq_zero hij]
    ring

theorem formEigenvector_orthonormal (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) : Orthonormal ℝ (formEigenvector J hc) := by
  classical
  exact orthonormal_iff_ite.mpr (inner_formEigenvector J hc hd)

theorem formEigenvectors_total (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hinj : Function.Injective J) :
    (Submodule.span ℝ (Set.range (formEigenvector J hc)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  apply hinj
  rw [map_zero]
  apply (eigenbasis J hc hd).repr.injective
  apply lp.ext
  funext i
  simp only [map_zero, lp.coeFn_zero, Pi.zero_apply, HilbertBasis.repr_apply_apply, eigenbasis_apply]
  have hz := Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (show formEigenvector J hc i ∈ Set.range (formEigenvector J hc)
      from ⟨i, rfl⟩)) hv
  rw [formEigenvector_pairing] at hz
  exact (mul_eq_zero.mp hz).resolve_left
    (inv_ne_zero ((Real.sqrt_pos.mpr (eigenparameter_pos J hc hd i)).ne'))

def formEigenbasis (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hinj : Function.Injective J) : HilbertBasis (EigenIndex J) ℝ V :=
  HilbertBasis.mkOfOrthogonalEqBot (formEigenvector_orthonormal J hc hd)
    (formEigenvectors_total J hc hd hinj)

@[simp] theorem formEigenbasis_apply (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hinj : Function.Injective J) (i : EigenIndex J) :
    formEigenbasis J hc hd hinj i = formEigenvector J hc i := by
  simp only [formEigenbasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem inclusion_formEigenvector (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (i : EigenIndex J) :
    J (formEigenvector J hc i) = Real.sqrt i.1.val • eigenvector J hc i := by
  rw [formEigenvector, map_smul, ← operator_apply, operator_eigenvector, smul_smul]
  have hpos := eigenparameter_pos J hc hd i
  have hsqrt := Real.sq_sqrt hpos.le
  have hnz := (Real.sqrt_pos.mpr hpos).ne'
  congr 1
  field_simp
  nlinarith

theorem repr_inclusion (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hinj : Function.Injective J) (v : V) (i : EigenIndex J) :
    (eigenbasis J hc hd).repr (J v) i =
      Real.sqrt i.1.val * (formEigenbasis J hc hd hinj).repr v i := by
  simp only [HilbertBasis.repr_apply_apply, eigenbasis_apply, formEigenbasis_apply,
    formEigenvector_pairing]
  rw [← mul_assoc, mul_inv_cancel₀ ((Real.sqrt_pos.mpr (eigenparameter_pos J hc hd i)).ne'),
    one_mul]

theorem repr_inclusion_decode (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hinj : Function.Injective J)
    (z : SpectralHeatNative.State (EigenIndex J)) (i : EigenIndex J) :
    (eigenbasis J hc hd).repr (J ((formEigenbasis J hc hd hinj).repr.symm z)) i =
      Real.sqrt i.1.val * z i := by
  rw [repr_inclusion J hc hd hinj, LinearIsometryEquiv.apply_symm_apply]

theorem sqrt_eigenparameter_mul_shifted (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (i : EigenIndex J) :
    Real.sqrt i.1.val * Real.sqrt (1 + (generatorParameters J hc hd hnorm i : ℝ)) = 1 := by
  rw [← Real.sqrt_mul (eigenparameter_pos J hc hd i).le]
  have hproduct : i.1.val * (1 + (generatorParameters J hc hd hnorm i : ℝ)) = 1 := by
    rw [mul_comm]
    exact parameter_resolvent_identity i.1.val (eigenparameter_pos J hc hd i)
      (eigenparameter_le_one J hc hd hnorm i)
  rw [hproduct, Real.sqrt_one]

open SpectralHeatNative (ForcingSpace)


def formResponsePath [SeparableSpace H]
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hinj : Function.Injective J) (hnorm : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (F : ForcingSpace (EigenIndex J) T) : C(Icc (0 : ℝ) T, V) := by
  haveI : Countable (EigenIndex J) := eigenIndex_countable J hc
  let trace := SpectralHeatNative.shiftedTracePath hT (generatorParameters J hc hd hnorm) F
  exact ⟨fun t => (formEigenbasis J hc hd hinj).repr.symm (trace t),
    (formEigenbasis J hc hd hinj).repr.symm.continuous.comp trace.continuous⟩

theorem inclusion_formResponsePath [SeparableSpace H]
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hinj : Function.Injective J) (hnorm : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (F : ForcingSpace (EigenIndex J) T) (t : Icc (0 : ℝ) T) :
    J (formResponsePath J hc hd hinj hnorm hT F t) =
      (eigenbasis J hc hd).repr.symm
        (SpectralHeatNative.responseState (generatorParameters J hc hd hnorm) F t) := by
  haveI : Countable (EigenIndex J) := eigenIndex_countable J hc
  apply (eigenbasis J hc hd).repr.injective
  apply lp.ext
  funext i
  change (eigenbasis J hc hd).repr
      (J ((formEigenbasis J hc hd hinj).repr.symm
        (SpectralHeatNative.shiftedTracePath hT (generatorParameters J hc hd hnorm) F t))) i = _
  rw [repr_inclusion_decode, LinearIsometryEquiv.apply_symm_apply,
    SpectralHeatNative.shiftedTracePath_coeff, ← mul_assoc,
    sqrt_eigenparameter_mul_shifted, one_mul]

theorem norm_formResponsePath_le [SeparableSpace H]
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hinj : Function.Injective J) (hnorm : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (F : ForcingSpace (EigenIndex J) T) :
    ‖formResponsePath J hc hd hinj hnorm hT F‖ ≤ (Real.sqrt T + 1) * ‖F‖ := by
  haveI : Countable (EigenIndex J) := eigenIndex_countable J hc
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖(formEigenbasis J hc hd hinj).repr.symm
    (SpectralHeatNative.shiftedTracePath hT (generatorParameters J hc hd hnorm) F t)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousMap.norm_coe_le_norm _ _).trans
    (SpectralHeatNative.norm_shiftedTracePath_le hT (generatorParameters J hc hd hnorm) F)

end PoincareConjecture.HilbertResolventNative
