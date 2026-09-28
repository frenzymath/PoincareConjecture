import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormWeakHeat
import PoincareConjecture.Proofs.M03.Existence.SpectralScaleNative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open HilbertResolventNative SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem form_adjoint_spectral_decode (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) (u : H) :
    (formEigenbasis J hc hd hi).repr (J.adjoint u) =
      scaleDecode (generatorParameters J hc hd hn) 1 ((eigenbasis J hc hd).repr u) := by
  apply lp.ext
  funext i
  rw [form_repr_adjoint, scaleDecode_apply, scaleWeight, pow_one]
  congr 1
  rw [inv_eq_one_div]
  exact (eq_div_iff (by positivity)).mpr (sqrt_eigenparameter_mul_shifted J hc hd hn i)

variable [SeparableSpace H]

theorem formWeakHeat_value_forcing_trace (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : Lp H 2 (timeMeasure T)) :
    letI : Countable (EigenIndex J) := eigenIndex_countable J hc
    let G := (eigenbasis J hc hd).repr.toContinuousLinearEquiv.toContinuousLinearMap.compLpL
      2 (timeMeasure T) F
    ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc 0 T,
      (formEigenbasis J hc hd hi).repr
        (formWeakHeatOperator J hc hd hi hn hT (J.adjoint.compLpL 2 (timeMeasure T) F) t) =
          shiftedTracePath hT (generatorParameters J hc hd hn) G ⟨t, ht⟩ := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  let BF := (formEigenbasis J hc hd hi).repr
  let BH := (eigenbasis J hc hd).repr
  let CF := BF.toContinuousLinearEquiv.toContinuousLinearMap
  let CH := BH.toContinuousLinearEquiv.toContinuousLinearMap
  let lambda := generatorParameters J hc hd hn
  let A := J.adjoint.compLpL 2 (timeMeasure T) F
  let E := CF.compLpL 2 (timeMeasure T) A
  let G := CH.compLpL 2 (timeMeasure T) F
  have hEG : E =ᵐ[timeMeasure T] fun t => scaleDecode lambda 1 (G t) := by
    filter_upwards [CF.coeFn_compLpL A, J.adjoint.coeFn_compLpL F, CH.coeFn_compLpL F]
      with t ht hA hG
    rw [ht, hA, hG]
    exact form_adjoint_spectral_decode J hc hd hi hn (F t)
  have hresponse (t : ℝ) (ht : t ∈ Icc 0 T) :
      responseState lambda E t = scaleDecode lambda 1 (responseState lambda G t) :=
    (responseState_eq_of_ae_eq (Lp.memLp E) ((scaleDecode lambda 1).comp_memLp' (Lp.memLp G))
      lambda hEG ht).trans (scaleDecode_responseState lambda 1 (Lp.memLp G) ht).symm
  filter_upwards [formDualResponseOperator_coe J hc hd hi hn hT E,
    shiftedHighOperator_coeff hT lambda E] with t hv hs
  intro ht
  change BF (formDualResponseOperator J hc hd hi hn hT E t) =
    shiftedTracePath hT lambda G ⟨t, ht⟩
  rw [hv, LinearIsometryEquiv.apply_symm_apply]
  apply lp.ext
  funext i
  rw [hs, hresponse t ht, scaleDecode_apply, scaleWeight, pow_one, shiftedTracePath_coeff]
  have hq : 0 ≤ 1 + (lambda i : ℝ) := by positivity
  have hsqrt : Real.sqrt (1 + (lambda i : ℝ)) ≠ 0 := by positivity
  have hscalar : (1 + (lambda i : ℝ)) * (Real.sqrt (1 + (lambda i : ℝ)))⁻¹ =
      Real.sqrt (1 + (lambda i : ℝ)) := by
    rw [← div_eq_mul_inv]
    exact (div_eq_iff hsqrt).mpr (Real.mul_self_sqrt hq).symm
  calc
    _ = ((1 + (lambda i : ℝ)) * (Real.sqrt (1 + (lambda i : ℝ)))⁻¹) *
        responseState lambda G t i := by ring
    _ = Real.sqrt (1 + (lambda i : ℝ)) * responseState lambda G t i := by rw [hscalar]

end PoincareConjecture.M35.Uniqueness.Heat
