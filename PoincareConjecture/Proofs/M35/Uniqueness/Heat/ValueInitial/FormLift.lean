import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.SpectralLift
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormDualCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open HilbertResolventNative SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def initialValuePath (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hn : ‖J‖ ≤ 1) (u₀ : H) (t : ℝ) : H :=
  (eigenbasis J hc hd).repr.symm
    (initialValueState (generatorParameters J hc hd hn) ((eigenbasis J hc hd).repr u₀) t)

def initialFormPath (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    (u₀ : H) (t : ℝ) : V :=
  (formEigenbasis J hc hd hi).repr.symm
    (initialFormState (generatorParameters J hc hd hn) ((eigenbasis J hc hd).repr u₀) t)

theorem initialValuePath_zero (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hn : ‖J‖ ≤ 1) (u₀ : H) :
    initialValuePath J hc hd hn u₀ 0 = u₀ := by
  rw [initialValuePath, initialValueState_zero, LinearIsometryEquiv.symm_apply_apply]

theorem initialValuePath_continuous (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hn : ‖J‖ ≤ 1) (u₀ : H) :
    Continuous (initialValuePath J hc hd hn u₀) :=
  (eigenbasis J hc hd).repr.symm.continuous.comp (initialValueState_continuous _ _)

theorem initialValuePath_norm_le (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hn : ‖J‖ ≤ 1) (u₀ : H) (t : ℝ) :
    ‖initialValuePath J hc hd hn u₀ t‖ ≤ ‖u₀‖ := by
  rw [initialValuePath, LinearIsometryEquiv.norm_map]
  exact (initialValueState_norm_le _ _ _).trans_eq (LinearIsometryEquiv.norm_map _ _)

variable [SeparableSpace H]

theorem initialFormPath_memLp (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (u₀ : H) :
    MemLp (initialFormPath J hc hd hi hn u₀) 2 (timeMeasure T) := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  let Q : State (EigenIndex J) →L[ℝ] V :=
    (formEigenbasis J hc hd hi).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact Q.comp_memLp' (initialFormState_memLp _ _ hT)

theorem initialFormPath_graph (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (u₀ : H) :
    ∀ᵐ t ∂timeMeasure T,
      J (initialFormPath J hc hd hi hn u₀ t) = initialValuePath J hc hd hn u₀ t := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  filter_upwards [initialFormState_coeff (generatorParameters J hc hd hn)
    ((eigenbasis J hc hd).repr u₀) hT, ae_restrict_mem measurableSet_Ioc] with t ht htime
  apply (eigenbasis J hc hd).repr.injective
  apply lp.ext
  funext i
  rw [initialFormPath, repr_inclusion_decode, initialValuePath,
    LinearIsometryEquiv.apply_symm_apply, ht, initialValueState_coeff _ _ htime.1.le]
  rw [← mul_assoc, ← mul_assoc, sqrt_eigenparameter_mul_shifted, one_mul]

theorem initialValuePath_memLp (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (u₀ : H) :
    MemLp (initialValuePath J hc hd hn u₀) 2 (timeMeasure T) :=
  (memLp_congr_ae (initialFormPath_graph J hc hd hi hn hT u₀)).mp
    (J.comp_memLp' (initialFormPath_memLp J hc hd hi hn hT u₀))

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
