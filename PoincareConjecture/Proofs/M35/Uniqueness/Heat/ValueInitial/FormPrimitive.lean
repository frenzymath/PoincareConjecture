import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.FormLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open HilbertResolventNative SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem initialValuePath_integral (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (u₀ : H) {t : ℝ} (ht : t ∈ Icc 0 T) :
    J.adjoint (initialValuePath J hc hd hn u₀ t) = J.adjoint u₀ +
      ∫ s in (0 : ℝ)..t, -initialFormPath J hc hd hi hn u₀ s +
        J.adjoint (initialValuePath J hc hd hn u₀ s) := by
  let : Countable (EigenIndex J) := eigenIndex_countable J hc
  let BV := (formEigenbasis J hc hd hi).repr
  let BH := (eigenbasis J hc hd).repr
  let lambda := generatorParameters J hc hd hn
  let D : ℝ → V := fun s => -initialFormPath J hc hd hi hn u₀ s +
    J.adjoint (initialValuePath J hc hd hn u₀ s)
  have hDm : MemLp D 2 (timeMeasure T) :=
    (initialFormPath_memLp J hc hd hi hn hT u₀).neg.add
      (J.adjoint.comp_memLp' (initialValuePath_memLp J hc hd hi hn hT u₀))
  have hDi : IntervalIntegrable D volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
      ((show IntegrableOn D (Ioc 0 T) volume from
        hDm.integrable (by norm_num)).mono_set (Ioc_subset_Ioc le_rfl ht.2))
  apply BV.injective
  apply lp.ext
  funext i
  let C : V →L[ℝ] ℝ := (lp.evalCLM ℝ (fun _ : EigenIndex J => ℝ) 2 i).comp
    BV.toContinuousLinearEquiv.toContinuousLinearMap
  have hweight : Real.sqrt (1 + (lambda i : ℝ)) =
      Real.sqrt i.1.val * (1 + (lambda i : ℝ)) := by
    have hs := sqrt_eigenparameter_mul_shifted J hc hd hn i
    calc
      _ = (Real.sqrt i.1.val * Real.sqrt (1 + (lambda i : ℝ))) *
          Real.sqrt (1 + (lambda i : ℝ)) := by rw [hs, one_mul]
      _ = _ := by rw [mul_assoc, Real.mul_self_sqrt (by positivity)]
  have hDcoeff : ∀ᵐ s ∂timeMeasure T, C (D s) =
      -Real.sqrt i.1.val * (lambda i : ℝ) * Real.exp (-s * lambda i) * BH u₀ i := by
    filter_upwards [initialFormState_coeff lambda (BH u₀) hT,
      ae_restrict_mem measurableSet_Ioc] with s hs htime
    change BV (-initialFormPath J hc hd hi hn u₀ s +
      J.adjoint (initialValuePath J hc hd hn u₀ s)) i = _
    simp only [map_add, map_neg, lp.coeFn_add, lp.coeFn_neg, Pi.add_apply, Pi.neg_apply]
    rw [form_repr_adjoint, initialFormPath, initialValuePath,
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply,
      hs, initialValueState_coeff _ _ htime.1.le, hweight]
    ring
  have hcoord (s : ℝ) : HasDerivAt
      (fun a => Real.sqrt i.1.val * Real.exp (-a * lambda i) * BH u₀ i)
      (-Real.sqrt i.1.val * (lambda i : ℝ) * Real.exp (-s * lambda i) * BH u₀ i) s := by
    have h := (((hasDerivAt_id s).neg.mul_const (lambda i : ℝ)).exp.const_mul
      (Real.sqrt i.1.val)).mul_const (BH u₀ i)
    convert! h using 1
    simp only [Pi.neg_apply, id_eq]
    ring
  have hscalar : (∫ s in (0 : ℝ)..t,
      -Real.sqrt i.1.val * (lambda i : ℝ) * Real.exp (-s * lambda i) * BH u₀ i) =
      Real.sqrt i.1.val * Real.exp (-t * lambda i) * BH u₀ i -
        Real.sqrt i.1.val * BH u₀ i := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hcoord s)
      ((show Continuous (fun s : ℝ => -Real.sqrt i.1.val * (lambda i : ℝ) *
        Real.exp (-s * lambda i) * BH u₀ i) by fun_prop).intervalIntegrable 0 t)]
    simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
  change (formEigenbasis J hc hd hi).repr (J.adjoint
    (initialValuePath J hc hd hn u₀ t)) i =
      (formEigenbasis J hc hd hi).repr (J.adjoint u₀ + ∫ s in (0 : ℝ)..t, D s) i
  rw [map_add]
  simp only [lp.coeFn_add, Pi.add_apply, form_repr_adjoint]
  rw [initialValuePath, LinearIsometryEquiv.apply_symm_apply,
    initialValueState_coeff _ _ ht.1]
  change Real.sqrt i.1.val * (Real.exp (-t * lambda i) * BH u₀ i) =
    Real.sqrt i.1.val * BH u₀ i + C (∫ s in (0 : ℝ)..t, D s)
  rw [← C.intervalIntegral_comp_comm hDi]
  have he : (∫ s in (0 : ℝ)..t, C (D s)) = ∫ s in (0 : ℝ)..t,
      -Real.sqrt i.1.val * (lambda i : ℝ) * Real.exp (-s * lambda i) * BH u₀ i := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2) hDcoeff
  rw [he, hscalar]
  ring

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
