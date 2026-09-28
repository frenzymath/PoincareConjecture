import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ScalarVolterraZero









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory

namespace PoincareConjecture.M35.Uniqueness.Heat

open HilbertResolventNative SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem form_homogeneous_integral_zero
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) {T : ℝ} (hT : 0 < T)
    (v : ℝ → V) (hv : MemLp v 2 (timeMeasure T)) (U : ℝ → H)
    (hU : ContinuousOn U (Icc 0 T))
    (hgraph : ∀ᵐ t ∂timeMeasure T, J (v t) = U t)
    (heq : ∀ t ∈ Icc 0 T, J.adjoint (U t) =
      ∫ s in (0 : ℝ)..t, -v s + J.adjoint (J (v s))) :
    (∀ t ∈ Icc 0 T, U t = 0) ∧ ∀ᵐ t ∂timeMeasure T, v t = 0 := by
  let B := (formEigenbasis J hc hd hi).repr.toContinuousLinearEquiv.toContinuousLinearMap
  let Q : ℝ → V := fun t => -v t + J.adjoint (J (v t))
  have hQ : MemLp Q 2 (timeMeasure T) :=
    hv.neg.add (J.adjoint.comp_memLp' (J.comp_memLp' hv))
  have hqi : IntervalIntegrable Q volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
      (hQ.integrable (by norm_num))
  have hmode (i : EigenIndex J) :
      ∀ t ∈ Icc 0 T, (formEigenbasis J hc hd hi).repr (J.adjoint (U t)) i = 0 := by
    let C := (lp.evalCLM ℝ (fun _ : EigenIndex J => ℝ) 2 i).comp B
    let q : ℝ → ℝ := fun t => C (J.adjoint (U t))
    have hqc : ContinuousOn q (Icc 0 T) :=
      C.continuous.comp_continuousOn (J.adjoint.continuous.comp_continuousOn hU)
    have hμ : i.1.val ≠ 0 := (eigenparameter_pos J hc hd i).ne'
    apply scalar_homogeneous_integral_zero (c := 1 - i.1.val⁻¹) hT q hqc
    intro t ht
    have hqit : IntervalIntegrable Q volume 0 t := hqi.mono_set (by
      simpa only [uIcc_of_le hT.le, uIcc_of_le ht.1] using Icc_subset_Icc le_rfl ht.2)
    have hCi := C.intervalIntegral_comp_comm hqit
    change C (J.adjoint (U t)) = _
    rw [heq t ht, ← hCi]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc le_rfl ht.2) hgraph] with s hs
    change C (-v s + J.adjoint (J (v s))) = (1 - i.1.val⁻¹) * C (J.adjoint (U s))
    rw [← hs, map_add, map_neg]
    change -(formEigenbasis J hc hd hi).repr (v s) i +
      (formEigenbasis J hc hd hi).repr (J.adjoint (J (v s))) i =
        (1 - i.1.val⁻¹) * (formEigenbasis J hc hd hi).repr (J.adjoint (J (v s))) i
    rw [form_repr_adjoint_inclusion J hc hd hi]
    field_simp [hμ]
    ring
  have hzero (t : ℝ) (ht : t ∈ Icc 0 T) : U t = 0 := by
    apply (eigenbasis J hc hd).repr.injective
    apply lp.ext
    funext i
    have he := hmode i t ht
    rw [form_repr_adjoint J hc hd hi] at he
    have hs : Real.sqrt i.1.val ≠ 0 := (Real.sqrt_pos.mpr (eigenparameter_pos J hc hd i)).ne'
    simpa only [map_zero, lp.coeFn_zero, Pi.zero_apply] using (mul_eq_zero.mp he).resolve_left hs
  refine ⟨hzero, ?_⟩
  filter_upwards [hgraph, ae_restrict_mem measurableSet_Ioc] with t ht htime
  apply hi
  rw [map_zero, ht, hzero t (Ioc_subset_Icc_self htime)]

end PoincareConjecture.M35.Uniqueness.Heat
