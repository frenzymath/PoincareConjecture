import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartDerivative
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]



theorem exists_normalized_chart_correction (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hzero : (0 : E) ∈ e.source) :
    ∃ A : E ≃L[ℝ] E, HasFDerivAt e (A : E →L[ℝ] E) 0 ∧
      ∃ h : E → E, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧ fderiv ℝ h 0 = 0 ∧
        ∀ᶠ w : E in 𝓝 0, e (A.symm w) = e 0 + w + h w := by
  obtain ⟨A, hA⟩ := exists_smoothChart_derivative e he hi hzero
  let U : Set E := A.symm ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage A.symm.continuous
  have h0U : (0 : E) ∈ U := by simpa only [U, mem_preimage, map_zero] using hzero
  let f : E → E := fun w => e (A.symm w) - e 0 - w
  have hf : ContDiffOn ℝ ∞ f U :=
    ((he.comp A.symm.contDiff.contDiffOn (fun _ hw => hw)).sub contDiffOn_const).sub
      contDiff_id.contDiffOn
  have hf0 : f 0 = 0 := by simp only [f, map_zero, sub_self, sub_zero]
  have hA0 : HasFDerivAt e (A : E →L[ℝ] E) (A.symm (0 : E)) := by
    simpa only [map_zero] using hA
  have hcomp : HasFDerivAt (fun w => e (A.symm w)) (ContinuousLinearMap.id ℝ E) 0 := by
    have h := hA0.comp (0 : E) A.symm.hasFDerivAt
    have hid : (A : E →L[ℝ] E).comp (A.symm : E →L[ℝ] E) =
        ContinuousLinearMap.id ℝ E := by
      ext w
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        A.apply_symm_apply, ContinuousLinearMap.id_apply]
    rw [hid] at h
    exact h
  have hfd : HasFDerivAt f (0 : E →L[ℝ] E) 0 := by
    simpa only [sub_self, id_eq] using
      (hcomp.sub_const (e 0)).fun_sub (hasFDerivAt_id (0 : E))
  obtain ⟨h, hh, _, _, hnear⟩ := exists_compactField_extension
    (isCompact_singleton (x := (0 : E))) hU (singleton_subset_iff.mpr h0U) f hf
  rw [nhdsSet_singleton] at hnear
  have hnear' : h =ᶠ[𝓝 (0 : E)] f := hnear
  refine ⟨A, hA, h, hh, hnear'.eq_of_nhds.trans hf0,
    (hfd.congr_of_eventuallyEq hnear').fderiv, ?_⟩
  filter_upwards [hnear'] with w hw
  rw [hw]
  dsimp [f]
  abel

end PoincareConjecture.M25.Topology3D
