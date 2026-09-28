import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularDerivative
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

theorem m64Source_image_interior (T : LoopPlane ≃ₜ LoopPlane) (hpre : T ⁻¹' S = S) :
    T '' S = S := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (congrArg (fun U => q ∈ U) hpre).mpr hq
  · intro hp
    refine ⟨T.symm p, ?_, T.apply_symm_apply p⟩
    exact (congrArg (fun U => T.symm p ∈ U) hpre).mp (by simpa using hp)

theorem m64TriangularSource_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : LoopPlane ≃ₜ LoopPlane) (hT : Differentiable ℝ T)
    (hsecond : ∀ p, T p 1 = p 1) (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hpre : T ⁻¹' S = S) (f : LoopPlane → E) :
    (∫ p in S, (fderiv ℝ T p e0 0) • f (T p)) = ∫ p in S, f p := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume (s := S)
    isOpen_interior.measurableSet (fun p _ => (hT p).hasFDerivAt.hasFDerivWithinAt)
    T.injective.injOn f
  rw [m64Source_image_interior T hpre] at h
  simpa only [m64TriangularSource_det hT hsecond, abs_of_pos (hpos _)] using h.symm

theorem m64Source_quasiMeasurePreserving
    (T : LoopPlane ≃ₜ LoopPlane) (hi : Differentiable ℝ T.symm) (hpre : T ⁻¹' S = S) :
    Measure.QuasiMeasurePreserving T mu mu := by
  have hq : Measure.QuasiMeasurePreserving T volume volume := by
    refine ⟨T.continuous.measurable, Measure.AbsolutelyContinuous.mk ?_⟩
    intro U hU hz
    rw [Measure.map_apply T.measurable hU]
    have himage : T ⁻¹' U = T.symm '' U := by
      ext p
      constructor
      · intro hp
        exact ⟨T p, hp, T.symm_apply_apply p⟩
      · rintro ⟨q, hq, rfl⟩
        simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hq
    rw [himage]
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      hi.differentiableOn hz
  apply hq.restrict
  intro p hp
  exact (congrArg (fun U => p ∈ U) hpre).mpr hp

theorem m64TriangularSource_memLp_two
    {E : Type*} [NormedAddCommGroup E] {f : LoopPlane → E}
    (T : LoopPlane ≃ₜ LoopPlane) (hT : ContDiff ℝ 1 T) (hi : ContDiff ℝ 1 T.symm)
    (hsecond : ∀ p, T p 1 = p 1) (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hpre : T ⁻¹' S = S) (hf : MemLp f 2 mu) :
    MemLp (f ∘ T) 2 mu := by
  have hd := hT.differentiable (by simp)
  have hid := hi.differentiable (by simp)
  have hmeas := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
    (m64Source_quasiMeasurePreserving T hid hpre)
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  have hint := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hweighted := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume (s := S) isOpen_interior.measurableSet
    (fun p _ => (hd p).hasFDerivAt.hasFDerivWithinAt) T.injective.injOn
    (fun p => ‖f p‖ ^ 2)).mp (by rwa [m64Source_image_interior T hpre])
  have hweighted' : Integrable (fun p => fderiv ℝ T p e0 0 * ‖f (T p)‖ ^ 2) mu := by
    simpa only [m64TriangularSource_det hd hsecond, abs_of_pos (hpos _), smul_eq_mul,
      IntegrableOn] using hweighted
  have hcoeff : Continuous (fun p : LoopPlane => fderiv ℝ T.symm (T p) e0 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous.comp
      (((hi.continuous_fderiv (by simp)).clm_apply continuous_const).comp T.continuous)
  obtain ⟨C, hC⟩ := m64AnnulusDomain_isCompact.exists_bound_of_continuousOn
    hcoeff.continuousOn
  have hbound : ∀ᵐ p ∂mu, ‖fderiv ℝ T.symm (T p) e0 0‖ ≤ C := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact hC p (interior_subset hp)
  have hprod := hweighted'.bdd_mul hcoeff.aestronglyMeasurable hbound
  apply hprod.congr
  filter_upwards [] with p
  dsimp only [Function.comp_apply]
  rw [← mul_assoc, (m64TriangularSource_inverse_derivative T hd hid hsecond p).1, one_mul]

end PoincareConjecture
