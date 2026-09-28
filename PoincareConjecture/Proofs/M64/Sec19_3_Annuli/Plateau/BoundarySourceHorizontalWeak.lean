import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceHorizontalGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem m64HorizontalSource_quasiMeasurePreserving {tau : ℝ ≃ₜ ℝ}
    (hi : ContDiff ℝ 1 tau.symm) (hmono : StrictMono tau)
    (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod) :
    Measure.QuasiMeasurePreserving (m64HorizontalSource tau) mu mu := by
  let T := m64HorizontalSource tau
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
      ((m64HorizontalSource_contDiff hi).differentiable (by simp)).differentiableOn hz
  apply hq.restrict
  intro p hp
  have hpre := m64HorizontalSource_preimage_interior hmono h0 hP
  exact (congrArg (fun U => p ∈ U) hpre).mpr hp

theorem m64HorizontalSource_memLp_two
    {E : Type*} [NormedAddCommGroup E] {f : LoopPlane → E}
    {tau : ℝ ≃ₜ ℝ} (ht : ContDiff ℝ 1 tau) (hi : ContDiff ℝ 1 tau.symm)
    (hpos : ∀ x, 0 < deriv tau x) (hmono : StrictMono tau)
    (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod) (hf : MemLp f 2 mu) :
    MemLp (f ∘ m64HorizontalSource tau) 2 mu := by
  let T := m64HorizontalSource tau
  have hmeas := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
    (m64HorizontalSource_quasiMeasurePreserving hi hmono h0 hP)
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  have hint := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hweighted := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume (s := S) isOpen_interior.measurableSet
    (fun p _ => (m64HorizontalSource_hasFDerivAt
      (ht.differentiable (by simp) (p 0))).hasFDerivWithinAt) T.injective.injOn
    (fun p => ‖f p‖ ^ 2)).mp
      (by rwa [m64HorizontalSource_image_interior hmono h0 hP])
  have hweighted' : Integrable (fun p => deriv tau (p 0) * ‖f (T p)‖ ^ 2) mu := by
    simpa only [m64HorizontalSourceDerivative_det, abs_of_pos (hpos _), smul_eq_mul,
      IntegrableOn, T]
      using hweighted
  have hcoeff : Continuous (fun p : LoopPlane => deriv tau.symm (tau (p 0))) := by
    exact (hi.continuous_deriv (by simp)).comp
      (tau.continuous.comp (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous)
  obtain ⟨C, hC⟩ := m64AnnulusDomain_isCompact.exists_bound_of_continuousOn
    hcoeff.continuousOn
  have hbound : ∀ᵐ p ∂mu, ‖deriv tau.symm (tau (p 0))‖ ≤ C := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact hC p (interior_subset hp)
  have hprod := hweighted'.bdd_mul hcoeff.aestronglyMeasurable hbound
  apply hprod.congr
  filter_upwards [] with p
  dsimp only [Function.comp_apply]
  rw [← mul_assoc, mul_comm (deriv tau.symm (tau (p 0))),
    m64HorizontalSource_inverse_deriv (ht.differentiable (by simp))
      (hi.differentiable (by simp)), one_mul]

theorem m64HorizontalSource_weakPartial {tau : ℝ ≃ₜ ℝ}
    (ht : ContDiff ℝ ∞ tau) (hi : ContDiff ℝ ∞ tau.symm)
    (hpos : ∀ x, 0 < deriv tau x) (hmono : StrictMono tau)
    (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod)
    {u V : LoopPlane → ℝ} {i : Fin 2} (hw : HasWeakPartialDeriv i V u S) :
    HasWeakPartialDeriv i
      (fun p => (if i = 0 then deriv tau (p 0) else 1) * V (m64HorizontalSource tau p))
      (u ∘ m64HorizontalSource tau) S := by
  let T := m64HorizontalSource tau
  intro phi hp hc hs
  have hpre : T '' S = S := m64HorizontalSource_image_interior hmono h0 hP
  have hpsi : ContDiff ℝ ∞ (phi ∘ T.symm) := hp.comp (m64HorizontalSource_contDiff hi)
  have hps : tsupport (phi ∘ T.symm) ⊆ S := by
    rw [tsupport_comp_eq_preimage]
    intro p h
    have hh : T.symm p ∈ S := hs h
    have himg : T (T.symm p) ∈ T '' S := mem_image_of_mem T hh
    simpa only [hpre, Homeomorph.apply_symm_apply] using himg
  have hz {v psi : LoopPlane → ℝ} {j : Fin 2}
      (h : HasWeakPartialDeriv j v u S) (hr : ContDiff ℝ ∞ psi)
      (hc' : HasCompactSupport psi) (hs' : tsupport psi ⊆ S) :
      (∫ p in S, psi p * v p) +
        (∫ p in S, fderiv ℝ psi p (EuclideanSpace.single j 1) * u p) = 0 := by
    have hh := h psi hr hc' hs'
    simp only [mul_comm] at hh ⊢
    linarith
  fin_cases i
  · have h := m64HorizontalSource_horizontal_green ht hi hpos hmono h0 hP u V
      (hp.of_le (by simp))
    rw [show (∫ p in S, (phi ∘ T.symm) p • V p) +
        (∫ p in S, fderiv ℝ (phi ∘ T.symm) p e0 • u p) = 0 from
      hz hw hpsi (hc.comp_homeomorph T.symm) hps] at h
    change (∫ p in S, u (T p) * fderiv ℝ phi p e0) =
      -(∫ p in S, (deriv tau (p 0) * V (T p)) * phi p)
    simp only [smul_eq_mul, mul_comm] at h ⊢
    linarith
  · let psi := m64HorizontalSourceRadialTest tau phi
    have hr : ContDiff ℝ ∞ psi := m64HorizontalSourceRadialTest_contDiff hi hp le_rfl
    have hc' : HasCompactSupport psi := (hc.comp_homeomorph T.symm).mul_left
    have hs' : tsupport psi ⊆ S := tsupport_mul_subset_right.trans hps
    have h := m64HorizontalSource_radial_green ht hi hpos hmono h0 hP u V
      (hp.of_le (by simp))
    rw [show (∫ p in S, psi p • V p) + (∫ p in S, fderiv ℝ psi p e1 • u p) = 0 from
      hz hw hr hc' hs'] at h
    change (∫ p in S, u (T p) * fderiv ℝ phi p e1) =
      -(∫ p in S, (1 * V (T p)) * phi p)
    simp only [one_mul, smul_eq_mul, mul_comm] at h ⊢
    linarith

end PoincareConjecture
