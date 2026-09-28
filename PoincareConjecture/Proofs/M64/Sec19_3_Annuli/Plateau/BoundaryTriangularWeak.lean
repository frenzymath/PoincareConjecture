import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularGreen







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



theorem m64Source_comp_test_support
    (T : LoopPlane ≃ₜ LoopPlane) (hpre : T ⁻¹' S = S)
    {phi : LoopPlane → ℝ} (hs : tsupport phi ⊆ S) :
    tsupport (phi ∘ T.symm) ⊆ S := by
  rw [tsupport_comp_eq_preimage]
  intro p h
  have hh : T.symm p ∈ S := hs h
  have himg : T (T.symm p) ∈ T '' S := mem_image_of_mem T hh
  simpa only [m64Source_image_interior T hpre, Homeomorph.apply_symm_apply] using himg




theorem m64TriangularSource_weakPartials
    (T : LoopPlane ≃ₜ LoopPlane) (hT : ContDiff ℝ ∞ T) (hi : ContDiff ℝ ∞ T.symm)
    (hsecond : ∀ p, T p 1 = p 1) (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hpre : T ⁻¹' S = S) {u V0 V1 : LoopPlane → ℝ}
    (hu : MemLp u 2 mu) (hV0 : MemLp V0 2 mu) (hV1 : MemLp V1 2 mu)
    (hw0 : HasWeakPartialDeriv 0 V0 u S) (hw1 : HasWeakPartialDeriv 1 V1 u S) :
    HasWeakPartialDeriv 0 (fun p => fderiv ℝ T p e0 0 * V0 (T p)) (u ∘ T) S ∧
      HasWeakPartialDeriv 1 (fun p => fderiv ℝ T p e1 0 * V0 (T p) + V1 (T p))
        (u ∘ T) S := by
  have hz {v psi : LoopPlane → ℝ} {j : Fin 2}
      (h : HasWeakPartialDeriv j v u S) (hr : ContDiff ℝ ∞ psi)
      (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ S) :
      (∫ p in S, psi p • v p) +
        (∫ p in S, fderiv ℝ psi p (EuclideanSpace.single j 1) • u p) = 0 := by
    have hh := h psi hr hc hs
    simp only [smul_eq_mul, mul_comm] at hh ⊢
    linarith
  constructor
  · intro phi hp hc hs
    have h := m64TriangularSource_horizontal_green T hT hi hsecond hpos hpre u V0
      (hp.of_le (by simp))
    have hzero := hz hw0 (hp.comp hi) (hc.comp_homeomorph T.symm)
      (m64Source_comp_test_support T hpre hs)
    rw [hzero] at h
    change (∫ p in S, u (T p) * fderiv ℝ phi p e0) =
      -(∫ p in S, (fderiv ℝ T p e0 0 * V0 (T p)) * phi p)
    simp only [smul_eq_mul, mul_comm] at h ⊢
    linarith
  · intro phi hp hc hs
    have hsmooth := m64TriangularCofactorTest_contDiff T hi hp le_rfl
    have hsupp := m64Source_comp_test_support T hpre hs
    have hc' := hc.comp_homeomorph T.symm
    have hc0 : HasCompactSupport (m64TriangularCofactorTest0 T phi) := hc'.mul_left
    have hc1 : HasCompactSupport (m64TriangularCofactorTest1 T phi) := hc'.mul_left
    have hs0 : tsupport (m64TriangularCofactorTest0 T phi) ⊆ S :=
      tsupport_mul_subset_right.trans hsupp
    have hs1 : tsupport (m64TriangularCofactorTest1 T phi) ⊆ S :=
      tsupport_mul_subset_right.trans hsupp
    have h := m64TriangularSource_radial_green T hT hi hsecond hpos hpre hu hV0 hV1
      (hp.of_le (by simp))
    rw [hz hw0 hsmooth.1 hc0 hs0, hz hw1 hsmooth.2 hc1 hs1, add_zero] at h
    change (∫ p in S, u (T p) * fderiv ℝ phi p e1) =
      -(∫ p in S, (fderiv ℝ T p e1 0 * V0 (T p) + V1 (T p)) * phi p)
    simp only [smul_eq_mul, mul_comm] at h ⊢
    linarith



theorem m64TriangularSource_weighted_column_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : LoopPlane → E}
    (T : LoopPlane ≃ₜ LoopPlane) (hT : ContDiff ℝ 1 T) (hi : ContDiff ℝ 1 T.symm)
    (hsecond : ∀ p, T p 1 = p 1) (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hpre : T ⁻¹' S = S) (hV : MemLp V 2 mu) (i : Fin 2) :
    MemLp (fun p => (fderiv ℝ T p (EuclideanSpace.single i 1) 0) • V (T p)) 2 mu := by
  let a := fun p : LoopPlane => fderiv ℝ T p (EuclideanSpace.single i 1) 0
  have ha : Continuous a :=
    (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous.comp
      ((hT.continuous_fderiv (by simp)).clm_apply continuous_const)
  obtain ⟨C, hC⟩ := m64AnnulusDomain_isCompact.exists_bound_of_continuousOn ha.continuousOn
  have htop : MemLp a ∞ mu := memLp_top_of_bound ha.aestronglyMeasurable C (by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact hC p (interior_subset hp))
  exact (m64TriangularSource_memLp_two T hT hi hsecond hpos hpre hV).smul htop

end PoincareConjecture
