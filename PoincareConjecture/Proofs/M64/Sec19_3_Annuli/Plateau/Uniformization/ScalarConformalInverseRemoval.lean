import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarComplexOpen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M64Uniformization

theorem scalar_conformal_linear_inverse (L : ℂ ≃L[ℝ] ℂ)
    (hL : IsConformalMap (L : ℂ →L[ℝ] ℂ)) :
    IsConformalMap (L.symm : ℂ →L[ℝ] ℂ) := by
  obtain ⟨c, hc, hmetric⟩ := (isConformalMap_iff _).mp hL
  apply (isConformalMap_iff _).mpr
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro u v
  have h := hmetric (L.symm u) (L.symm v)
  simp only [ContinuousLinearEquiv.coe_coe, L.apply_symm_apply] at h
  rw [h]
  simp [hc.ne']

theorem scalar_localHomeomorph_regular_of_conformal_punctured
    (e : OpenPartialHomeomorph ℂ ℂ) {c : ℂ} (hc : c ∈ e.source)
    (hs : ContDiffAt ℝ ∞ e c)
    (hp : ∀ᶠ z in 𝓝[≠] c, ContDiffAt ℝ ∞ e z ∧ IsConformalMap (fderiv ℝ e z)) :
    ContDiffAt ℝ ∞ e.symm (e c) ∧ Function.Injective (fderiv ℝ e c) := by
  have hpinv : ∀ᶠ y in 𝓝[≠] e c,
      ContDiffAt ℝ ∞ e.symm y ∧ IsConformalMap (fderiv ℝ e.symm y) := by
    rw [eventually_nhdsWithin_iff] at hp ⊢
    filter_upwards [e.open_target.mem_nhds (e.map_source hc),
      (e.tendsto_symm hc).eventually hp] with y hy hys hyne
    have hsymmne : e.symm y ≠ c := by
      intro heq
      exact hyne ((e.right_inv hy).symm.trans (congrArg e heq))
    obtain ⟨hsy, hconf⟩ := hys hsymmne
    let A := fderiv ℝ e (e.symm y)
    have hinj : Function.Injective A := hconf.injective
    have hsurj : Function.Surjective A :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
    let L := (LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
    have hD : HasFDerivAt e (L : ℂ →L[ℝ] ℂ) (e.symm y) :=
      (hsy.differentiableAt (by simp)).hasFDerivAt
    refine ⟨e.contDiffAt_symm hy hD hsy, ?_⟩
    rw [(e.hasFDerivAt_symm hy hD).fderiv]
    exact scalar_conformal_linear_inverse L hconf
  have hi : ContDiffAt ℝ ∞ e.symm (e c) :=
    M60.contDiffAt_of_conformal_punctured (e.symm.continuousAt (e.map_source hc)) hpinv
  refine ⟨hi, ?_⟩
  have hcomp := ((hi.differentiableAt (by simp)).hasFDerivAt).comp c
    (hs.differentiableAt (by simp)).hasFDerivAt
  have hid : HasFDerivAt (e.symm ∘ e) (ContinuousLinearMap.id ℝ ℂ) c :=
    (hasFDerivAt_id c).congr_of_eventuallyEq (e.eventually_left_inverse hc)
  have heq := hcomp.unique hid
  intro u v huv
  have h := congrArg (fderiv ℝ e.symm (e c)) huv
  change ((fderiv ℝ e.symm (e c)).comp (fderiv ℝ e c)) u =
    ((fderiv ℝ e.symm (e c)).comp (fderiv ℝ e c)) v at h
  simpa only [heq, ContinuousLinearMap.id_apply] using h

theorem scalar_locally_injective_regular_of_conformal_punctured
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hcU : ContinuousOn f U)
    (hi : InjOn f U) (ho : ∀ z ∈ U, 𝓝 (f z) ≤ map f (𝓝 z))
    {c : ℂ} (hc : c ∈ U) (hs : ContDiffAt ℝ ∞ f c)
    (hp : ∀ᶠ z in 𝓝[≠] c, ContDiffAt ℝ ∞ f z ∧ IsConformalMap (fderiv ℝ f z)) :
    Function.Injective (fderiv ℝ f c) := by
  have hopen : IsOpenMap (U.domRestrict f) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro z
    have h := ho z z.property
    rw [← hU.nhdsWithin_eq z.property, ← map_nhds_subtype_val, map_map] at h
    exact h
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hi.toPartialEquiv f U) hcU hopen hU
  exact (scalar_localHomeomorph_regular_of_conformal_punctured e hc hs hp).2

end PoincareConjecture.M64Uniformization
