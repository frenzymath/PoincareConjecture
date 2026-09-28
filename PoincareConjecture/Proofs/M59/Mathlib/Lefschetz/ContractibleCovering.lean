import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.CoveringDeformation












set_option autoImplicit false

noncomputable section

open scoped unitInterval

universe u v

namespace PoincareConjecture.Proofs.M59

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
  (p : C(E, X)) (hp : IsCoveringMap p) (H : C(I × X, X))
  (hzero : ∀ x, H (0, x) = x) (x₀ : X) (hone : ∀ x, H (1, x) = x₀)



def coveringFiberRetraction : C(E, p ⁻¹' {x₀}) :=
  coveringDeformationRetraction p hp H hzero {x₀} hone



def coveringReverseDeformation : C(I × (X × p ⁻¹' {x₀}), E) := by
  refine hp.liftHomotopy
    ⟨fun q => H (unitInterval.symm q.1, q.2.1),
      H.continuous.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        (continuous_fst.comp continuous_snd))⟩
    ⟨fun q => q.2.val, continuous_subtype_val.comp continuous_snd⟩ ?_
  intro q
  change H (unitInterval.symm 0, q.1) = p q.2.val
  rw [unitInterval.symm_zero, hone]
  exact q.2.property.symm



theorem coveringReverseDeformation_projection (t : I) (q : X × p ⁻¹' {x₀}) :
    p (coveringReverseDeformation p hp H x₀ hone (t, q)) =
      H (unitInterval.symm t, q.1) :=
  congrFun (hp.liftHomotopy_lifts _ _ _) (t, q)



theorem coveringReverseDeformation_zero (q : X × p ⁻¹' {x₀}) :
    coveringReverseDeformation p hp H x₀ hone (0, q) = q.2.val :=
  hp.liftHomotopy_zero _ _ _ q



def coveringFiberSection : C(X × p ⁻¹' {x₀}, E) :=
  ⟨fun q => coveringReverseDeformation p hp H x₀ hone (1, q),
    (coveringReverseDeformation p hp H x₀ hone).continuous.comp
      (continuous_const.prodMk continuous_id)⟩

include hzero in


theorem coveringFiberSection_projection (q : X × p ⁻¹' {x₀}) :
    p (coveringFiberSection p hp H x₀ hone q) = q.1 := by
  change p (coveringReverseDeformation p hp H x₀ hone (1, q)) = _
  rw [coveringReverseDeformation_projection, unitInterval.symm_one, hzero]



theorem coveringFiberRetraction_section (q : X × p ⁻¹' {x₀}) :
    coveringFiberRetraction p hp H hzero x₀ hone
      (coveringFiberSection p hp H x₀ hone q) = q.2 := by
  apply Subtype.ext
  have h := hp.eq_of_comp_eq
    ((coveringLiftedDeformation p hp H hzero).continuous.comp
      (continuous_id.prodMk continuous_const))
    ((coveringReverseDeformation p hp H x₀ hone).continuous.comp
      (unitInterval.continuous_symm.prodMk continuous_const))
    (show (fun t => p (coveringLiftedDeformation p hp H hzero
        (t, coveringFiberSection p hp H x₀ hone q))) =
      (fun t => p (coveringReverseDeformation p hp H x₀ hone
        (unitInterval.symm t, q))) from by
      funext t
      rw [coveringLiftedDeformation_projection,
        coveringFiberSection_projection p hp H hzero x₀ hone q,
        coveringReverseDeformation_projection, unitInterval.symm_symm])
    0 (by
      dsimp only [Function.comp_apply, id_eq]
      rw [coveringLiftedDeformation_zero, unitInterval.symm_zero]
      rfl)
  have h₁ := congrFun h 1
  dsimp only [Function.comp_apply, id_eq] at h₁
  rw [unitInterval.symm_one, coveringReverseDeformation_zero] at h₁
  exact h₁




theorem coveringFiberRetraction_injective_on_fiber {e e' : E}
    (he : p e = p e')
    (hr : coveringFiberRetraction p hp H hzero x₀ hone e =
      coveringFiberRetraction p hp H hzero x₀ hone e') : e = e' := by
  have h := hp.eq_of_comp_eq
    ((coveringLiftedDeformation p hp H hzero).continuous.comp
      (continuous_id.prodMk continuous_const))
    ((coveringLiftedDeformation p hp H hzero).continuous.comp
      (continuous_id.prodMk continuous_const))
    (show (fun t => p (coveringLiftedDeformation p hp H hzero (t, e))) =
      (fun t => p (coveringLiftedDeformation p hp H hzero (t, e'))) from by
      funext t
      rw [coveringLiftedDeformation_projection, coveringLiftedDeformation_projection, he])
    1 (congrArg Subtype.val hr)
  simpa only [Function.comp_apply, id_eq, coveringLiftedDeformation_zero] using congrFun h 0



def contractibleCoveringHomeomorph : E ≃ₜ X × p ⁻¹' {x₀} where
  toFun e := (p e, coveringFiberRetraction p hp H hzero x₀ hone e)
  invFun := coveringFiberSection p hp H x₀ hone
  left_inv _e := coveringFiberRetraction_injective_on_fiber p hp H hzero x₀ hone
    (coveringFiberSection_projection p hp H hzero x₀ hone _)
    (coveringFiberRetraction_section p hp H hzero x₀ hone _)
  right_inv q := Prod.ext (coveringFiberSection_projection p hp H hzero x₀ hone q)
    (coveringFiberRetraction_section p hp H hzero x₀ hone q)
  continuous_toFun := p.continuous.prodMk
    (coveringFiberRetraction p hp H hzero x₀ hone).continuous
  continuous_invFun := (coveringFiberSection p hp H x₀ hone).continuous

end PoincareConjecture.Proofs.M59
