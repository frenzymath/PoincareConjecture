import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.CoveringDeformation

/-!
# A covering of an explicitly contracted base is a product

Lift the contraction to transport each point to the endpoint fiber. Lift
the reverse contraction to transport that fiber back to each base point.
Covering uniqueness proves these actual maps are inverse homeomorphisms.
No local path-connectedness assumption is inferred from contractibility.
Source: Hatcher, Proposition 1.30, printed p. 60, and Proposition 1.34,
p. 62; used in the cone case of Theorem 2.27, pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open scoped unitInterval

universe u v

namespace PoincareMT.Proofs.M59

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
  (p : C(E, X)) (hp : IsCoveringMap p) (H : C(I × X, X))
  (hzero : ∀ x, H (0, x) = x) (x₀ : X) (hone : ∀ x, H (1, x) = x₀)

/-- The actual endpoint-fiber projection obtained by lifting the
contraction. Source: Hatcher, Proposition 1.30, p. 60. -/
def coveringFiberRetraction : C(E, p ⁻¹' {x₀}) :=
  coveringDeformationRetraction p hp H hzero {x₀} hone

/-- Lifting the reverse contraction with the entire endpoint fiber as
parameter. Source: Hatcher, Proposition 1.30, p. 60. -/
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

/-- The reverse lift projects to the reversed original contraction.
Source: Hatcher, Proposition 1.30, p. 60. -/
theorem coveringReverseDeformation_projection (t : I) (q : X × p ⁻¹' {x₀}) :
    p (coveringReverseDeformation p hp H x₀ hone (t, q)) =
      H (unitInterval.symm t, q.1) :=
  congrFun (hp.liftHomotopy_lifts _ _ _) (t, q)

/-- The reverse lift starts at its retained endpoint-fiber point.
Source: Hatcher, Proposition 1.30, p. 60. -/
theorem coveringReverseDeformation_zero (q : X × p ⁻¹' {x₀}) :
    coveringReverseDeformation p hp H x₀ hone (0, q) = q.2.val :=
  hp.liftHomotopy_zero _ _ _ q

/-- The endpoint of the reverse lift gives the continuous family of
global covering sections. Source: Hatcher, Proposition 1.30, p. 60. -/
def coveringFiberSection : C(X × p ⁻¹' {x₀}, E) :=
  ⟨fun q => coveringReverseDeformation p hp H x₀ hone (1, q),
    (coveringReverseDeformation p hp H x₀ hone).continuous.comp
      (continuous_const.prodMk continuous_id)⟩

include hzero in
/-- The section really lies above its specified base point.
Source: Hatcher, Proposition 1.30, p. 60. -/
theorem coveringFiberSection_projection (q : X × p ⁻¹' {x₀}) :
    p (coveringFiberSection p hp H x₀ hone q) = q.1 := by
  change p (coveringReverseDeformation p hp H x₀ hone (1, q)) = _
  rw [coveringReverseDeformation_projection, unitInterval.symm_one, hzero]

/-- Reversing and then following the same lifted contraction returns
the retained fiber point. Source: Hatcher, Proposition 1.34, p. 62. -/
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

/-- The endpoint-fiber coordinate separates points in each original
fiber by uniqueness on the lifted contraction interval.
Source: Hatcher, Proposition 1.34, p. 62. -/
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

/-- The actual global trivialization of a covering of an explicitly
contracted base. Source: Hatcher, Propositions 1.30 and 1.34. -/
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

end PoincareMT.Proofs.M59
