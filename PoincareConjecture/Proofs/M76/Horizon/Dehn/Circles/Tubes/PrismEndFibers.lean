import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedPrismPreimages

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn
local notation "P2" => (ℝ × ℝ)

theorem signed_prism_joint_fiber_iff
    {E : Type*} [TopologicalSpace E] {B C J : Set E}
    {α β γ δ : ℝ} (u : Icc α β) (v : Icc γ δ)
    (left : ↥(signedTubeDiamond ×ˢ Icc α β) ≃ₜ B)
    (right : ↥(signedTubeDiamond ×ˢ Icc γ δ) ≃ₜ C)
    (G : signedTubeDiamond ≃ₜ J) (closing : signedTubeDiamond ≃ₜ signedTubeDiamond)
    (hcontact : B ∩ C = J)
    (hl : ∀ x : signedTubeDiamond,
      (left ⟨(x, u), x.property, u.property⟩ : E) = G (closing x))
    (hr : ∀ x : signedTubeDiamond,
      (right ⟨(x, v), x.property, v.property⟩ : E) = G x)
    (x : ↥(signedTubeDiamond ×ˢ Icc α β)) (y : ↥(signedTubeDiamond ×ˢ Icc γ δ)) :
    (left x : E) = right y ↔
      (x : P2 × ℝ).2 = u ∧ (y : P2 × ℝ).2 = v ∧
      (closing ⟨(x : P2 × ℝ).1, x.property.1⟩ : P2) = (y : P2 × ℝ).1 := by
  have hlJ : (left x : E) ∈ J ↔ (x : P2 × ℝ).2 = u :=
    signed_prism_end_preimage u.property left (closing.trans G) hl x
  have hrJ : (right y : E) ∈ J ↔ (y : P2 × ℝ).2 = v :=
    signed_prism_end_preimage v.property right G hr y
  have hxform (hx : (x : P2 × ℝ).2 = u) : x =
      ⟨((x : P2 × ℝ).1, u),
        x.property.1, u.property⟩ := Subtype.ext (Prod.ext rfl hx)
  have hyform (hy : (y : P2 × ℝ).2 = v) : y =
      ⟨((y : P2 × ℝ).1, v),
        y.property.1, v.property⟩ := Subtype.ext (Prod.ext rfl hy)
  constructor
  · intro hxy
    have hx : (x : P2 × ℝ).2 = u := hlJ.mp
      (hcontact ▸ ⟨(left x).property, hxy.symm ▸ (right y).property⟩)
    have hy : (y : P2 × ℝ).2 = v := hrJ.mp
      (hcontact ▸ ⟨hxy ▸ (left x).property, (right y).property⟩)
    refine ⟨hx, hy, ?_⟩
    have hleft := hl ⟨(x : P2 × ℝ).1, x.property.1⟩
    have hright := hr ⟨(y : P2 × ℝ).1, y.property.1⟩
    rw [← hxform hx] at hleft
    rw [← hyform hy] at hright
    exact congrArg Subtype.val (G.injective (Subtype.ext
      (hleft.symm.trans (hxy.trans hright))))
  · rintro ⟨hx, hy, hcoord⟩
    have hleft := hl ⟨(x : P2 × ℝ).1, x.property.1⟩
    have hright := hr ⟨(y : P2 × ℝ).1, y.property.1⟩
    rw [← hxform hx] at hleft
    rw [← hyform hy] at hright
    exact hleft.trans ((congrArg (fun p : signedTubeDiamond ↦ (G p : E))
      (Subtype.ext hcoord)).trans hright.symm)

end PoincareConjecture.M76.Dehn
