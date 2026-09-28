import PoincareConjecture.Proofs.M76.Mathlib.GeometricPointedArcLevel











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]





theorem pointed_cap_collar_arc_inter_fixed_residual
    {d b R : Set E} (H : E ≃ₜ E) {A r upper : E → ℝ} {f : E → E} {a c : ℝ}
    (hdplane : d ⊆ {x | A x = 0}) (hc : 0 < c)
    (hfix : ∀ x ∈ R, H x = x)
    (hhigh : ∀ x ∈ b, a ≤ r x → c < upper x)
    (hcontact : ∀ x ∈ (b ∩ {x | r x ≤ a}) ∩ {x | c ≤ upper x},
      f x ∈ R ↔ upper x = c) :
    ((((H '' d) ∩ {x | A x = c}) ∪
      f '' ((b ∩ {x | r x ≤ a}) ∩ {x | c ≤ upper x})) ∩ R) =
      f '' (b ∩ {x | upper x = c}) := by
  obtain ⟨_, _, houter⟩ := rim_superlevel_truncated_sublevel_partition hhigh
  ext y
  constructor
  · rintro ⟨hy, hyR⟩
    rcases hy with ⟨⟨x, hx, rfl⟩, hAx⟩ | ⟨x, hx, rfl⟩
    · have hHx : H x = x := H.injective (hfix _ hyR)
      have hc0 : c = 0 := hAx.symm.trans ((congrArg A hHx).trans (hdplane hx))
      exact False.elim (hc.ne' hc0)
    · exact ⟨x, ⟨hx.1.1, (hcontact x hx).mp hyR⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Or.inr (mem_image_of_mem f (houter hx)), (hcontact x (houter hx)).mpr hx.2⟩

end Homeomorph
