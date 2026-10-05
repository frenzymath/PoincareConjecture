import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.GeometricPointedArcLevel

/-!
# Exact fixed-residual contact of a replaced pointed arc

A positive moved cap level avoids every set fixed pointwise by
the ambient homeomorphism. The collar chart's original roof
test therefore gives exactly the new arc's outer endpoints as
its residual contacts. See Alexander 1924, pp. 7--8 and
M76 derivations 213, 227--228.
-/

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]

/-- The actual cap-and-collar arc meets a fixed residual exactly
in the collar images of the original roof-level endpoints.
Strictly positive level excludes contact with the moved cap.
See Alexander pp. 7--8 and M76 derivation 228. -/
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
