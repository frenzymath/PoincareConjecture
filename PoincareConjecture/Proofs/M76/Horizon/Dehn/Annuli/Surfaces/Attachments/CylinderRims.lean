import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.CylinderGluing



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Cyl" => Set.prod Q I

variable {E : Type*} [TopologicalSpace E]

theorem cylinder_rim_mem_iff {T B : Set E} (c : Cyl ≃ₜ T) (g : Q ≃ₜ B)
    (v : I) (hvalue : ∀ u : Q, (c ⟨(u, v), u.property, v.property⟩ : E) = g u)
    (x : Cyl) : (c x : E) ∈ B ↔ x.val.2 = v := by
  constructor
  · intro hx
    let u := g.symm ⟨c x, hx⟩
    have heq : c ⟨(u, v), u.property, v.property⟩ = c x :=
      Subtype.ext ((hvalue u).trans (congrArg Subtype.val (g.apply_symm_apply _)))
    exact (congrArg (fun y : Cyl ↦ y.val.2) (c.injective heq)).symm
  · intro hx
    have hxeq : x = ⟨(x.val.1, v), x.property.1, v.property⟩ :=
      Subtype.ext (Prod.ext rfl hx)
    rw [hxeq, hvalue ⟨x.val.1, x.property.1⟩]
    exact (g _).property

end PoincareConjecture.M76.Dehn.Annuli
