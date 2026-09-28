import PoincareConjecture.Proofs.M76.Mathlib.FinitePLRectanglePatches

set_option autoImplicit false

open Set RectangleCornerArcs

namespace Geometry

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem quadrant_graph_contact_of_height_surface
    {ψ : (ℝ × ℝ) → E} {F S g : Set E} (A : E →ₗ[ℝ] ℝ) {t z : ℝ}
    (hgraph : g = F ∩ (S ∪ {x | A x = 0}))
    (hfront : ψ '' (uIcc 0 t ×ˢ uIcc 0 z) ⊆ F)
    (hheight : ∀ x : ℝ × ℝ, A (ψ x) = x.1)
    (hsurface : ∀ x ∈ (uIcc 0 t ×ˢ uIcc 0 z), ψ x ∈ S ↔ x.2 = 0) :
    (ψ '' (uIcc 0 t ×ˢ uIcc 0 z)) ∩ g = ψ '' cornerArc 0 t 0 z := by
  apply Subset.antisymm
  · rintro p ⟨⟨x, hx, rfl⟩, hxg⟩
    rw [hgraph] at hxg
    refine ⟨x, ?_, rfl⟩
    rcases hxg.2 with hxS | hxA
    · exact Or.inr ⟨hx.1, (hsurface x hx).mp hxS⟩
    · exact Or.inl ⟨(hheight x).symm.trans hxA, hx.2⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxR := cornerArc_subset_rectangle 0 t 0 z hx
    refine ⟨⟨x, hxR, rfl⟩, ?_⟩
    rw [hgraph]
    refine ⟨hfront ⟨x, hxR, rfl⟩, ?_⟩
    rcases hx with hx | hx
    · exact Or.inr ((hheight x).trans hx.1)
    · exact Or.inl ((hsurface x hxR).mpr hx.2)

theorem quadrant_axis_incidence_of_height_surface
    {ψ : (ℝ × ℝ) → E} (hinj : Function.Injective ψ)
    {F S g M : Set E} (A : E →ₗ[ℝ] ℝ) {t z : ℝ}
    (ht : t ≠ 0) (hz : z ≠ 0)
    (hgraph : g = F ∩ (S ∪ {x | A x = 0}))
    (hfront : ψ '' (uIcc 0 t ×ˢ uIcc 0 z) ⊆ F)
    (hheight : ∀ x : ℝ × ℝ, A (ψ x) = x.1)
    (hsurface : ∀ x ∈ (uIcc 0 t ×ˢ uIcc 0 z), ψ x ∈ S ↔ x.2 = 0)
    (hM : M ⊆ S ∩ {x | A x = 0}) :
    (ψ '' ({0} ×ˢ uIcc 0 z) ⊆ F ∩ {x | A x = 0}) ∧
    (ψ '' (uIcc 0 t ×ˢ {0}) ⊆ F ∩ S) ∧
    ψ (0, z) ∈ ((ψ '' ({0} ×ˢ uIcc 0 z)) ∩ g) \ M ∧
    ψ (t, 0) ∈ ((ψ '' (uIcc 0 t ×ˢ {0})) ∩ g) \ M ∧
    (ψ '' cornerArc t 0 z 0) \ {ψ (0, z), ψ (t, 0)} ⊆ gᶜ := by
  have hvR : ({0} ×ˢ uIcc 0 z : Set (ℝ × ℝ)) ⊆ uIcc 0 t ×ˢ uIcc 0 z := by
    rintro x ⟨hx, hy⟩
    refine ⟨?_, hy⟩
    exact hx ▸ left_mem_uIcc
  have hhR : (uIcc 0 t ×ˢ {0} : Set (ℝ × ℝ)) ⊆ uIcc 0 t ×ˢ uIcc 0 z := by
    rintro x ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    exact hy ▸ left_mem_uIcc
  have hv : ψ '' ({0} ×ˢ uIcc 0 z) ⊆ F ∩ {x | A x = 0} := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hfront ⟨x, hvR hx, rfl⟩, (hheight x).trans hx.1⟩
  have hh : ψ '' (uIcc 0 t ×ˢ {0}) ⊆ F ∩ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hfront ⟨x, hhR hx, rfl⟩, (hsurface x (hhR hx)).mpr hx.2⟩
  have hvend : ψ (0, z) ∈ ψ '' ({0} ×ˢ uIcc 0 z) :=
    ⟨(0, z), ⟨rfl, right_mem_uIcc⟩, rfl⟩
  have hhend : ψ (t, 0) ∈ ψ '' (uIcc 0 t ×ˢ {0}) :=
    ⟨(t, 0), ⟨right_mem_uIcc, rfl⟩, rfl⟩
  have hvgraph : ψ (0, z) ∈ g := by
    rw [hgraph]
    exact ⟨(hv hvend).1, Or.inr (hv hvend).2⟩
  have hhgraph : ψ (t, 0) ∈ g := by
    rw [hgraph]
    exact ⟨(hh hhend).1, Or.inl (hh hhend).2⟩
  have hvmark : ψ (0, z) ∉ M := by
    intro hm
    exact hz ((hsurface (0, z) ⟨left_mem_uIcc, right_mem_uIcc⟩).mp (hM hm).1)
  have hhmark : ψ (t, 0) ∉ M := by
    intro hm
    exact ht ((hheight (t, 0)).symm.trans (hM hm).2)
  refine ⟨hv, hh, ⟨⟨hvend, hvgraph⟩, hvmark⟩, ⟨⟨hhend, hhgraph⟩, hhmark⟩, ?_⟩
  have houterR : cornerArc t 0 z 0 ⊆ uIcc 0 t ×ˢ uIcc 0 z := by
    simpa only [uIcc_comm t (0 : ℝ), uIcc_comm z (0 : ℝ)] using
      cornerArc_subset_rectangle t 0 z 0
  have hcontact := quadrant_graph_contact_of_height_surface A hgraph hfront hheight hsurface
  have hinter : (ψ '' cornerArc 0 t 0 z) ∩ (ψ '' cornerArc t 0 z 0) =
      {ψ (0, z), ψ (t, 0)} := by
    rw [← image_inter hinj, cornerArc_inter_opposite ht.symm hz.symm, image_pair]
  intro x hx hxg
  have hxd : x ∈ ψ '' (uIcc 0 t ×ˢ uIcc 0 z) := image_mono houterR hx.1
  exact hx.2 (hinter.subset ⟨hcontact.subset ⟨hxd, hxg⟩, hx.1⟩)

end Geometry
