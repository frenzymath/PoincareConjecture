import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffine
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps

set_option autoImplicit false

open Set

namespace Geometry

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem LocallyPiecewiseAffineOn.exists_compact_affine_neighborhood
    {f : E → F} {U A : Set E} (hf : LocallyPiecewiseAffineOn f U)
    (hA : IsCompact A) (hAU : A ⊆ U) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧
      A ⊆ interior J.space ∧ J.space ⊆ U ∧ J.AffineOnFaces f := by
  classical
  choose L hL hxL hLU hfL using fun x : A => hf x (hAU x.property)
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun x : A => interior (L x).space)
    (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxL ⟨x, hx⟩⟩)
  obtain ⟨J, hJ, hJs, hfaces⟩ := SimplicialComplex.exists_finite_triangulation_iUnion
    (fun x : t => L x) (fun x => hL x)
  refine ⟨J, hJ, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, hat, hxa⟩ := mem_iUnion₂.mp (ht hx)
    apply interior_mono (s := (L a).space) ?_ hxa
    intro y hy
    rw [hJs]
    exact mem_iUnion.mpr ⟨⟨a, hat⟩, hy⟩
  · intro x hx
    rw [hJs] at hx
    obtain ⟨a, hxa⟩ := mem_iUnion.mp hx
    exact hLU a hxa
  · intro s hs
    obtain ⟨a, r, hr, hsr⟩ := hfaces s hs
    obtain ⟨b, hb⟩ := hfL a r hr
    exact ⟨b, hb.mono hsr⟩

theorem LocallyPiecewiseAffineOn.finitePiecewiseAffineOn
    {f : E → F} {U : Set E} (hf : LocallyPiecewiseAffineOn f U)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKU : K.space ⊆ U) :
    FinitePiecewiseAffineOn f K.space := by
  obtain ⟨J, hJ, hKJ, _, hfJ⟩ :=
    hf.exists_compact_affine_neighborhood (K.isCompact_space_of_finite hK) hKU
  exact (hfJ.finitePiecewiseAffineOn hJ).restrict K hK
    (fun x hx => interior_subset (hKJ hx))

theorem LocallyPiecewiseAffineOn.comp_finitePiecewiseAffineOn
    {f : F → E} {g : E → G} {S : Set F} {U : Set E}
    (hg : LocallyPiecewiseAffineOn g U) (hf : FinitePiecewiseAffineOn f S)
    (hfU : MapsTo f S U) : FinitePiecewiseAffineOn (g ∘ f) S := by
  have hA : IsCompact (f '' S) := hf.isCompact.image_of_continuousOn hf.continuousOn
  obtain ⟨J, hJ, hAJ, _, hgJ⟩ := hg.exists_compact_affine_neighborhood hA
    (by rintro _ ⟨x, hx, rfl⟩; exact hfU hx)
  exact (hgJ.finitePiecewiseAffineOn hJ).comp hf
    (fun x hx => interior_subset (hAJ (mem_image_of_mem f hx)))

end Geometry
