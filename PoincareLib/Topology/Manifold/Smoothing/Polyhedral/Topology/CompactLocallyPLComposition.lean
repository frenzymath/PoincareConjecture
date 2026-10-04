import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.LocallyPiecewiseAffine
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.FinitePLUnionMaps

/-!
# Finite formulas on compact subsets of local PL domains

An actual finite union of local affine neighborhoods covers
any compact subset of an open PL domain. Refining that exact
union retains all original formulas and permits composition
with maps from closed finite polyhedra. See Hudson 1969,
pp. 12--19 and M76 derivation 270, closed polyhedral sources.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A compact subset of the actual domain of a locally PL
map lies in one finite affine neighborhood inside that same
domain. No triangulation of the compact subset is assumed.
See Hudson pp. 12--19 and M76 derivation 270. -/
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

/-- Local PL regularity restricts to every finite polyhedron
contained in its original open domain, including all source
boundary points. See Hudson pp. 15--19 and derivation 270. -/
theorem LocallyPiecewiseAffineOn.finitePiecewiseAffineOn
    {f : E → F} {U : Set E} (hf : LocallyPiecewiseAffineOn f U)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKU : K.space ⊆ U) :
    FinitePiecewiseAffineOn f K.space := by
  obtain ⟨J, hJ, hKJ, _, hfJ⟩ :=
    hf.exists_compact_affine_neighborhood (K.isCompact_space_of_finite hK) hKU
  exact (hfJ.finitePiecewiseAffineOn hJ).restrict K hK
    (fun x hx => interior_subset (hKJ hx))

/-- A locally PL map composes with a finite PL map on its
whole closed source carrier. Compactness supplies a finite
target neighborhood, allowing collapsed source images.
See Hudson pp. 15--19 and M76 derivation 270. -/
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
