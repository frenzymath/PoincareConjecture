import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.ClosedStarProjectionCoverage
import Mathlib.Analysis.Convex.Intrinsic

/-!
# Whole local affine germs at maximal simplex interiors

Intrinsic interior supplies an actual ambient open neighborhood
on which a set fills its affine span. Finiteness excludes every
other face near a relative-interior point of a maximal simplex.
Both directions of the whole carrier equation are retained.
See Dehn032, section8, and Hudson1969, pp.15--19.
-/

set_option autoImplicit false

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Near an intrinsic-interior point the entire set agrees with
its actual affine span on an ambient open neighborhood. This
uses the definition of intrinsic interior and adds no convexity
or ambient dimension hypothesis. See Dehn032, section8. -/
theorem Set.exists_open_affine_germ_of_mem_intrinsicInterior
    {S : Set E} {p : E} (hp : p ∈ intrinsicInterior ℝ S) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, x ∈ S ↔ x ∈ affineSpan ℝ S := by
  obtain ⟨q, hq, hqp⟩ := mem_intrinsicInterior.mp hp
  obtain ⟨U, hU, hUs⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior ((↑) ⁻¹' S : Set (affineSpan ℝ S))))
  have hpU : p ∈ U := by
    rw [← hqp]
    exact hUs.symm.subset hq
  refine ⟨U, hU, hpU, ?_⟩
  intro x hx
  refine ⟨(fun hxS => subset_affineSpan ℝ S hxS), ?_⟩
  intro hxS
  have hint : (⟨x, hxS⟩ : affineSpan ℝ S) ∈ interior ((↑) ⁻¹' S) := hUs.subset hx
  have hmem : (⟨x, hxS⟩ : affineSpan ℝ S) ∈ (Subtype.val ⁻¹' S) :=
    interior_subset hint
  exact hmem

namespace Geometry.SimplicialComplex

/-- At an intrinsic-interior point of an actual maximal face,
the whole finite carrier agrees locally with that face's affine
span. Every other face is excluded by one closed finite union.
See Dehn032, section8. -/
theorem exists_open_maximal_face_affine_germ
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {a : Finset E} (ha : a ∈ K.faces)
    (hmax : ∀ b ∈ K.faces, a ⊆ b → b = a)
    {p : E} (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set E))) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, x ∈ K.space ↔ x ∈ affineSpan ℝ (a : Set E) := by
  classical
  let bad := hK.toFinset.filter (fun b => b ≠ a)
  let Z := ⋃ b ∈ bad, convexHull ℝ (b : Set E)
  have hZ : IsClosed Z :=
    (bad.finite_toSet.isCompact_biUnion
      (fun b _ => b.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have hpZ : p ∉ Z := by
    intro hp'
    obtain ⟨b, hb, hpb⟩ := mem_iUnion₂.mp hp'
    obtain ⟨hbK, hbne⟩ := Finset.mem_filter.mp hb
    have hbK' := hK.mem_toFinset.mp hbK
    exact hbne (hmax b hbK' (K.subset_of_mem_intrinsicInterior_face ha hbK' hp hpb))
  obtain ⟨V, hV, hpV, hVaff⟩ := Set.exists_open_affine_germ_of_mem_intrinsicInterior hp
  refine ⟨V ∩ Zᶜ, hV.inter hZ.isOpen_compl, ⟨hpV, hpZ⟩, ?_⟩
  intro x hx
  have hcarrier : x ∈ K.space ↔ x ∈ convexHull ℝ (a : Set E) := by
    refine ⟨?_, fun hxa => K.convexHull_subset_space ha hxa⟩
    intro hxK
    obtain ⟨b, hb, hxb⟩ := mem_space_iff.mp hxK
    have hba : b = a := by
      by_contra hne
      exact hx.2 (mem_iUnion₂.mpr ⟨b,
        Finset.mem_filter.mpr ⟨hK.mem_toFinset.mpr hb, hne⟩, hxb⟩)
    exact hba ▸ hxb
  exact hcarrier.trans (by simpa only [affineSpan_convexHull] using hVaff x hx.1)

end Geometry.SimplicialComplex
