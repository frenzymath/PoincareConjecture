import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.RelativePolyhedralNeighborhood
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedralUnions

/-!
# Actual finite neighborhoods of compact relative subsets

Finite closed patches from the original source carrier cover the
given compact subset. Their exact finite union stays in the prescribed
relative open set, including at source boundary points.
See Hudson1969, pp.12--19, and Dehn032, section3.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

/-- A compact subset of a finite carrier has an actual finite
polyhedral neighborhood inside any prescribed relative open set.
The new carrier stays inside the entire original carrier.
See Dehn032, section3. -/
theorem exists_relative_compact_polyhedral_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {A O : Set K.space} (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O) :
    ∃ (J : SimplicialComplex ℝ E) (V : Set K.space),
      J.faces.Finite ∧ J.space ⊆ K.space ∧ IsOpen V ∧ A ⊆ V ∧
      Subtype.val '' V ⊆ J.space ∧
      (Subtype.val : K.space → E) ⁻¹' J.space ⊆ O := by
  classical
  choose L W hL hLK hW hxW hWL hLO using fun x : A =>
    K.exists_relative_polyhedral_neighborhood hK x.val hO (hAO x.property)
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover W hW
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
  obtain ⟨J, hJ, hJs, _⟩ := exists_finite_triangulation_iUnion
    (fun x : t => L x) (fun x => hL x)
  let V : Set K.space := ⋃ x : t, W x
  refine ⟨J, V, hJ, ?_, isOpen_iUnion (fun x => hW x), ?_, ?_, ?_⟩
  · intro y hy
    rw [hJs] at hy
    obtain ⟨x, hx⟩ := mem_iUnion.mp hy
    exact hLK x hx
  · intro x hx
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨y, hyt⟩, hxy⟩
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨a, hxa⟩ := mem_iUnion.mp hx
    rw [hJs]
    exact mem_iUnion.mpr ⟨a, hWL a (mem_image_of_mem Subtype.val hxa)⟩
  · intro y hy
    change (y : E) ∈ J.space at hy
    rw [hJs] at hy
    obtain ⟨a, hya⟩ := mem_iUnion.mp hy
    exact hLO a hya

end Geometry.SimplicialComplex
