import PoincareConjecture.Proofs.M76.Mathlib.OriginalConnectorBody

set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex

theorem exists_original_maximal_face_image_germ
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ t ∈ K.faces, s ⊆ t → t = s)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    ∃ W : Set X, IsOpen W ∧ g x ∈ W ∧
      ∀ y ∈ W, y ∈ g '' K.space ↔ y ∈ g '' convexHull ℝ (s : Set E) := by
  obtain ⟨U, hU, hfaceU, hfaces, _⟩ :=
    K.exists_open_maximal_face_interior_neighborhood hK hs hmax
  have hxK : x ∈ K.space := K.convexHull_subset_space hs (intrinsicInterior_subset hx)
  have hcompact : IsCompact (g '' (K.space \ U)) :=
    ((K.isCompact_space_of_finite hK).diff hU).image_of_continuousOn
      (hgc.mono sdiff_subset)
  refine ⟨(g '' (K.space \ U))ᶜ, hcompact.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨z, hz, heq⟩
    exact hz.2 ((hgi hz.1 hxK heq).symm ▸ hfaceU hx)
  · intro y hy
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzU : z ∈ U := by
        by_contra hn
        exact hy ⟨z, ⟨hz, hn⟩, rfl⟩
      obtain ⟨t, ht, hzt⟩ := mem_space_iff.mp hz
      exact ⟨z, hfaces t ht ⟨z, hzt, hzU⟩ ▸ hzt, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact mem_image_of_mem g (K.convexHull_subset_space hs hz)

end Geometry.SimplicialComplex
