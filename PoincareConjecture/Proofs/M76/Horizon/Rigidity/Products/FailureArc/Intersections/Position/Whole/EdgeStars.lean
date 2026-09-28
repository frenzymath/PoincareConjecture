import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.EdgeImages
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarCarrierNeighborhood



set_option autoImplicit false
open Set Geometry Filter
open scoped Topology

namespace Geometry.SimplicialComplex

theorem exists_original_coface_star_image_germ
    {E V X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] [T2Space X] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hxK : x ∈ interior K.space)
    (B : OpenPartialHomeomorph X V)
    (hcofaces : ∀ t ∈ K.faces, s ⊆ t →
      MapsTo g (convexHull ℝ (t : Set E)) B.source ∧
      ∃ A : E →ᴬ[ℝ] V, EqOn (B ∘ g) A (convexHull ℝ (t : Set E))) :
    (K.closedFaceStar s).faces.Finite ∧
    (K.closedFaceStar s).space ⊆ K.space ∧
    x ∈ interior (K.closedFaceStar s).space ∧
    MapsTo g (K.closedFaceStar s).space B.source ∧
    (K.closedFaceStar s).AffineOnFaces (B ∘ g) ∧
    InjOn (B ∘ g) (K.closedFaceStar s).space ∧
    ∃ W : Set X, IsOpen W ∧ g x ∈ W ∧
      ∀ y ∈ W, y ∈ g '' K.space ↔ y ∈ g '' (K.closedFaceStar s).space := by
  have hTK : (K.closedFaceStar s).space ⊆ K.space :=
    space_subset_of_le (K.closedFaceStar_le s)
  have hnhds := K.closedFaceStar_mem_nhds_of_intrinsicInterior hK hs
    ⟨x, interior_subset hxK⟩ hx
  obtain ⟨V, hVT, hV, hxV⟩ := mem_nhds_iff.mp hnhds
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp hV
  have hxU : x ∈ U := hUV.symm.subset hxV
  have hUT : interior K.space ∩ U ⊆ (K.closedFaceStar s).space := by
    intro z hz
    exact hVT (hUV.subset (show (⟨z, interior_subset hz.1⟩ : K.space) ∈
      (Subtype.val : K.space → E) ⁻¹' U from hz.2))
  have hxT : x ∈ interior (K.closedFaceStar s).space :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
      ((isOpen_interior.inter hU).mem_nhds ⟨hxK, hxU⟩) hUT)
  have hmap : MapsTo g (K.closedFaceStar s).space B.source := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := mem_space_iff.mp hz
    exact (hcofaces (s ∪ t) ht.2 Finset.subset_union_left).1
      (convexHull_mono Finset.subset_union_right hzt)
  have hfaces : (K.closedFaceStar s).AffineOnFaces (B ∘ g) := by
    intro t ht
    obtain ⟨A, hA⟩ := (hcofaces (s ∪ t) ht.2 Finset.subset_union_left).2
    exact ⟨A, hA.mono (convexHull_mono Finset.subset_union_right)⟩
  have hcoord : InjOn (B ∘ g) (K.closedFaceStar s).space := by
    intro a ha b hb heq
    exact hgi (hTK ha) (hTK hb) (B.injOn (hmap ha) (hmap hb) heq)
  have hcompact : IsCompact (g '' (K.space \ (interior K.space ∩ U))) :=
    ((K.isCompact_space_of_finite hK).diff (isOpen_interior.inter hU)).image_of_continuousOn
      (hgc.mono sdiff_subset)
  refine ⟨finite_closedFaceStar_faces hK s, hTK, hxT, hmap, hfaces, hcoord,
    (g '' (K.space \ (interior K.space ∩ U)))ᶜ, hcompact.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨z, hz, heq⟩
    exact hz.2 ((hgi hz.1 (interior_subset hxK) heq).symm ▸ ⟨hxK, hxU⟩)
  · intro y hy
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzU : z ∈ interior K.space ∩ U := by
        by_contra hn
        exact hy ⟨z, ⟨hz, hn⟩, rfl⟩
      exact ⟨z, hUT hzU, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact mem_image_of_mem g (hTK hz)

end Geometry.SimplicialComplex
