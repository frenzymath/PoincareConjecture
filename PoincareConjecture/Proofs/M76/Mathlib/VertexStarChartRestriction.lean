import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarCarrierNeighborhood
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  [TopologicalSpace F]

theorem injOn_and_interior_closedStar_of_chart (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) {p : E} (hp : {p} ∈ K.faces)
    (e : OpenPartialHomeomorph K.space F) (f : E → F)
    (hsource : ∀ y : K.space, (y : E) ∈ (K.closedFaceStar {p}).space → y ∈ e.source)
    (he : ∀ y : K.space, (y : E) ∈ (K.closedFaceStar {p}).space → e y = f y) :
    InjOn f (K.closedFaceStar {p}).space ∧
      f p ∈ interior (f '' (K.closedFaceStar {p}).space) := by
  have hsub : (K.closedFaceStar {p}).space ⊆ K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact convexHull_subset_space hs.1 hxs
  have hpK : p ∈ K.space := convexHull_subset_space hp (by simp)
  let a : K.space := ⟨p, hpK⟩
  let S : Set K.space := Subtype.val ⁻¹' (K.closedFaceStar {p}).space
  have hS : S ∈ 𝓝 a := K.closedFaceStar_mem_nhds_of_intrinsicInterior hfinite hp a (by
    simp [a, intrinsicInterior_singleton])
  have haS : (a : E) ∈ (K.closedFaceStar {p}).space :=
    (show a ∈ S from mem_of_mem_nhds hS)
  have himage : e '' S = f '' (K.closedFaceStar {p}).space := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (he y hy).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hsub hy⟩, hy, he ⟨y, hsub hy⟩ hy⟩
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    have hexy : e ⟨x, hsub hx⟩ = e ⟨y, hsub hy⟩ := by
      rw [he _ hx, he _ hy]
      exact hxy
    exact congrArg Subtype.val (e.injOn (hsource _ hx) (hsource _ hy) hexy)
  · apply mem_interior_iff_mem_nhds.mpr
    have hn := e.image_mem_nhds (hsource a haS) hS
    rwa [himage, he a haS] at hn

end Geometry.SimplicialComplex
