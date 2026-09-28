import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem closedFaceStar_mem_nhds_of_intrinsicInterior (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) {s : Finset E} (hs : s ∈ K.faces)
    (x : K.space) (hx : (x : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    (Subtype.val ⁻¹' (K.closedFaceStar s).space : Set K.space) ∈ 𝓝 x := by
  classical
  let T := hfinite.toFinset.filter (fun t => ¬s ⊆ t)
  let D := ⋃ t ∈ T, convexHull ℝ (t : Set E)
  have hD : IsClosed D :=
    (T.finite_toSet.isCompact_biUnion (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have hxD : (x : E) ∉ D := by
    intro h
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp h
    obtain ⟨htK, hnot⟩ := Finset.mem_filter.mp ht
    exact hnot (K.subset_of_mem_intrinsicInterior_face hs
      (hfinite.mem_toFinset.mp htK) hx hxt)
  have hnhds : (Subtype.val ⁻¹' Dᶜ : Set K.space) ∈ 𝓝 x :=
    (hD.isOpen_compl.preimage continuous_subtype_val).mem_nhds hxD
  apply Filter.mem_of_superset hnhds
  intro y hy
  obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp y.property
  have hst : s ⊆ t := by
    by_contra h
    exact hy (mem_iUnion₂.mpr ⟨t,
      Finset.mem_filter.mpr ⟨hfinite.mem_toFinset.mpr ht, h⟩, hyt⟩)
  exact convexHull_subset_space
    (show t ∈ (K.closedFaceStar s).faces from
      ⟨ht, by simpa only [Finset.union_eq_right.mpr hst] using ht⟩) hyt

end Geometry.SimplicialComplex
