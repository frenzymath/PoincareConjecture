import PoincareConjecture.Proofs.M76.Mathlib.FaceStarSaturation
import Mathlib.Data.Finset.Max










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]





theorem exists_minimal_faceStar_neighborhood_of_finite (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) (x : K.space) :
    ∃ s ∈ K.faces, (x : E) ∈ convexHull ℝ (s : Set E) ∧
      (∀ t ∈ K.faces, (x : E) ∈ convexHull ℝ (t : Set E) → s ⊆ t) ∧
      ∃ V : Set K.space, IsOpen V ∧ x ∈ V ∧
        Subtype.val '' V ⊆ (K.closedFaceStar s).space := by
  classical
  let T := hfinite.toFinset.filter (fun s : Finset E => (x : E) ∈ convexHull ℝ (s : Set E))
  have hT : T.Nonempty := by
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp x.property
    exact ⟨s, Finset.mem_filter.mpr ⟨hfinite.mem_toFinset.mpr hs, hxs⟩⟩
  obtain ⟨s, hsT, hmin⟩ := T.exists_min_image (fun t => t.card) hT
  obtain ⟨hsK', hxs⟩ := Finset.mem_filter.mp hsT
  have hsK := hfinite.mem_toFinset.mp hsK'
  have hsub : ∀ t ∈ K.faces, (x : E) ∈ convexHull ℝ (t : Set E) → s ⊆ t := by
    intro t ht hxt
    have hxi : (x : E) ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using K.inter_subset_convexHull hsK ht ⟨hxs, hxt⟩
    have hne : (s ∩ t).Nonempty := by
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      simp [he] at hxi
    have hiK := K.down_closed hsK Finset.inter_subset_left hne
    have hiT : s ∩ t ∈ T :=
      Finset.mem_filter.mpr ⟨hfinite.mem_toFinset.mpr hiK, hxi⟩
    have he : s ∩ t = s :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (hmin _ hiT)
    exact he ▸ Finset.inter_subset_right
  let F := hfinite.toFinset.filter (fun t => ¬s ⊆ t)
  let D := ⋃ t ∈ F, convexHull ℝ (t : Set E)
  have hD : IsClosed D :=
    (F.finite_toSet.isCompact_biUnion
      (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have hxD : (x : E) ∉ D := by
    intro hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    obtain ⟨htK, hst⟩ := Finset.mem_filter.mp ht
    exact hst (hsub t (hfinite.mem_toFinset.mp htK) hxt)
  let V : Set K.space := Subtype.val ⁻¹' Dᶜ
  refine ⟨s, hsK, hxs, hsub, V, hD.isOpen_compl.preimage continuous_subtype_val, hxD, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp y.property
  have hst : s ⊆ t := by
    by_contra h
    exact hy (mem_iUnion₂.mpr ⟨t,
      Finset.mem_filter.mpr ⟨hfinite.mem_toFinset.mpr ht, h⟩, hyt⟩)
  exact convexHull_subset_space
    (show t ∈ (K.closedFaceStar s).faces from
      ⟨ht, by simpa only [Finset.union_eq_right.mpr hst] using ht⟩) hyt




theorem exists_faceStar_neighborhood_of_finite (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) (x : K.space) :
    ∃ s ∈ K.faces, (x : E) ∈ convexHull ℝ (s : Set E) ∧
      ∃ V : Set K.space, IsOpen V ∧ x ∈ V ∧
        Subtype.val '' V ⊆ (K.closedFaceStar s).space := by
  obtain ⟨s, hs, hxs, _, V, hV, hxV, hVstar⟩ :=
    K.exists_minimal_faceStar_neighborhood_of_finite hfinite x
  exact ⟨s, hs, hxs, V, hV, hxV, hVstar⟩

end Geometry.SimplicialComplex
