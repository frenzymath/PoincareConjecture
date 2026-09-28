import PoincareConjecture.Proofs.M76.Mathlib.ClosedRegionPatchIncidence
import PoincareConjecture.Proofs.M76.Mathlib.VertexAbstractComplex

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E)

theorem graph_face_contacts_subset_vertices
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hne : s ≠ t) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆ K.vertices := by
  classical
  have hcard : (s ∩ t).card ≤ 1 := by
    by_contra h
    have htwo : 2 ≤ (s ∩ t).card := by omega
    have hs' : s ∩ t = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      ((hdim s hs).trans htwo)
    have ht' : s ∩ t = t := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      ((hdim t ht).trans htwo)
    exact hne (hs'.symm.trans ht')
  have hcv : Convex ℝ ((s ∩ t : Finset E) : Set E) :=
    (Finset.card_le_one_iff_subsingleton.mp hcard).convex
  intro x hx
  have h := K.inter_subset_convexHull hs ht hx
  rw [← Finset.coe_inter, hcv.convexHull_eq] at h
  exact K.down_closed hs
    (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp h).1)
    (Finset.singleton_nonempty x)

theorem pair_mem_faces_of_segment_avoids_vertices [DecidableEq E]
    (hK : K.faces.Finite) (hdim : ∀ s ∈ K.faces, s.card ≤ 2)
    {a b : E} (ha : a ∈ K.vertices) (hb : b ∈ K.vertices)
    (hsegment : segment ℝ a b ⊆ K.space)
    (havoid : Disjoint (openSegment ℝ a b) K.vertices) :
    ({a, b} : Finset E) ∈ K.faces := by
  classical
  let : Finite K.faces := hK.to_subtype
  have hconnected : IsConnected (openSegment ℝ a b) :=
    (convex_openSegment a b).isConnected ⟨midpoint ℝ a b, midpoint_mem_openSegment a b⟩
  have hcover : openSegment ℝ a b ⊆
      ⋃ s : K.faces, convexHull ℝ (s.val : Set E) := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp
      (hsegment (openSegment_subset_segment ℝ a b hx))
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, hxs⟩
  obtain ⟨s, hs⟩ := hconnected.exists_closure_subset_of_finite_closed_cover
    (fun s : K.faces => convexHull ℝ (s.val : Set E))
    (fun s => s.val.finite_toSet.isClosed_convexHull ℝ) hcover
    (fun s t hst => K.graph_face_contacts_subset_vertices hdim s.property t.property
      (fun h => hst (Subtype.ext h))) havoid
  have hwhole : segment ℝ a b ⊆ convexHull ℝ (s.val : Set E) :=
    segment_subset_closure_openSegment.trans hs
  have has : a ∈ s.val := (K.vertex_mem_convexHull_iff ha s.property).mp
    (hwhole (left_mem_segment ℝ a b))
  have hbs : b ∈ s.val := (K.vertex_mem_convexHull_iff hb s.property).mp
    (hwhole (right_mem_segment ℝ a b))
  exact K.down_closed s.property
    (Finset.insert_subset_iff.mpr ⟨has, Finset.singleton_subset_iff.mpr hbs⟩)
    (Finset.insert_nonempty _ _)

end Geometry.SimplicialComplex
