import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.ClosedRegionPatchIncidence
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.VertexAbstractComplex

/-!
# Consecutive original vertices determine a whole graph edge

A straight interval in a finite one-dimensional carrier cannot
change faces without meeting an original vertex. Apply the finite
closed-cover lemma to its connected open interval and retain both
endpoints by closure. See Stallings, section 2.A.2, p. 11, and
Dehn derivation 024, section 2.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E)

/-- Different original faces of a graph carrier meet only in
original vertices, including singleton faces. See Dehn 024,
section 2, for the exact image graph. -/
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

/-- A whole straight segment in the finite graph carrier whose
open part avoids all original vertices is one original edge.
Both endpoints are retained; collinear neighboring edges are
not merged. See Dehn 024, section 2. -/
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
