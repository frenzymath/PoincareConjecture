import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SurfaceDualEdgeGeometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalJointRadii
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCirclePoleBranches

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [DecidableEq E] in


theorem exists_boundary_circle_joint
    (A : SimplicialComplex ℝ E) [Fintype A.faces]
    (hbound : ∀ t ∈ A.faces, t.card ≤ 3)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    {s : Finset E} (hs : s ∈ A.faces) (hsc : s.card = 2) :
    ∃ t : Bool → Finset E,
      (∀ j, t j ∈ A.faces ∧ (t j).card = 3 ∧ s ⊆ t j) ∧
      t false ≠ t true ∧
      (∀ u ∈ A.faces, u.card = 3 → s ⊆ u → u = t false ∨ u = t true) ∧
      IsFinitePLBallPair ℝ (A.barycentricDualBlock s).space
        {(t false).centroid ℝ id, (t true).centroid ℝ id} ∧
      (∀ j, s.centroid ℝ id ≠ (t j).centroid ℝ id) ∧
      (∀ j, IsFinitePLBallPair ℝ (segment ℝ (s.centroid ℝ id) ((t j).centroid ℝ id))
        {s.centroid ℝ id, (t j).centroid ℝ id}) ∧
      (A.barycentricDualBlock s).space =
        segment ℝ (s.centroid ℝ id) ((t false).centroid ℝ id) ∪
          segment ℝ (s.centroid ℝ id) ((t true).centroid ℝ id) ∧
      segment ℝ (s.centroid ℝ id) ((t false).centroid ℝ id) ∩
        segment ℝ (s.centroid ℝ id) ((t true).centroid ℝ id) = {s.centroid ℝ id} := by
  classical
  obtain ⟨t, u, htu, hset⟩ := Set.ncard_eq_two.mp (hcofaces s hs hsc)
  have ht : t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t := hset.symm.subset (Or.inl rfl)
  have hu : u ∈ A.faces ∧ u.card = 3 ∧ s ⊆ u := hset.symm.subset (Or.inr rfl)
  have hexhaust (v : Finset E) (hv : v ∈ A.faces) (hsv : s ⊆ v) (hvc : v.card = 3) :
      v = t ∨ v = u := hset.subset ⟨hv, hvc, hsv⟩
  obtain ⟨hI, hm⟩ := A.isFinitePLBallPair_barycentricDualBlock_of_paired_facet
    (n := 2) hbound hs ht.1 hu.1 hsc ht.2.1 hu.2.1 ht.2.2 hu.2.2 htu hexhaust
  have hsegments := A.dual_interval_eq_centroid_segments hs ht.1 hu.1 ht.2.2 hu.2.2 htu hI hm
  let coface : Bool → Finset E := fun j => if j then u else t
  have hne (j : Bool) : s.centroid ℝ id ≠ (coface j).centroid ℝ id := by
    cases j
    · exact fun h => hm.2 (Or.inl h)
    · exact fun h => hm.2 (Or.inr h)
  refine ⟨coface, ?_, htu, ?_, hI, hne, ?_, hsegments⟩
  · intro j
    cases j
    · exact ht
    · exact hu
  · intro v hv hvc hsv
    exact hexhaust v hv hsv hvc
  · intro j
    have h := isFinitePLBallPair_affine_interval (show (0 : ℝ) < 1 from zero_lt_one)
      (ContinuousAffineMap.lineMap (s.centroid ℝ id) ((coface j).centroid ℝ id))
      (AffineMap.lineMap_injective ℝ (hne j)).injOn
    simpa only [ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap] using h

omit [FiniteDimensional ℝ E] in


theorem boundary_circle_joints_disjoint
    (A L : SimplicialComplex ℝ E) [Fintype A.faces]
    (hfull : ∀ t ∈ A.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces)
    (hLcard : ∀ t ∈ L.faces, t.card ≤ 2)
    {s t : Finset E} (hs : s ∈ L.faces) (ht : t ∈ L.faces)
    (hsc : s.card = 2) (htc : t.card = 2) (hst : s ≠ t) :
    Disjoint (A.barycentricDualBlock s).space (A.barycentricDualBlock t).space := by
  classical
  have hnot : s ∪ t ∉ A.faces := by
    intro hface
    have hLface := hfull (s ∪ t) hface (by
      intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · exact L.face_subset_vertices hs h
      · exact L.face_subset_vertices ht h)
    have hsize := hLcard (s ∪ t) hLface
    have hsu : s = s ∪ t := Finset.eq_of_subset_of_card_le Finset.subset_union_left
      (by simpa only [hsc] using hsize)
    have hts : t ⊆ s := hsu.symm ▸ Finset.subset_union_right
    exact hst (Finset.eq_of_subset_of_card_le hts (by omega)).symm
  rw [Set.disjoint_iff_inter_eq_empty, A.barycentricDualBlock_space_inter]
  exact A.barycentricDualBlock_space_eq_empty_of_not_face
    (Finset.card_pos.mp (by
      have := Finset.card_le_card (show s ⊆ s ∪ t from Finset.subset_union_left)
      omega)) hnot

omit [FiniteDimensional ℝ E] in


theorem boundary_circle_joint_subset_vertex_rim
    (A : SimplicialComplex ℝ E) [Fintype A.faces]
    {s : Finset E} (hs : s ∈ A.faces) (hsc : s.card = 2)
    {p : E} (hp : p ∈ s) :
    (A.barycentricDualBlock s).space ⊆ (A.barycentricSubdivision.link p).space := by
  classical
  obtain ⟨q, hqp, hs'⟩ := Finset.card_eq_two.mp hsc
  rcases hs' with ⟨hqp', rfl⟩
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact fun x hx => (A.dualEdge_space_subset_vertex_links
      (A.face_subset_vertices hs (Finset.mem_insert_self _ _))
      (A.face_subset_vertices hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      hqp' hx).1
  · have hpeq := Finset.mem_singleton.mp hp
    subst p
    exact fun x hx => (A.dualEdge_space_subset_vertex_links
      (A.face_subset_vertices hs (Finset.mem_insert_self _ _))
      (A.face_subset_vertices hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      hqp' hx).2

end PoincareConjecture.M76.Dehn
