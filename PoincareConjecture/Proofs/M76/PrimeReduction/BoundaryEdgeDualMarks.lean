import PoincareConjecture.Proofs.M76.Wall.Mathlib.DualStrictCoface
import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryEdgeDualDisk
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.MaximalFaceDual

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K L : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype L.faces]

omit [Fintype L.faces] in

theorem m76_prime_barycentricDualBlock_le_link_of_ssubset
    {s t : Finset E} (hs : s ∈ K.faces) (hst : s ⊂ t) :
    K.barycentricDualBlock t ≤ (K.barycentricDualBlock s).link (s.centroid ℝ id) := by
  exact K.barycentricDualBlock_le_link_of_ssubset hs hst

omit [DecidableEq E] [Fintype L.faces] in

theorem boundary_triangle_dual_contact [Finite L.faces]
    (hLK : L ≤ K) (hLcard : ∀ t ∈ L.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ L.faces) (hscard : s.card = 3) :
    (K.barycentricDualBlock s).space ∩ L.space = {s.centroid ℝ id} := by
  classical
  let : Fintype L.faces := Fintype.ofFinite _
  rw [K.barycentricDualBlock_space_inter_subcomplex L hLK]
  apply L.barycentricDualBlock_space_eq_singleton_of_maximal hs
  intro t ht hst
  exact (Finset.eq_of_subset_of_card_le hst (by
    rw [hscard]
    exact hLcard t ht)).symm

omit [DecidableEq E] [Fintype L.faces] in

theorem disjoint_boundary_triangle_duals
    (hLcard : ∀ t ∈ L.faces, t.card ≤ 3)
    (hfull : ∀ t ∈ K.faces, (∀ p ∈ t, p ∈ L.vertices) → t ∈ L.faces)
    {t u : Finset E} (ht : t ∈ L.faces) (hu : u ∈ L.faces)
    (htcard : t.card = 3) (hucard : u.card = 3) (htu : t ≠ u) :
    Disjoint (K.barycentricDualBlock t).space (K.barycentricDualBlock u).space := by
  classical
  have hnot : t ∪ u ∉ K.faces := by
    intro h
    have hL := hfull _ h (fun p hp => (Finset.mem_union.mp hp).elim
      (fun hp => L.face_subset_vertices ht hp) (fun hp => L.face_subset_vertices hu hp))
    have hle := hLcard _ hL
    have he : t ∪ u = t := (Finset.eq_of_subset_of_card_le
      Finset.subset_union_left (by omega)).symm
    have hut : u ⊆ t := he ▸ Finset.subset_union_right
    exact htu (Finset.eq_of_subset_of_card_le hut (by omega)).symm
  apply disjoint_iff_inter_eq_empty.mpr
  rw [K.barycentricDualBlock_space_inter]
  exact K.barycentricDualBlock_space_eq_empty_of_not_face
    ((L.nonempty_of_mem_faces ht).mono Finset.subset_union_left) hnot

theorem exists_boundary_edge_dual_marks [FiniteDimensional ℝ E]
    (hLK : L ≤ K) (hLcard : ∀ t ∈ L.faces, t.card ≤ 3)
    (hfull : ∀ t ∈ K.faces, (∀ p ∈ t, p ∈ L.vertices) → t ∈ L.faces)
    {s : Finset E} (hs : s ∈ L.faces) (hscard : s.card = 2)
    (hends : (L.faceLink s).vertices.ncard = 2)
    (hI : IsFinitePLBallPair ℝ (K.faceLink s).space (L.faceLink s).space) :
    IsFinitePLBallPair (ℝ × ℝ) (K.barycentricDualBlock s).space
        (((K.barycentricDualBlock s).link (s.centroid ℝ id)).space ∪
          (L.barycentricDualBlock s).space) ∧
      (K.barycentricDualBlock s).space ∩ L.space = (L.barycentricDualBlock s).space ∧
      ∃ t u : Finset E, t ∈ L.faces ∧ u ∈ L.faces ∧
        t.card = 3 ∧ u.card = 3 ∧ s ⊆ t ∧ s ⊆ u ∧ t ≠ u ∧
        (∀ v ∈ L.faces, s ⊆ v → v.card = 3 → v = t ∨ v = u) ∧
        IsFinitePLBallPair ℝ ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space
          {t.centroid ℝ id, u.centroid ℝ id} ∧
        IsFinitePLBallPair ℝ (L.barycentricDualBlock s).space
          {t.centroid ℝ id, u.centroid ℝ id} ∧
        (L.barycentricDualBlock s).space =
          segment ℝ (s.centroid ℝ id) (t.centroid ℝ id) ∪
            segment ℝ (s.centroid ℝ id) (u.centroid ℝ id) ∧
        ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space ∩
            (L.barycentricDualBlock s).space = {t.centroid ℝ id, u.centroid ℝ id} ∧
        (K.barycentricDualBlock t).space ⊆
          ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space ∧
        (K.barycentricDualBlock u).space ⊆
          ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space ∧
        (K.barycentricDualBlock t).space ∩ (L.barycentricDualBlock s).space =
          {t.centroid ℝ id} ∧
        (K.barycentricDualBlock u).space ∩ (L.barycentricDualBlock s).space =
          {u.centroid ℝ id} ∧
        Disjoint (K.barycentricDualBlock t).space (K.barycentricDualBlock u).space := by
  classical
  obtain ⟨t, u, ht, hu, htc, huc, hst, hsu, htu, hcofaces, hMlink, hNlink⟩ :=
    K.exists_boundary_edge_dual_link_data L hLK hLcard hs hscard hends hI
  have hW := L.isFinitePLBallPair_barycentricDualBlock_of_paired_facet hLcard
    hs ht hu hscard htc huc hst hsu htu hcofaces
  have hMne : ((L.barycentricDualBlock s).link (s.centroid ℝ id)).space.Nonempty := by
    rw [hMlink]
    simp
  have hcone := (L.barycentricDualBlock s).closedStar_space_eq_convexJoin_link
    (L.faceCentroid_mem_barycentricDualBlock_vertices hs) hMne
  rw [L.barycentricDualBlock_closedStar_faceCentroid hs, hMlink] at hcone
  have hpair : ({t.centroid ℝ id, u.centroid ℝ id} : Set E) =
      {t.centroid ℝ id} ∪ {u.centroid ℝ id} := by ext x; simp [or_comm]
  rw [hpair, convexJoin_union_right, convexJoin_singletons, convexJoin_singletons] at hcone
  have hmeet := link_space_eq_inter_of_closedStar_eq
    (K.barycentricDualBlock s) (L.barycentricDualBlock s)
    (K.barycentricDualBlock_mono_of_subcomplex L hLK s) (s.centroid ℝ id)
    (L.barycentricDualBlock_closedStar_faceCentroid hs)
  have hstrict (v : Finset E) (hsv : s ⊆ v) (hvc : v.card = 3) : s ⊂ v := by
    apply hsv.ssubset_of_ne
    intro he
    have hc := congrArg Finset.card he
    omega
  have hcontact (v : Finset E) (hv : v ∈ L.faces) (hvc : v.card = 3) (hsv : s ⊆ v) :
      (K.barycentricDualBlock v).space ∩ (L.barycentricDualBlock s).space =
        {v.centroid ℝ id} := by
    rw [← K.barycentricDualBlock_space_inter_subcomplex L hLK s, ← inter_assoc,
      K.barycentricDualBlock_space_inter, Finset.union_eq_left.mpr hsv]
    exact K.boundary_triangle_dual_contact L hLK hLcard hv hvc
  refine ⟨K.isFinitePLBallPair_boundary_edge_dual L hLK hLcard hs hscard hends hI,
    K.barycentricDualBlock_space_inter_subcomplex L hLK s,
    t, u, ht, hu, htc, huc, hst, hsu, htu, hcofaces, hNlink, hW.1, hcone, ?_,
    space_subset_of_le (K.m76_prime_barycentricDualBlock_le_link_of_ssubset (hLK hs) (hstrict t hst htc)),
    space_subset_of_le (K.m76_prime_barycentricDualBlock_le_link_of_ssubset (hLK hs) (hstrict u hsu huc)),
    hcontact t ht htc hst, hcontact u hu huc hsu,
    K.disjoint_boundary_triangle_duals L hLcard hfull ht hu htc huc htu⟩
  rw [inter_comm, ← hmeet, hMlink]

end Geometry.SimplicialComplex
