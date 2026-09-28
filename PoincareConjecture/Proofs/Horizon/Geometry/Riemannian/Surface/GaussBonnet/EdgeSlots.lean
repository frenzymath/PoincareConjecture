import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Planar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]

theorem coordinateTriangle_side_injective
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : convexHull ℝ (range b) ⊆ F.source) :
    Function.Injective (fun k : Fin 3 =>
      F '' affineSegment ℝ (b (k.succAbove 0)) (b (k.succAbove 1))) := by
  have hside (i : Fin 3) :
      affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) ⊆ F.source := by
    rw [affineSegment_eq_segment]
    exact (segment_subset_convexHull (mem_range_self _) (mem_range_self _)).trans hsource
  intro i j heq
  dsimp only at heq
  have hzero : ∀ z ∈ affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)),
      b.coord i z = 0 := by
    rintro z ⟨t, ht, rfl⟩
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
    simp [b.coord_apply]
  have hj0 : b.coord i (b (j.succAbove 0)) = 0 := by
    have hz := left_mem_affineSegment ℝ (b (j.succAbove 0)) (b (j.succAbove 1))
    obtain ⟨z, hz', hF⟩ := heq.symm ▸ mem_image_of_mem F hz
    rw [← F.injOn (hside i hz') (hside j hz) hF]
    exact hzero z hz'
  have hj1 : b.coord i (b (j.succAbove 1)) = 0 := by
    have hz := right_mem_affineSegment ℝ (b (j.succAbove 0)) (b (j.succAbove 1))
    obtain ⟨z, hz', hF⟩ := heq.symm ▸ mem_image_of_mem F hz
    rw [← F.injOn (hside i hz') (hside j hz) hF]
    exact hzero z hz'
  by_contra hne
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
  fin_cases k
  · change j.succAbove (0 : Fin 2) = i at hk
    rw [hk, b.coord_apply_eq] at hj0
    norm_num at hj0
  · change j.succAbove (1 : Fin 2) = i at hk
    rw [hk, b.coord_apply_eq] at hj1
    norm_num at hj1

variable [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [IsManifold (𝓡 2) ∞ S]

namespace FiniteSmoothTriangulation

theorem face_edge_injective_of_coordinates
    (T : FiniteSmoothTriangulation (M := S))
    (F : T.faces → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : T.faces → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : ∀ f, convexHull ℝ (range (b f)) ⊆ (F f).source)
    (hside : ∀ f k, ((T.face f).boundary k).map '' Icc (0 : ℝ) 1 =
      F f '' affineSegment ℝ (b f (k.succAbove 0)) (b f (k.succAbove 1)))
    (f : T.faces) : Function.Injective (T.face_edge f) := by
  intro i j hij
  apply coordinateTriangle_side_injective (F f) (b f) (hsource f)
  dsimp only
  rw [← hside f i, ← hside f j, T.face_edge_map, T.face_edge_map, hij]

theorem exists_edge_slot_equiv
    (T : FiniteSmoothTriangulation (M := S))
    (hinj : ∀ f, Function.Injective (T.face_edge f)) :
    ∃ slots : (T.faces × Fin 3) ≃ (T.edges × Fin 2),
      (∀ q, T.face_edge (slots.symm q).1 (slots.symm q).2 = q.1) ∧
      (∀ q, (slots.symm q).1 = T.edge_face q.1 q.2) := by
  classical
  choose index hindex using T.edge_face_boundary
  let pair : T.edges × Fin 2 → T.faces × Fin 3 :=
    fun q => (T.edge_face q.1 q.2, index q.1 q.2)
  have hpair (q : T.edges × Fin 2) : T.face_edge (pair q).1 (pair q).2 = q.1 :=
    hindex q.1 q.2
  have hpair_inj : Function.Injective pair := by
    rintro ⟨e, i⟩ ⟨d, j⟩ h
    have hed : e = d := (hpair (e, i)).symm.trans
      ((congrArg (fun p : T.faces × Fin 3 => T.face_edge p.1 p.2) h).trans (hpair (d, j)))
    subst d
    have hf : T.edge_face e i = T.edge_face e j := congrArg Prod.fst h
    have hij : i = j := by
      fin_cases i <;> fin_cases j
      · rfl
      · exact (T.edge_faces_distinct e hf).elim
      · exact (T.edge_faces_distinct e hf.symm).elim
      · rfl
    exact congrArg (Prod.mk e) hij
  have hpair_surj : Function.Surjective pair := by
    rintro ⟨f, k⟩
    let e := T.face_edge f k
    rcases T.edge_face_exact e f k rfl with hf | hf
    · refine ⟨(e, 0), Prod.ext hf.symm ?_⟩
      apply hinj f
      change T.face_edge f (index e 0) = e
      rw [hf]
      exact hindex e 0
    · refine ⟨(e, 1), Prod.ext hf.symm ?_⟩
      apply hinj f
      change T.face_edge f (index e 1) = e
      rw [hf]
      exact hindex e 1
  exact ⟨(Equiv.ofBijective pair ⟨hpair_inj, hpair_surj⟩).symm, hpair, fun _ => rfl⟩

theorem three_card_faces_eq_two_card_edges
    (T : FiniteSmoothTriangulation (M := S))
    (hinj : ∀ f, Function.Injective (T.face_edge f)) :
    letI := T.faces_finite
    letI := T.edges_finite
    3 * Fintype.card T.faces = 2 * Fintype.card T.edges := by
  let _ := T.faces_finite
  let _ := T.edges_finite
  obtain ⟨slots, _, _⟩ := T.exists_edge_slot_equiv hinj
  have h := Fintype.card_congr slots
  simpa [Fintype.card_prod, Nat.mul_comm] using h

end FiniteSmoothTriangulation
end PoincareConjecture.Topology.Surface
