import PoincareConjecture.Proofs.M25.Topology3D.Polygon.SimplePolygon
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SegmentSubdivision
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SegmentSides
import Mathlib.Tactic.Abel











set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D



theorem finRotate_symm_ne_apply_of_three_le {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    (finRotate n).symm i ≠ finRotate n i := by
  have : NeZero n := ⟨by omega⟩
  intro he
  simp only [finRotate_symm_apply, finRotate_apply] at he
  have hsum : (1 : Fin n) + 1 = 0 := by
    calc
      (1 : Fin n) + 1 = (i + 1) - (i - 1) := by abel
      _ = 0 := by rw [he, sub_self]
  have hval : (1 % n + 1 % n) % n = 0 := congrArg Fin.val hsum
  have h1 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : 2 % n = 2 := Nat.mod_eq_of_lt (by omega)
  rw [h1] at hval
  change 2 % n = 0 at hval
  omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}



theorem IsSimplePolygon.exists_local_two_segments {p : Polygon E n}
    (hp : IsSimplePolygon p) (q : E) (hq : q ∈ p.boundary ℝ) :
    ∃ a b : E, a ≠ q ∧ b ≠ q ∧ segment ℝ q a ∩ segment ℝ q b ⊆ {q} ∧
      ∃ U : Set E, IsOpen U ∧ q ∈ U ∧ ∀ z ∈ U,
        z ∈ p.boundary ℝ ↔ z ∈ segment ℝ q a ∪ segment ℝ q b := by
  classical
  have hclosed (i : Fin n) : IsClosed (p.edgeSet ℝ i) :=
    (polygon_edgeSet_isCompact p i).isClosed
  by_cases hvertex : ∃ k, p k = q
  · obtain ⟨k, rfl⟩ := hvertex
    let j := (finRotate n).symm k
    have hjk : finRotate n j = k := (finRotate n).apply_symm_apply k
    have ha : p j ≠ p k := by simpa only [hjk] using hp.hasNondegenerateEdges j
    have hb : p (finRotate n k) ≠ p k := (hp.hasNondegenerateEdges k).symm
    have hne : j ≠ k := fun he => ha (congrArg p he)
    have hneighbors : j ≠ finRotate n k := finRotate_symm_ne_apply_of_three_le hp.three_le k
    have hsegj : segment ℝ (p k) (p j) = p.edgeSet ℝ j := by
      rw [polygon_edgeSet_eq_segment, hjk, segment_symm]
    have hsegk : segment ℝ (p k) (p (finRotate n k)) = p.edgeSet ℝ k :=
      (polygon_edgeSet_eq_segment p k).symm
    have hinter : segment ℝ (p k) (p j) ∩ segment ℝ (p k) (p (finRotate n k)) ⊆ {p k} := by
      rw [hsegj, hsegk]
      intro z hz
      have hends := hp.edges_inter j k hne hz
      rw [hjk] at hends
      rcases hends.1 with hzj | hzk
      · rcases hends.2 with hzk | hzl
        · exact hzk
        · exact False.elim (hneighbors (hp.vertices_injective (hzj.symm.trans hzl)))
      · exact hzk
    obtain ⟨U, hU, hkU, hlocal⟩ := exists_open_iUnion_eq_of_mem_imp
      (p.edgeSet ℝ) hclosed {j, k} (p k) (by
        intro i hi
        rcases (hp.vertex_mem_edgeSet_iff k i).mp hi with hki | hki
        · exact Or.inr hki.symm
        · apply Or.inl
          exact (finRotate n).injective (hki.symm.trans hjk.symm))
    refine ⟨p j, p (finRotate n k), ha, hb, hinter, U, hU, hkU, ?_⟩
    intro z hz
    change z ∈ ⋃ i, p.edgeSet ℝ i ↔ _
    rw [hlocal z hz, hsegj, hsegk]
    simp only [mem_insert_iff, mem_singleton_iff, exists_eq_or_imp, exists_eq_left, mem_union]
  · obtain ⟨i, hqi⟩ := (polygon_mem_boundary_iff p q).mp hq
    have ha : p i ≠ q := fun he => hvertex ⟨i, he⟩
    have hb : p (finRotate n i) ≠ q := fun he => hvertex ⟨_, he⟩
    have hsplit := segment_split_at_point ((polygon_edgeSet_eq_segment p i) ▸ hqi)
    obtain ⟨U, hU, hqU, hlocal⟩ := exists_open_iUnion_eq_of_mem_imp
      (p.edgeSet ℝ) hclosed {i} q (by
        intro j hqj
        by_contra hji
        have hends := (hp.edges_inter i j (Ne.symm hji) ⟨hqi, hqj⟩).1
        rcases hends with he | he
        · exact ha he.symm
        · exact hb he.symm)
    refine ⟨p i, p (finRotate n i), ha, hb, hsplit.2.subset, U, hU, hqU, ?_⟩
    intro z hz
    change z ∈ ⋃ j, p.edgeSet ℝ j ↔ _
    rw [hlocal z hz, hsplit.1, ← polygon_edgeSet_eq_segment]
    simp only [mem_singleton_iff, exists_eq_left]



theorem IsSimplePolygon.hasLocalTwoSides [FiniteDimensional ℝ E] {p : Polygon E n}
    (hp : IsSimplePolygon p) (hdim : Module.finrank ℝ E = 2) :
    HasLocalTwoSides (p.boundary ℝ) :=
  hasLocalTwoSides_of_locally_two_segments hdim hp.exists_local_two_segments

end PoincareConjecture.M25.Topology3D
