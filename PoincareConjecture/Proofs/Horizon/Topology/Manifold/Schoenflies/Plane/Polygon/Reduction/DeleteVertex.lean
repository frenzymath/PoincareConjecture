import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.SegmentSubdivision
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Cyclic.CyclicDistance
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Reduction.VertexReplacement












set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane



theorem cyclicDistance_rotate_self {N : ℕ} (hN : 2 ≤ N) (k : Fin N) :
    cyclicDistance (finRotate N k) k = N - 1 := by
  have hforward : cyclicDistance k (finRotate N k) = 1 := by
    simpa only [Function.iterate_one] using cyclicDistance_iterate k 1 (by omega)
  have hk : k ≠ finRotate N k := by
    intro h
    rw [← h, cyclicDistance_self] at hforward
    omega
  have hsum := cyclicDistance_add_reverse (finRotate N k) k hk
  omega

variable {n : ℕ}



theorem cyclicArcIndex_delete_last (k : Fin (n + 4)) :
    cyclicArcIndex (finRotate (n + 4) k) (n + 2) (Fin.last (n + 2)) =
      (finRotate (n + 4)).symm k := by
  have hd : cyclicDistance (finRotate (n + 4) k) k = n + 3 := by
    simpa using cyclicDistance_rotate_self (by omega) k
  have hreach : (finRotate (n + 4))^[n + 3] (finRotate (n + 4) k) = k := by
    rw [← hd]
    exact iterate_cyclicDistance _ _
  rw [cyclicArcIndex_last]
  apply (finRotate (n + 4)).injective
  rw [Equiv.apply_symm_apply]
  simpa only [Function.iterate_succ_apply'] using hreach



theorem cyclicArcIndex_delete_range (k : Fin (n + 4)) :
    range (cyclicArcIndex (finRotate (n + 4) k) (n + 2)) = ({k} : Set (Fin (n + 4)))ᶜ := by
  have hd : cyclicDistance (finRotate (n + 4) k) k = n + 3 := by
    simpa using cyclicDistance_rotate_self (by omega) k
  ext i
  rw [mem_range_cyclicArcIndex_iff _ _ (by omega)]
  change cyclicDistance (finRotate (n + 4) k) i ≤ n + 2 ↔ i ≠ k
  constructor
  · intro hi hik
    subst i
    omega
  · intro hi
    have hbound := cyclicDistance_lt (finRotate (n + 4) k) i
    by_contra hle
    have heq : cyclicDistance (finRotate (n + 4) k) i =
        cyclicDistance (finRotate (n + 4) k) k := by omega
    have h := congrArg (fun m => (finRotate (n + 4))^[m] (finRotate (n + 4) k)) heq
    exact hi (by simpa only [iterate_cyclicDistance] using h)



theorem cyclicArcEdgeIndex_delete_range (k : Fin (n + 4)) :
    range (fun j : Fin (n + 2) =>
      cyclicArcIndex (finRotate (n + 4) k) (n + 2) j.castSucc) =
      ({k, (finRotate (n + 4)).symm k} : Set (Fin (n + 4)))ᶜ := by
  have hd : cyclicDistance (finRotate (n + 4) k) k = n + 3 := by
    simpa using cyclicDistance_rotate_self (by omega) k
  have hlast := cyclicArcIndex_delete_last k
  rw [cyclicArcIndex_last] at hlast
  have hpred : cyclicDistance (finRotate (n + 4) k) ((finRotate (n + 4)).symm k) = n + 2 := by
    rw [← hlast]
    exact cyclicDistance_iterate _ _ (by omega)
  have hinj : Function.Injective (cyclicDistance (finRotate (n + 4) k)) := by
    intro i j hij
    have h := congrArg (fun m => (finRotate (n + 4))^[m] (finRotate (n + 4) k)) hij
    simpa only [iterate_cyclicDistance] using h
  ext i
  rw [mem_range_cyclicArcEdgeIndex_iff _ _ (by omega)]
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · intro hi
    constructor
    · intro hik
      subst i
      omega
    · intro hip
      subst i
      omega
  · intro hi
    have hbound := cyclicDistance_lt (finRotate (n + 4) k) i
    by_contra hlt
    have hcases : cyclicDistance (finRotate (n + 4) k) i = n + 2 ∨
        cyclicDistance (finRotate (n + 4) k) i = n + 3 := by omega
    rcases hcases with heq | heq
    · exact hi.2 (hinj (heq.trans hpred.symm))
    · exact hi.1 (hinj (heq.trans hd.symm))



def polygonDeleteVertex {E : Type*} (p : Polygon E (n + 4)) (k : Fin (n + 4)) :
    Polygon E (n + 3) := polygonArc p (finRotate (n + 4) k) (n + 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem polygonDeleteVertex_boundary (p : Polygon E (n + 4)) (k : Fin (n + 4))
    (hstraight : p k ∈ segment ℝ (p ((finRotate (n + 4)).symm k)) (p (finRotate (n + 4) k))) :
    (polygonDeleteVertex p k).boundary ℝ = p.boundary ℝ := by
  have hlast := cyclicArcIndex_delete_last k
  rw [cyclicArcIndex_last] at hlast
  have hD : segment ℝ (p ((finRotate (n + 4)).symm k)) (p (finRotate (n + 4) k)) =
      p.edgeSet ℝ ((finRotate (n + 4)).symm k) ∪ p.edgeSet ℝ k := by
    rw [polygon_edgeSet_eq_segment, polygon_edgeSet_eq_segment, Equiv.apply_symm_apply,
      segment_symm ℝ (p ((finRotate (n + 4)).symm k)) (p k)]
    exact (segment_split_at_point hstraight).1.symm
  rw [polygonDeleteVertex, polygonArc_boundary, hlast, hD]
  apply subset_antisymm
  · intro z hz
    rcases hz with hz | hz
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact polygon_edgeSet_subset_boundary p _ hi
    · exact hz.elim (fun h => polygon_edgeSet_subset_boundary p _ h)
        (fun h => polygon_edgeSet_subset_boundary p _ h)
  · intro z hz
    obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff p z).mp hz
    by_cases hik : i = k
    · subst i
      exact Or.inr (Or.inr hi)
    · by_cases hip : i = (finRotate (n + 4)).symm k
      · subst i
        exact Or.inr (Or.inl hi)
      · have hr : i ∈ range (fun j : Fin (n + 2) =>
            cyclicArcIndex (finRotate (n + 4) k) (n + 2) j.castSucc) := by
          rw [cyclicArcEdgeIndex_delete_range]
          exact fun h => h.elim hik hip
        obtain ⟨j, hj⟩ := hr
        change cyclicArcIndex (finRotate (n + 4) k) (n + 2) j.castSucc = i at hj
        exact Or.inl (mem_iUnion.mpr ⟨j, hj.symm ▸ hi⟩)



theorem IsSimplePolygon.isSimple_polygonDeleteVertex {p : Polygon E (n + 4)}
    (hp : IsSimplePolygon p) (k : Fin (n + 4))
    (hstraight : p k ∈ segment ℝ (p ((finRotate (n + 4)).symm k)) (p (finRotate (n + 4) k))) :
    IsSimplePolygon (polygonDeleteVertex p k) := by
  have hsplit := (segment_split_at_point hstraight).1
  have hT : polygonVertexTriangle p k ⊆
      segment ℝ (p ((finRotate (n + 4)).symm k)) (p (finRotate (n + 4) k)) := by
    apply convexHull_min _ (convex_segment (𝕜 := ℝ) _ _)
    rintro z (hz | hz | hz)
    · exact hz.symm ▸ hstraight
    · exact hz.symm ▸ left_mem_segment ℝ _ _
    · exact hz.symm ▸ right_mem_segment ℝ _ _
  have had : IsAdmissibleVertex p k := by
    change polygonVertexTriangle p k ∩ p.boundary ℝ = _
    apply subset_antisymm _ (polygonIncidentEdges_subset_triangle_inter_boundary p k)
    rintro z ⟨hz, _⟩
    exact hsplit.symm ▸ hT hz
  have hDT : segment ℝ (p ((finRotate (n + 4)).symm k)) (p (finRotate (n + 4) k)) ⊆
      polygonVertexTriangle p k := segment_subset_convexHull (by simp) (by simp)
  have hinj := cyclicArcIndex_injective (finRotate (n + 4) k) (show n + 2 < n + 4 by omega)
  have hnext (i : Fin (n + 2)) :
      (polygonArc p (finRotate (n + 4) k) (n + 2)) (finRotate (n + 3) i.castSucc) =
        p (finRotate (n + 4) (cyclicArcIndex (finRotate (n + 4) k) (n + 2) i.castSucc)) := by
    change p (cyclicArcIndex (finRotate (n + 4) k) (n + 2)
      (finRotate (n + 3) i.castSucc)) = _
    rw [show finRotate (n + 3) i.castSucc = i.succ from finRotate_of_lt i.isLt,
      cyclicArcIndex_succ]
  have hlastIndex := cyclicArcIndex_delete_last k
  have hlast : (polygonArc p (finRotate (n + 4) k) (n + 2)) (Fin.last (n + 2)) =
      p ((finRotate (n + 4)).symm k) := congrArg p hlastIndex
  have hzero : (polygonArc p (finRotate (n + 4) k) (n + 2))
      (finRotate (n + 3) (Fin.last (n + 2))) = p (finRotate (n + 4) k) := by
    rw [finRotate_last]
    rfl
  rw [cyclicArcIndex_last] at hlastIndex
  have hclose (i : Fin (n + 2)) :
      (polygonArc p (finRotate (n + 4) k) (n + 2)).edgeSet ℝ (Fin.last (n + 2)) ∩
        (polygonArc p (finRotate (n + 4) k) (n + 2)).edgeSet ℝ i.castSucc ⊆
      {(polygonArc p (finRotate (n + 4) k) (n + 2)) (Fin.last (n + 2)),
        (polygonArc p (finRotate (n + 4) k) (n + 2)) (finRotate (n + 3) (Fin.last (n + 2)))} ∩
      {(polygonArc p (finRotate (n + 4) k) (n + 2)) i.castSucc,
        (polygonArc p (finRotate (n + 4) k) (n + 2)) (finRotate (n + 3) i.castSucc)} := by
    rw [polygonArc_edgeSet_last, polygonArc_edgeSet_castSucc, hlastIndex, hlast, hzero, hnext]
    have hr : cyclicArcIndex (finRotate (n + 4) k) (n + 2) i.castSucc ∈
        range (fun j : Fin (n + 2) => cyclicArcIndex (finRotate (n + 4) k) (n + 2) j.castSucc) :=
      ⟨i, rfl⟩
    rw [cyclicArcEdgeIndex_delete_range] at hr
    have hne := not_or.mp hr
    rintro z ⟨hzD, hzi⟩
    exact hp.triangle_inter_edge_subset_of_admissible k had _ hne.1 hne.2 ⟨hDT hzD, hzi⟩
  change IsSimplePolygon (polygonArc p (finRotate (n + 4) k) (n + 2))
  refine ⟨by omega, hp.vertices_injective.comp hinj, ?_⟩
  intro i j
  refine Fin.lastCases ?_ (fun a => ?_) i
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · intro hne
      exact (hne rfl).elim
    · intro _
      exact hclose b
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · intro _ z hz
      exact ⟨(hclose a ⟨hz.2, hz.1⟩).2, (hclose a ⟨hz.2, hz.1⟩).1⟩
    · intro hne
      rw [polygonArc_edgeSet_castSucc, polygonArc_edgeSet_castSucc, hnext, hnext]
      exact hp.edges_inter _ _ (fun hab => hne (hinj hab))

end Poincare.Manifold.Schoenflies.Plane
