import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Reduction.AdmissibleVertex
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Reduction.CutVertex
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Triangle.EmptyTriangle
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Reduction.SupportingVertex
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Triangle.TriangleRegion










set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} {p : Polygon E n}



theorem IsSimplePolygon.admissibleVertex_of_triangle_arc (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) (a : Fin n)
    (hdiag : Disjoint (openSegment ℝ (p a) (p ((finRotate n)^[2] a))) (p.boundary ℝ))
    (hseg : segment ℝ (p a) (p ((finRotate n)^[2] a)) ⊆ closure (polygonInterior p)) :
    IsAdmissibleVertex p (finRotate n a) ∧
      polygonVertexTriangle p (finRotate n a) ⊆ closure (polygonInterior p) := by
  let q : Polygon E 3 := polygonArc p a 2
  let c := finRotate n a
  let b := (finRotate n)^[2] a
  have hq : IsSimplePolygon q := hp.isSimple_polygonArc a 2 (by omega)
    (by have := hp.three_le; omega) hdiag
  have hq0 : q 0 = p a := rfl
  have hq1 : q 1 = p c := rfl
  have hq2 : q 2 = p b := rfl
  have hpred : (finRotate n).symm c = a := (finRotate n).symm_apply_apply a
  have hsucc : finRotate n c = b := rfl
  have hThull : polygonVertexTriangle p c = convexHull ℝ (range q) := by
    unfold polygonVertexTriangle
    rw [hpred, hsucc]
    apply congrArg (convexHull ℝ)
    ext x
    constructor
    · rintro (hx | hx | hx)
      · exact ⟨1, hq1.trans hx.symm⟩
      · exact ⟨0, hq0.trans hx.symm⟩
      · exact ⟨2, hq2.trans hx.symm⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inr (Or.inl hq0)
      · exact Or.inl hq1
      · exact Or.inr (Or.inr hq2)
  have hboundary : q.boundary ℝ ⊆
      p.edgeSet ℝ a ∪ p.edgeSet ℝ c ∪ segment ℝ (p a) (p b) := by
    intro x hx
    obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff q x).mp hx
    fin_cases i
    · change x ∈ (polygonArc p a 2).edgeSet ℝ (0 : Fin 2).castSucc at hi
      rw [polygonArc_edgeSet_castSucc] at hi
      exact Or.inl (Or.inl hi)
    · change x ∈ (polygonArc p a 2).edgeSet ℝ (1 : Fin 2).castSucc at hi
      rw [polygonArc_edgeSet_castSucc] at hi
      exact Or.inl (Or.inr hi)
    · change x ∈ (polygonArc p a 2).edgeSet ℝ (Fin.last 2) at hi
      rw [polygonArc_edgeSet_last, segment_symm] at hi
      exact Or.inr hi
  have hB : q.boundary ℝ ⊆ closure (polygonInterior p) := by
    intro x hx
    rcases hboundary hx with (ha | hc) | hd
    · rw [hp.closure_polygonInterior hdim]
      exact Or.inr (polygon_edgeSet_subset_boundary p a ha)
    · rw [hp.closure_polygonInterior hdim]
      exact Or.inr (polygon_edgeSet_subset_boundary p c hc)
    · exact hseg hd
  have hnested := hp.polygonRegions_subset_of_boundary_subset_closureInterior hq hdim hB
  have hTclosure : polygonVertexTriangle p c = closure (polygonInterior q) :=
    hThull.trans (hq.triangle_closure_polygonInterior hdim).symm
  refine ⟨?_, ?_⟩
  · change polygonVertexTriangle p c ∩ p.boundary ℝ = _
    apply subset_antisymm _ (polygonIncidentEdges_subset_triangle_inter_boundary p c)
    rintro x ⟨hxT, hxB⟩
    have hxq : x ∈ closure (polygonInterior q) := hTclosure ▸ hxT
    rw [hq.closure_polygonInterior hdim] at hxq
    have hxqB : x ∈ q.boundary ℝ :=
      hxq.resolve_left fun hxI => (hnested.1 hxI).1 hxB
    rcases hboundary hxqB with (ha | hc) | hd
    · left
      rw [hpred, segment_symm]
      exact (polygon_edgeSet_eq_segment p a) ▸ ha
    · right
      exact (polygon_edgeSet_eq_segment p c) ▸ hc
    · rw [← insert_endpoints_openSegment] at hd
      rcases hd with ha | hb | hopen
      · left
        rw [ha, hpred]
        exact right_mem_segment ℝ _ _
      · right
        rw [hb, hsucc]
        exact right_mem_segment ℝ _ _
      · exact (Set.disjoint_left.mp hdiag hopen hxB).elim
  · change polygonVertexTriangle p c ⊆ closure (polygonInterior p)
    rw [hTclosure]
    exact hnested.2




theorem IsSimplePolygon.exists_admissible_vertex_away_edge (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) (hn : 3 < n) (i : Fin n) :
    ∃ k : Fin n, k ≠ i ∧ k ≠ finRotate n i ∧ IsAdmissibleVertex p k ∧
      polygonVertexTriangle p k ⊆ closure (polygonInterior p) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hchild (c d : Fin n) (hcd : d ≠ c)
        (hq : IsSimplePolygon (polygonCut p c d))
        (hsmall : cyclicDistance c d + 1 < n)
        (hother : cyclicDistance d i < cyclicDistance d c)
        (hdiag : Disjoint (openSegment ℝ (p c) (p d)) (p.boundary ℝ))
        (hseg : segment ℝ (p c) (p d) ⊆ closure (polygonInterior p)) :
        ∃ k : Fin n, k ≠ i ∧ k ≠ finRotate n i ∧ IsAdmissibleVertex p k ∧
          polygonVertexTriangle p k ⊆ closure (polygonInterior p) := by
      by_cases hthree : cyclicDistance c d + 1 = 3
      · have hcd2 : cyclicDistance c d = 2 := by omega
        have hd : (finRotate n)^[2] c = d := by
          simpa only [hcd2] using iterate_cyclicDistance c d
        obtain ⟨had, hT⟩ := hp.admissibleVertex_of_triangle_arc hdim c
          (by simpa only [hd] using hdiag) (by simpa only [hd] using hseg)
        let j : Fin (cyclicDistance c d + 1) := ⟨1, by omega⟩
        have hj0 : j ≠ 0 := by
          intro h
          have hv := congrArg (fun x : Fin (cyclicDistance c d + 1) => x.val) h
          norm_num [j] at hv
        have hjlast : j ≠ Fin.last (cyclicDistance c d) := by
          intro h
          have hv := congrArg (fun x : Fin (cyclicDistance c d + 1) => x.val) h
          simp only [j, Fin.val_last] at hv
          omega
        have haway := cyclicArcIndex_internal_ne_other_edge c d hcd j hj0 hjlast i hother
        have hj : cyclicArcIndex c (cyclicDistance c d) j = finRotate n c := rfl
        rw [hj] at haway
        exact ⟨finRotate n c, haway.1, haway.2, had, hT⟩
      · have hlarge : 3 < cyclicDistance c d + 1 := by
          have := hq.three_le
          omega
        obtain ⟨j, hjlast, hjnext, had, hT⟩ :=
          ih _ hsmall hq hlarge (Fin.last (cyclicDistance c d))
        have hj0 : j ≠ 0 := by simpa only [finRotate_last] using hjnext
        let l := cyclicArcIndex c (cyclicDistance c d) j
        have hpred : (polygonCut p c d) ((finRotate (cyclicDistance c d + 1)).symm j) =
            p ((finRotate n).symm l) :=
          congrArg p (cyclicArcIndex_rotate_symm c _ j hj0)
        have hsucc : (polygonCut p c d) (finRotate (cyclicDistance c d + 1) j) =
            p (finRotate n l) :=
          congrArg p (cyclicArcIndex_rotate c _ j hjlast)
        have hregions := hp.polygonCut_regions_subset c d hq hdim hseg
        have htransfer := hq.admissibleVertex_of_child hdim j l rfl hpred hsucc
          hregions.1 hT had
        have haway := cyclicArcIndex_internal_ne_other_edge c d hcd j hj0 hjlast i hother
        exact ⟨l, haway.1, haway.2, htransfer⟩
    obtain ⟨e, a, hai, har, hmin, _, hli⟩ := hp.exists_supporting_vertex_away_edge hdim i
    let X : E →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp e.toContinuousLinearMap
    have hX : Function.Surjective X := by
      intro t
      refine ⟨e.symm (t, 0), ?_⟩
      simp [X]
    have hsupport : ∀ j, X (p a) ≤ X (p j) := hmin
    by_cases hempty : ∀ j, p j ∈ polygonVertexTriangle p a →
        j = a ∨ j = (finRotate n).symm a ∨ j = finRotate n a
    · exact ⟨a, hai, har,
        hp.supporting_triangle_of_no_triangle_vertex hdim hn a hli X hX hsupport hempty⟩
    · push Not at hempty
      obtain ⟨j, hjT, hja, hjpred, hjsucc⟩ := hempty
      obtain ⟨b, hba, hbpred, hbsucc, hopen, hseg⟩ :=
        hp.exists_visible_diagonal_of_triangle_vertex hdim a hli X hX hsupport
          ⟨j, hja, hjpred, hjsucc, hjT⟩
      have hdiag : Disjoint (openSegment ℝ (p a) (p b)) (p.boundary ℝ) :=
        Set.disjoint_left.mpr fun _ hx hxB => (hopen hx).1 hxB
      obtain ⟨hsmallAB, hsmallBA, hqAB, hqBA⟩ :=
        hp.polygonCut_pair a b hba hbsucc hbpred hdiag
      have hi : i ∈
          range (fun j : Fin (cyclicDistance a b) =>
            cyclicArcIndex a (cyclicDistance a b) j.castSucc) ∪
          range (fun j : Fin (cyclicDistance b a) =>
            cyclicArcIndex b (cyclicDistance b a) j.castSucc) := by
        rw [(cyclicArc_edgeIndex_partition a b hba).2]
        exact mem_univ i
      rcases hi with hi | hi
      · apply hchild b a hba.symm hqBA hsmallBA
          ((mem_range_cyclicArcEdgeIndex_iff a _ (cyclicDistance_lt a b) i).mp hi)
        · simpa only [openSegment_symm] using hdiag
        · simpa only [segment_symm] using hseg
      · exact hchild a b hba hqAB hsmallAB
          ((mem_range_cyclicArcEdgeIndex_iff b _ (cyclicDistance_lt b a) i).mp hi) hdiag hseg

end Poincare.Manifold.Schoenflies.Plane
