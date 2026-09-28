import PoincareConjecture.Proofs.M76.Mathlib.CyclicMarkedIndices
import PoincareConjecture.Proofs.M76.Mathlib.MarkedPolygonSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.PolygonReindex
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSplitIntersection
import PoincareConjecture.Proofs.M76.Mathlib.PolygonPathCycles
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLinearChain











set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {N : ℕ}





theorem exists_arcs_at_vertices (P : Polygon E (N + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (a b : Fin (N + 3)) (hab : a ≠ b) :
    ∃ U V : Set E, IsFinitePLBallPair ℝ U {P a, P b} ∧
      IsFinitePLBallPair ℝ V {P a, P b} ∧
      U ∪ V = P.boundary ℝ ∧ U ∩ V = {P a, P b} := by
  classical
  obtain ⟨m, n, e, he, hea, heb⟩ := Fin.exists_cyclic_marked_split a b hab
  let u : Fin (m + 1) → E := fun i => P (e (i.castAdd (n + 1)))
  let v : Fin (n + 1) → E := fun i => P (e (Fin.natAdd (m + 1) i))
  let Q : Polygon E ((m + 1) + (n + 1)) := mk (Fin.append u v)
  let p : Fin (m + 2) → E := Fin.snoc u (v 0)
  let q : Fin (n + 2) → E := Fin.snoc v (u 0)
  have hfun : Fin.append u v = P ∘ e := by
    funext i
    induction i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right] <;> rfl
  have hpoly : Q = P.reindex e := congrArg mk hfun
  have hQ : Q.HasSimplicialEdges := by
    rw [hpoly]
    exact P.hasSimplicialEdges_reindex hP e he
  have hQi : Function.Injective Q := by
    change Function.Injective (Fin.append u v)
    rw [hfun]
    exact hinj.comp e.injective
  have hboundary : Q.boundary ℝ = P.boundary ℝ := by
    rw [hpoly, P.boundary_reindex e he]
  have hrange : range Q = range P := by
    change range (Fin.append u v) = _
    rw [hfun]
    exact e.surjective.range_comp P
  have hu0 : u 0 = P a := congrArg P hea
  have hv0 : v 0 = P b := congrArg P heb
  have hleft (i : Fin (m + 1)) :
      segment ℝ (p i.castSucc) (p i.succ) = Q.edgeSet ℝ (i.castAdd (n + 1)) := by
    have hi := edgeSet_split_left u v i
    have hrot : finRotate ((m + 1) + 1) i.castSucc = i.succ :=
      finRotate_of_lt i.isLt
    simpa only [edgeSet, hrot, affineSegment_eq_segment] using hi
  have hright (i : Fin (n + 1)) :
      segment ℝ (q i.castSucc) (q i.succ) = Q.edgeSet ℝ (Fin.natAdd (m + 1) i) := by
    have hi := edgeSet_split_right u v i
    have hrot : finRotate ((n + 1) + 1) i.castSucc = i.succ :=
      finRotate_of_lt i.isLt
    simpa only [edgeSet, hrot, affineSegment_eq_segment] using hi
  have hleftEnd (i : Fin (m + 1)) :
      (Q.edgeVertices (i.castAdd (n + 1)) : Set E) = {p i.castSucc, p i.succ} := by
    change ((mk (Fin.append u v)).edgeVertices (i.castAdd (n + 1)) : Set E) = _
    rw [← edgeVertices_split_left u v i]
    have hrot : finRotate ((m + 1) + 1) i.castSucc = i.succ :=
      finRotate_of_lt i.isLt
    simp only [edgeVertices, hrot, Finset.coe_pair, p]
  have hrightEnd (i : Fin (n + 1)) :
      (Q.edgeVertices (Fin.natAdd (m + 1) i) : Set E) = {q i.castSucc, q i.succ} := by
    change ((mk (Fin.append u v)).edgeVertices (Fin.natAdd (m + 1) i) : Set E) = _
    rw [← edgeVertices_split_right u v i]
    have hrot : finRotate ((n + 1) + 1) i.castSucc = i.succ :=
      finRotate_of_lt i.isLt
    simp only [edgeVertices, hrot, Finset.coe_pair, q]
  obtain ⟨hpi, hqi⟩ := injective_split u v hQi
  have hU : IsFinitePLBallPair ℝ (pathCarrier p) {P a, P b} := by
    have h := Set.isFinitePLBallPair_linear_chain p hpi (fun i j => by
      rw [hleft, hleft, ← hleftEnd, ← hleftEnd]
      exact hQ _ _)
    simpa only [pathCarrier, p, Fin.snoc_apply_zero, Fin.snoc_last, hu0, hv0] using h
  have hV : IsFinitePLBallPair ℝ (pathCarrier q) {P a, P b} := by
    have h := Set.isFinitePLBallPair_linear_chain q hqi (fun i j => by
      rw [hright, hright, ← hrightEnd, ← hrightEnd]
      exact hQ _ _)
    simpa only [pathCarrier, q, Fin.snoc_apply_zero, Fin.snoc_last, hu0, hv0, pair_comm] using h
  refine ⟨pathCarrier p, pathCarrier q, hU, hV, ?_, ?_⟩
  · rw [← hboundary]
    ext x
    constructor
    · rintro (hx | hx)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i.castAdd (n + 1), hleft i ▸ hi⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨Fin.natAdd (m + 1) i, hright i ▸ hi⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      induction i using Fin.addCases with
      | left i => exact Or.inl (mem_iUnion.mpr ⟨i, (hleft i).symm ▸ hi⟩)
      | right i => exact Or.inr (mem_iUnion.mpr ⟨i, (hright i).symm ▸ hi⟩)
  · apply Subset.antisymm
    · rintro x ⟨hxU, hxV⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxV
      rw [hleft] at hi
      rw [hright] at hj
      have hxv : x ∈ range P := by
        by_contra hx
        have hiP : x ∈ P.edgeSet ℝ (e (i.castAdd (n + 1))) := by
          rwa [hpoly, P.edgeSet_reindex e he] at hi
        have hjP : x ∈ P.edgeSet ℝ (e (Fin.natAdd (m + 1) j)) := by
          rwa [hpoly, P.edgeSet_reindex e he] at hj
        have heq := e.injective (P.eq_of_mem_edgeSets_of_not_vertex hP hinj hx hiP hjP)
        have hval := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        have := i.isLt
        omega
      obtain ⟨k, hk⟩ := hrange.symm ▸ hxv
      have hxend (l : Fin ((m + 1) + (n + 1))) (hl : x ∈ Q.edgeSet ℝ l) :
          x ∈ (Q.edgeVertices l : Set E) := by
        have hkl := (Q.vertex_mem_edgeSet_iff hQ hQi k l).mp (hk.symm ▸ hl)
        simp only [edgeVertices, Finset.coe_pair, mem_insert_iff, mem_singleton_iff]
        rcases hkl with hkl | hkl
        · exact Or.inl (hk.symm.trans (congrArg Q hkl))
        · exact Or.inr (hk.symm.trans (congrArg Q hkl))
      have hxleft : x ∈ range p := by
        have hx := hxend _ hi
        rw [hleftEnd] at hx
        rcases hx with hx | hx
        · exact ⟨i.castSucc, hx.symm⟩
        · exact ⟨i.succ, hx.symm⟩
      have hxright : x ∈ range q := by
        have hx := hxend _ hj
        rw [hrightEnd] at hx
        rcases hx with hx | hx
        · exact ⟨j.castSucc, hx.symm⟩
        · exact ⟨j.succ, hx.symm⟩
      have hx : x ∈ ({u 0, v 0} : Set E) :=
        (range_split_inter u v hQi).subset ⟨hxleft, hxright⟩
      simpa only [hu0, hv0] using hx
    · intro x hx
      exact ⟨hU.1 hx, hV.1 hx⟩





theorem exists_arcs_at_marks (P : Polygon E (N + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {a b : E} (ha : a ∈ P.boundary ℝ) (hb : b ∈ P.boundary ℝ) (hab : a ≠ b) :
    ∃ U V : Set E, IsFinitePLBallPair ℝ U {a, b} ∧
      IsFinitePLBallPair ℝ V {a, b} ∧
      U ∪ V = P.boundary ℝ ∧ U ∩ V = {a, b} := by
  obtain ⟨M, Q, hQ, hQi, hboundary, ⟨i, hi⟩, ⟨j, hj⟩⟩ :=
    P.exists_subdivision_at_marks hP hinj ha hb
  have hij : i ≠ j := fun h => hab (hi.symm.trans ((congrArg Q h).trans hj))
  simpa only [hi, hj, hboundary] using Q.exists_arcs_at_vertices hQ hQi i j hij

end Polygon
