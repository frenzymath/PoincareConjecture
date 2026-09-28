import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIncidence
import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalEdges

set_option autoImplicit false

open Set Filter AffineMap
open scoped Topology

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem eventually_cutArcs_at_edgeCut
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) (i : Fin (n + 3)) :
    ∀ᶠ x in 𝓝 (P.edgeCut t i),
      (x ∈ P.boundary ℝ ↔ x ∈ P.edgeSet ℝ i) ∧
      (x ∈ P.cutArc t i ↔
        x ∈ lineMap (P i) (P (finRotate (n + 3) i)) '' Icc (t i) 1) ∧
      (x ∈ P.cutArc t ((finRotate (n + 3)).symm i) ↔
        x ∈ lineMap (P i) (P (finRotate (n + 3) i)) '' Icc 0 (t i)) := by
  have hqi : P.edgeCut t i ∈ P.edgeSet ℝ i :=
    P.edgeCut_mem_edgeSet t ⟨(ht i).1.le, (ht i).2.le⟩
  have hqv := P.edgeCut_notMem_range hP hinj t (ht i)
  have hnext : finRotate (n + 3) i ≠ i := fun h =>
    P.edge_endpoints_ne_of_injective hinj i (congrArg P h.symm)
  have hprev : (finRotate (n + 3)).symm i ≠ i := by
    intro h
    apply hnext
    simpa only [Equiv.apply_symm_apply] using
      (congrArg (finRotate (n + 3)) h).symm
  have hqnext : P.edgeCut t i ∉ P.edgeSet ℝ (finRotate (n + 3) i) := fun h =>
    hnext (P.eq_of_mem_edgeSets_of_not_vertex hP hinj hqv h hqi)
  have hqprev : P.edgeCut t i ∉ P.edgeSet ℝ ((finRotate (n + 3)).symm i) := fun h =>
    hprev (P.eq_of_mem_edgeSets_of_not_vertex hP hinj hqv h hqi)
  filter_upwards [P.eventually_boundary_iff_single_edge hP hinj hqv hqi,
    (P.isClosed_edgeSet (finRotate (n + 3) i)).isOpen_compl.mem_nhds hqnext,
    (P.isClosed_edgeSet ((finRotate (n + 3)).symm i)).isOpen_compl.mem_nhds hqprev]
    with x hboundary hxnext hxprev
  refine ⟨hboundary, ?_, ?_⟩
  · constructor
    · rintro (hx | ⟨u, hu, hux⟩)
      · exact hx
      · exact False.elim (hxnext ⟨u, ⟨hu.1, hu.2.trans (ht _).2.le⟩, hux⟩)
    · exact Or.inl
  · simp only [cutArc, Equiv.apply_symm_apply, mem_union]
    constructor
    · rintro (⟨u, hu, hux⟩ | hx)
      · apply False.elim
        apply hxprev
        refine ⟨u, ⟨(ht _).1.le.trans hu.1, hu.2⟩, ?_⟩
        simpa only [Equiv.apply_symm_apply] using hux
      · exact hx
    · exact Or.inr

end Polygon
