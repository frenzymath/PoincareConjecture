import PoincareConjecture.Proofs.M76.PrimeReduction.PathVertexIncidence
import PoincareConjecture.Proofs.M76.PrimeReduction.JoinedPathIntersections
import PoincareConjecture.Proofs.M76.PrimeReduction.MidpointClosingPath
import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningArcNesting

set_option autoImplicit false

open Set

namespace Polygon

local notation "V" => (ℝ × ℝ)
local notation "Z" => (Set.preimage (Prod.snd : (ℝ × ℝ) → ℝ) ({0} : Set ℝ))

theorem exists_polygon_of_returning_path {n : ℕ} (p : Fin (n + 2) → V)
    (hp : Function.Injective p)
    (hinter : ∀ i j : Fin (n + 1),
      segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆
        convexHull ℝ (({p i.castSucc, p i.succ} : Set V) ∩ {p j.castSucc, p j.succ}))
    (haxis : pathCarrier p ∩ Z = {p 0, p (Fin.last (n + 1))})
    (hup : ∀ i, 0 ≤ (p i).2) :
    ∃ P : Polygon V (n + 3), P.HasSimplicialEdges ∧ Function.Injective P ∧
      (∀ i, 0 ≤ (P i).2) ∧
      P.boundary ℝ = pathCarrier p ∪ segment ℝ (p 0) (p (Fin.last (n + 1))) := by
  have hab : p 0 ≠ p (Fin.last (n + 1)) := by
    intro h
    have hv := congrArg Fin.val (hp h)
    change 0 = n + 1 at hv
    omega
  have haZ : p 0 ∈ Z := (haxis.symm.subset (Or.inl rfl)).2
  have hbZ : p (Fin.last (n + 1)) ∈ Z := (haxis.symm.subset (Or.inr rfl)).2
  obtain ⟨q, hq, hq0, hq2, hqc, hqi⟩ :=
    exists_midpoint_segment_path (p (Fin.last (n + 1))) (p 0) hab.symm
  have hqZ : pathCarrier q ⊆ Z := by
    rw [hqc]
    exact segment_subset_returning_axis hbZ haZ
  have hmix (i : Fin (n + 1)) (j : Fin 2) :
      segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (q j.castSucc) (q j.succ) ⊆
        convexHull ℝ (({p i.castSucc, p i.succ} : Set V) ∩ {q j.castSucc, q j.succ}) := by
    intro x hx
    have hends := haxis.subset
      ⟨mem_iUnion.mpr ⟨i, hx.1⟩, hqZ (mem_iUnion.mpr ⟨j, hx.2⟩)⟩
    apply subset_convexHull ℝ _
    constructor
    · rcases hends with rfl | rfl
      · exact (path_vertex_mem_segment_iff p hp hinter 0 i).mp hx.1
      · exact (path_vertex_mem_segment_iff p hp hinter (Fin.last (n + 1)) i).mp hx.1
    · rcases hends with rfl | rfl
      · have he := path_vertex_mem_segment_iff q hq hqi 2 j
        rw [hq2] at he
        exact he.mp hx.2
      · have he := path_vertex_mem_segment_iff q hq hqi 0 j
        rw [hq0] at he
        exact he.mp hx.2
  let P : Polygon V (n + 3) := ofPaths (m := n + 1) (n := 2) p q
  have hP : P.HasSimplicialEdges :=
    hasSimplicialEdges_ofPaths_of_intersections p q hq0.symm hq2 hinter hqi hmix
  have hrange : range p ∩ range q ⊆ {p 0, q 0} := by
    rintro x ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
    have hqmem : p i ∈ pathCarrier q := hj ▸ vertex_mem_pathCarrier q j
    have hends := haxis.subset ⟨vertex_mem_pathCarrier p i, hqZ hqmem⟩
    exact hends.elim Or.inl (fun h => Or.inr (h.trans hq0.symm))
  have hPi : Function.Injective P := injective_ofPaths p q hp hq hq0.symm hq2 hrange
  have hboundary : P.boundary ℝ = pathCarrier p ∪
      segment ℝ (p 0) (p (Fin.last (n + 1))) := by
    rw [boundary_ofPaths p q hq0.symm hq2, hqc, segment_symm]
  have hhalf : Convex ℝ {x : V | 0 ≤ x.2} := by
    intro x hx y hy a b ha hb _
    change 0 ≤ a * x.2 + b * y.2
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hpathup : pathCarrier p ⊆ {x : V | 0 ≤ x.2} := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hhalf.segment_subset (hup i.castSucc) (hup i.succ) hi
  refine ⟨P, hP, hPi, ?_, hboundary⟩
  intro i
  rcases hboundary.subset (P.vertex_mem_boundary i) with hi | hi
  · exact hpathup hi
  · exact hhalf.segment_subset (hup 0) (hup (Fin.last (n + 1))) hi

end Polygon
