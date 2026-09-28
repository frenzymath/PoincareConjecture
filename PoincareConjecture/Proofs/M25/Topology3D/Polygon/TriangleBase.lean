import PoincareConjecture.Proofs.M25.Topology3D.Polygon.BoundaryBasics
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Affine.AddTorsorBases













set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]


def affineBasisTriangle (b : AffineBasis (Fin 3) ℝ E) : Polygon E 3 :=
  ⟨b⟩

end Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem affineBasisTriangle_boundary_eq_frontier (b : AffineBasis (Fin 3) ℝ E) :
    (affineBasisTriangle b).boundary ℝ = frontier (convexHull ℝ (range b)) := by
  have hclosed := ((finite_range b).isCompact_convexHull ℝ).isClosed
  rw [hclosed.frontier_eq]
  apply subset_antisymm
  · intro x hx
    refine ⟨polygon_boundary_subset_convexHull (affineBasisTriangle b) hx, ?_⟩
    intro hint
    rw [b.interior_convexHull] at hint
    obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff (affineBasisTriangle b) x).mp hx
    obtain ⟨t, _, rfl⟩ := hi
    have hzero : b.coord (finRotate 3 (finRotate 3 i))
        ((affineBasisTriangle b).edgePath ℝ i t) = 0 := by
      change b.coord _ (AffineMap.lineMap (b i) (b (finRotate 3 i)) t) = 0
      rw [AffineMap.apply_lineMap]
      fin_cases i <;> simp
    exact (hint _).ne' hzero
  · intro x hx
    have hnonneg : ∀ i, 0 ≤ b.coord i x := by
      simpa only [b.convexHull_eq_nonneg_coord, mem_ofPred_eq] using hx.1
    have hnot : ¬∀ i, 0 < b.coord i x := by
      simpa only [b.interior_convexHull, mem_ofPred_eq] using hx.2
    push Not at hnot
    obtain ⟨k, hk⟩ := hnot
    have hkzero : b.coord k x = 0 := le_antisymm hk (hnonneg k)
    have hsum := b.sum_coord_apply_eq_one x
    have hrepr := b.linear_combination_coord_eq_self x
    simp only [Fin.sum_univ_three] at hsum hrepr
    fin_cases k
    · change b.coord 0 x = 0 at hkzero
      apply polygon_edgeSet_subset_boundary (affineBasisTriangle b) 1
      rw [polygon_edgeSet_eq_segment]
      change x ∈ segment ℝ (b 1) (b 2)
      refine ⟨b.coord 1 x, b.coord 2 x, hnonneg 1, hnonneg 2, ?_, ?_⟩
      · simpa only [hkzero, zero_add] using hsum
      · simpa only [hkzero, zero_smul, zero_add] using hrepr
    · change b.coord 1 x = 0 at hkzero
      apply polygon_edgeSet_subset_boundary (affineBasisTriangle b) 2
      rw [polygon_edgeSet_eq_segment]
      change x ∈ segment ℝ (b 2) (b 0)
      refine ⟨b.coord 2 x, b.coord 0 x, hnonneg 2, hnonneg 0, ?_, ?_⟩
      · simpa [hkzero, add_comm] using hsum
      · simpa [hkzero, add_comm] using hrepr
    · change b.coord 2 x = 0 at hkzero
      apply polygon_edgeSet_subset_boundary (affineBasisTriangle b) 0
      rw [polygon_edgeSet_eq_segment]
      change x ∈ segment ℝ (b 0) (b 1)
      refine ⟨b.coord 0 x, b.coord 1 x, hnonneg 0, hnonneg 1, ?_, ?_⟩
      · simpa only [hkzero, add_zero] using hsum
      · simpa only [hkzero, zero_smul, add_zero] using hrepr



theorem affineBasisTriangle_homeomorph (b : AffineBasis (Fin 3) ℝ E) :
    ∃ h : E ≃ₜ E, h '' interior (convexHull ℝ (range b)) = ball 0 1 ∧
      h '' convexHull ℝ (range b) = closedBall 0 1 ∧
      h '' (affineBasisTriangle b).boundary ℝ = sphere 0 1 := by
  have hcompact := (finite_range b).isCompact_convexHull ℝ
  obtain ⟨h, hint, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_convexHull ℝ _) ⟨_, b.centroid_mem_interior_convexHull⟩ hcompact.isBounded
  refine ⟨h, hint, ?_, ?_⟩
  · simpa only [hcompact.isClosed.closure_eq] using hclosure
  · rwa [affineBasisTriangle_boundary_eq_frontier]

end PoincareConjecture.M25.Topology3D
