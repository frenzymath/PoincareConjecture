import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.RegularTriangleIntersection
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineEdgeSlab

/-!
# Common edges of triangle strips throughout a regular slab

Translate height to the actual common point's level. The
regular triangle-intersection theorem supplies its original
crossing edge, on which height is injective. See Alexander
1924, pp. 6--8 and M76 derivation 164.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Distinct triangle carriers meeting in a vertex-free slab
share an original edge containing their common point. Height
is injective on the whole edge hull. See M76 derivation 164. -/
theorem common_edge_of_regularSlab_intersection (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {α β : ℝ} (hreg : ∀ z ∈ K.vertices, A z < α ∨ β < A z)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hsc : s.card = 3) (htc : t.card = 3) (hne : s ≠ t) {x : E}
    (hxs : x ∈ convexHull ℝ (s : Set E)) (hxt : x ∈ convexHull ℝ (t : Set E))
    (hxA : A x ∈ Icc α β) :
    ∃ e : Finset E, e.card = 2 ∧ e ⊆ s ∧ e ⊆ t ∧
      x ∈ convexHull ℝ (e : Set E) ∧ InjOn A (convexHull ℝ (e : Set E)) := by
  let B : E →ᵃ[ℝ] ℝ := A - AffineMap.const ℝ E (A x)
  have hBreg : ∀ z ∈ K.vertices, B z ≠ 0 := by
    intro z hz
    change A z - A x ≠ 0
    rcases hreg z hz with h | h
    · exact (sub_neg.mpr (h.trans_le hxA.1)).ne
    · exact (sub_pos.mpr (hxA.2.trans_lt h)).ne'
  obtain ⟨e, he, _, hes, het, heq⟩ := K.common_straddling_edge_of_triangle_intersection B hBreg
    hs ht hsc htc hne hxs hxt (sub_self (A x))
  have hmem : x ∈ convexHull ℝ (e : Set E) := heq ▸ (B.straddlingPoint_mem e he).1
  refine ⟨e, AffineMap.StraddlesZero.card B he, hes, het, hmem, ?_⟩
  obtain ⟨u, v, hu, hv, he⟩ := he
  have huv : A v ≠ A u := by
    change A u - A x < 0 at hu
    change 0 < A v - A x at hv
    exact ne_of_gt (by linarith)
  rw [he]
  exact (A.injOn_edgeLine huv).mono (convexHull_subset_affineSpan _)

end Geometry.SimplicialComplex
