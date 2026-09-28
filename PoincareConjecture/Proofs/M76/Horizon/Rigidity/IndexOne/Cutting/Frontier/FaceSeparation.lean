import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Frontier.BoundaryPL
import Mathlib.Analysis.Convex.Topology










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem affine_closed_piece_boundary_or_endpoint
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {S : Set E} (hS : IsClosed S) (hconv : Convex ℝ S)
    {q : E → X} (hq : ContinuousOn q S) {B : Set X} (hB : IsClosed B)
    (l : E →ᴬ[ℝ] ℝ) {a b : ℝ} (hab : a < b)
    (hbound : ∀ x ∈ S, l x ∈ Icc a b)
    (hbetween : ∀ x ∈ S, l x ∈ Ioo a b → q x ∈ B) :
    MapsTo q S B ∨ (∀ x ∈ S, l x = a) ∨ (∀ x ∈ S, l x = b) := by
  by_cases hinterior : ∃ y ∈ S, l y ∈ Ioo a b
  · obtain ⟨y, hy, hly⟩ := hinterior
    left
    intro x hx
    have hseg : openSegment ℝ x y ⊆ S := hconv.openSegment_subset hx hy
    have hclosure : closure (openSegment ℝ x y) ⊆ S := closure_minimal hseg hS
    have hmap : MapsTo q (openSegment ℝ x y) B := by
      intro z hz
      apply hbetween z (hseg hz)
      have hlz : l z ∈ openSegment ℝ (l x) (l y) := by
        exact (image_openSegment ℝ l.toAffineMap x y).subset ⟨z, hz, rfl⟩
      have hly' : l y ∈ interior (Icc a b) := by simpa only [interior_Icc] using hly
      simpa only [interior_Icc] using
        (convex_Icc a b).openSegment_self_interior_subset_interior (hbound x hx) hly' hlz
    have hxclosure : x ∈ closure (openSegment ℝ x y) :=
      segment_subset_closure_openSegment (left_mem_segment ℝ x y)
    exact hB.closure_eq ▸ hmap.closure_of_continuousOn (hq.mono hclosure) hxclosure
  · right
    have hend (x : E) (hx : x ∈ S) : l x = a ∨ l x = b := by
      have h := hbound x hx
      by_contra! hn
      exact hinterior ⟨x, hx, lt_of_le_of_ne h.1 hn.1.symm, lt_of_le_of_ne h.2 hn.2⟩
    by_cases ha : ∀ x ∈ S, l x = a
    · exact Or.inl ha
    · right
      push Not at ha
      obtain ⟨x, hx, hxa⟩ := ha
      have hxb := (hend x hx).resolve_left hxa
      intro y hy
      rcases hend y hy with hya | hyb
      · have himage : Convex ℝ (l '' S) := hconv.affine_image l.toAffineMap
        have hm : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ l '' S :=
          himage ⟨y, hy, hya⟩ ⟨x, hx, hxb⟩ (by norm_num) (by norm_num) (by norm_num)
        obtain ⟨z, hz, hzm⟩ := hm
        exact False.elim (hinterior ⟨z, hz, by
          rw [hzm]; simp only [smul_eq_mul]; constructor <;> linarith⟩)
      · exact hyb

end PoincareConjecture.M76.HamiltonIntervalTorus
