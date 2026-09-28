import PoincareConjecture.Proofs.M76.Mathlib.RegularUpperTriangleStrip
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSegmentCollar

set_option autoImplicit false

open Set Geometry PLStrip

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem triangle_upper_section_eq_edgeLevels (A : E →ᵃ[ℝ] ℝ) {v u w : E} {c : ℝ}
    (hv : c < A v) (hu : A u < c) (hw : A w < c) :
    convexHull ℝ (insert v ({u, w} : Set E)) ∩ {x | A x = c} =
      segment ℝ (A.edgeLevel v u c) (A.edgeLevel v w c) := by
  have h := (-A).triangle_section_eq_edgeLevels (neg_lt_neg hv) (neg_lt_neg hu) (neg_lt_neg hw)
  rw [A.edgeLevel_neg (ne_of_lt (hu.trans hv)), A.edgeLevel_neg (ne_of_lt (hw.trans hv))] at h
  convert h using 2
  ext x
  change A x = c ↔ -A x = -c
  exact neg_inj.symm

variable [FiniteDimensional ℝ E]

theorem exists_triangle_segment_collar (A : E →ᵃ[ℝ] ℝ) {v u w : E} {α β : ℝ}
    (hi : AffineIndependent ℝ ![v, u, w]) (hαβ : α < β)
    (hside : (A v < α ∧ β < A u ∧ β < A w) ∨
      (β < A v ∧ A u < α ∧ A w < α)) :
    (convexHull ℝ (insert v ({u, w} : Set E)) ∩ {x | A x = α} =
      segment ℝ (A.edgeLevel v u α) (A.edgeLevel v w α)) ∧
    ∃ H : (segment ℝ (A.edgeLevel v u α) (A.edgeLevel v w α) ×ˢ Icc α β : Set (E × ℝ)) ≃ₜ
        (convexHull ℝ (insert v ({u, w} : Set E)) ∩ {x | A x ∈ Icc α β} : Set E),
      H.IsFinitePL ∧
      (∀ p, A (H p) = (p : E × ℝ).2) ∧
      (∀ (x : E) (hx : x ∈ segment ℝ (A.edgeLevel v u α) (A.edgeLevel v w α)),
        (H ⟨(x, α), ⟨hx, ⟨le_rfl, hαβ.le⟩⟩⟩ : E) = x) ∧
      ∀ (t : ℝ) (ht : t ∈ Icc α β),
        (H ⟨(A.edgeLevel v u α, t),
          ⟨left_mem_segment ℝ _ _, ht⟩⟩ : E) = A.edgeLevel v u t ∧
        (H ⟨(A.edgeLevel v w α, t),
          ⟨right_mem_segment ℝ _ _, ht⟩⟩ : E) = A.edgeLevel v w t := by
  have hav : α ≠ A v := by
    rcases hside with h | h
    · exact h.1.ne'
    · exact (hαβ.trans h.1).ne
  have huv : A u ≠ A v := by
    rcases hside with h | h
    · exact (h.1.trans (hαβ.trans h.2.1)).ne'
    · exact (h.2.1.trans (hαβ.trans h.1)).ne
  have hlr : A.edgeLevel v u α ≠ A.edgeLevel v w α := by
    intro h
    apply A.heightRay_ne_of_affineIndependent hi huv
    exact smul_right_injective E (sub_ne_zero.mpr hav) (add_right_cancel h)
  rcases hside with ⟨hv, hu, hw⟩ | ⟨hv, hu, hw⟩
  · refine ⟨A.triangle_section_eq_edgeLevels hv (hαβ.trans hu) (hαβ.trans hw), ?_⟩
    obtain ⟨e, he, _, hheight, hsides, hends⟩ := A.exists_lower_triangle_strip hi hv hαβ hu hw
    exact he.exists_segment_collar A hlr hαβ (A.edgeLevel v u) (A.edgeLevel v w)
      hheight (fun s hs => (hends s hs).1) hsides
  · refine ⟨A.triangle_upper_section_eq_edgeLevels (hαβ.trans hv) hu hw, ?_⟩
    obtain ⟨e, he, hheight, hsides, hends⟩ := A.exists_upper_triangle_strip hi hv hαβ hu hw
    exact he.exists_segment_collar A hlr hαβ (A.edgeLevel v u) (A.edgeLevel v w)
      hheight (fun s hs => (hends s hs).1) hsides

end AffineMap
