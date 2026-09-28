import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCornerHeightChart
import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalSegments










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}





theorem exists_local_height_chart_of_both_signs
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hq : q ∈ P.boundary ℝ) (hAq : A q = 0)
    (hpos : q ∈ closure (P.boundary ℝ ∩ {x | 0 < A x}))
    (hneg : q ∈ closure (P.boundary ℝ ∩ {x | A x < 0})) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
      ∃ N : Set E, N ⊆ P.boundary ℝ ∧
        ∃ d : Icc a b ≃ₜ N, d.IsFinitePL ∧
          (∀ t, A (d t) = (t : ℝ)) ∧
          (∀ hzero : (0 : ℝ) ∈ Icc a b, (d ⟨0, hzero⟩ : E) = q) ∧
          ∀ᶠ x in 𝓝 q, x ∈ P.boundary ℝ ↔ x ∈ N := by
  obtain ⟨u, v, _, _, _, hpair, hlocal⟩ := P.exists_local_segment_pair hP hinj hq
  have hneighbor (B : E →ᵃ[ℝ] ℝ) (hBq : B q = 0)
      (hBpos : q ∈ closure (P.boundary ℝ ∩ {x | 0 < B x})) :
      0 < B u ∨ 0 < B v := by
    by_contra h
    have hu : B u ≤ 0 := le_of_not_gt (fun hu => h (Or.inl hu))
    have hv : B v ≤ 0 := le_of_not_gt (fun hv => h (Or.inr hv))
    have hhalf : Convex ℝ {x : E | B x ≤ 0} := (convex_Iic (0 : ℝ)).affine_preimage B
    obtain ⟨x, hx, hnear⟩ :=
      ((mem_closure_iff_frequently.mp hBpos).and_eventually hlocal).exists
    have hnonpos : B x ≤ 0 := by
      rcases hnear.mp hx.1 with hxu | hxv
      · exact hhalf.segment_subset hBq.le hu hxu
      · exact hhalf.segment_subset hBq.le hv hxv
    exact hx.2.not_ge hnonpos
  have hp := hneighbor A hAq hpos
  have hn : A u < 0 ∨ A v < 0 := by
    have hneg' : q ∈ closure (P.boundary ℝ ∩ {x | 0 < (-A) x}) := by
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hneg
    have hq' : (-A) q = 0 := by simp only [AffineMap.coe_neg, Pi.neg_apply, hAq, neg_zero]
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hneighbor (-A) hq' hneg'
  have hsigns : (A u < 0 ∧ 0 < A v) ∨ (A v < 0 ∧ 0 < A u) := by
    rcases hp with hp | hp <;> rcases hn with hn | hn
    · exact (hp.not_gt hn).elim
    · exact Or.inr ⟨hn, hp⟩
    · exact Or.inl ⟨hn, hp⟩
    · exact (hp.not_gt hn).elim
  obtain ⟨u', v', hu', hv', hsub, hnear⟩ :
      ∃ u' v' : E, A u' < 0 ∧ 0 < A v' ∧
        segment ℝ u' q ∪ segment ℝ q v' ⊆ P.boundary ℝ ∧
        ∀ᶠ x in 𝓝 q, x ∈ P.boundary ℝ ↔ x ∈ segment ℝ u' q ∪ segment ℝ q v' := by
    rcases hsigns with h | h
    · refine ⟨u, v, h.1, h.2, ?_, ?_⟩
      · rw [segment_symm ℝ u q]
        exact hpair
      · rw [segment_symm ℝ u q]
        exact hlocal
    · refine ⟨v, u, h.1, h.2, ?_, ?_⟩
      · rw [segment_symm ℝ v q, union_comm]
        exact hpair
      · rw [segment_symm ℝ v q, union_comm]
        exact hlocal
  obtain ⟨d, hd, hdA, _, hdq, _⟩ := A.exists_finitePL_corner_height_chart hu' hAq hv'
  exact ⟨A u', A v', hu', hv', _, hsub, d, hd, hdA, fun _ => hdq, hnear⟩

end Polygon
