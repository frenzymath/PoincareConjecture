import PoincareConjecture.Proofs.M76.Mathlib.RegularTriangleSegmentCollar
import PoincareConjecture.Proofs.M76.Mathlib.RegularSlabTriangleLabels
import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeSlab
import PoincareConjecture.Proofs.M76.Mathlib.HeightPreservingEdgeIncidence










set_option autoImplicit false

open Set Geometry PLStrip

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]




theorem exists_triangle_segment_edge_collar (A : E →ᵃ[ℝ] ℝ) {v u w : E} {α β : ℝ}
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
      ∀ (e : Finset E), e.card = 2 → e ⊆ {v, u, w} →
        ∀ p : (segment ℝ (A.edgeLevel v u α) (A.edgeLevel v w α) ×ˢ Icc α β : Set (E × ℝ)),
          (p : E × ℝ).1 ∈ convexHull ℝ (e : Set E) ↔ (H p : E) ∈ convexHull ℝ (e : Set E) := by
  obtain ⟨hsection, H, hH, hheight, hbase, hpaths⟩ :=
    A.exists_triangle_segment_collar hi hαβ hside
  have hbetween (z : E) (hz : z = u ∨ z = w) (t : ℝ) (ht : t ∈ Icc α β) :
      (A v < t ∧ t < A z) ∨ (A z < t ∧ t < A v) := by
    rcases hside with h | h <;> rcases hz with rfl | rfl
    · exact Or.inl ⟨h.1.trans_le ht.1, ht.2.trans_lt h.2.1⟩
    · exact Or.inl ⟨h.1.trans_le ht.1, ht.2.trans_lt h.2.2⟩
    · exact Or.inr ⟨h.2.1.trans_le ht.1, ht.2.trans_lt h.1⟩
    · exact Or.inr ⟨h.2.2.trans_le ht.1, ht.2.trans_lt h.1⟩
  have hne (z : E) (hz : z = u ∨ z = w) : A z ≠ A v := by
    rcases hbetween z hz α ⟨le_rfl, hαβ.le⟩ with h | h
    · exact (h.1.trans h.2).ne'
    · exact (h.1.trans h.2).ne
  have hmem (z : E) (hz : z = u ∨ z = w) (t : ℝ) (ht : t ∈ Icc α β) :
      A.edgeLevel v z t ∈ convexHull ℝ ({v, z} : Set E) := by
    rw [convexHull_pair]
    exact A.edgeLevel_mem_segment (hbetween z hz t ht)
  have hconst (x : E) (hx : x ∈ segment ℝ (A.edgeLevel v u α) (A.edgeLevel v w α)) :
      A x = α := by
    have hx' : x ∈ convexHull ℝ (insert v ({u, w} : Set E)) ∩ {x | A x = α} :=
      hsection.symm ▸ hx
    exact hx'.2
  have hleft (p : (segment ℝ (A.edgeLevel v u α) (A.edgeLevel v w α) ×ˢ Icc α β : Set (E × ℝ))) :
      (p : E × ℝ).1 ∈ convexHull ℝ ({v, u} : Set E) ↔
      (H p : E) ∈ convexHull ℝ ({v, u} : Set E) := by
    apply H.edge_membership_iff A hconst hheight
      ((A.injOn_edgeLine (hne u (Or.inl rfl))).mono (convexHull_subset_affineSpan _))
      (left_mem_segment ℝ _ _) (hmem u (Or.inl rfl) α ⟨le_rfl, hαβ.le⟩)
    intro t ht
    rw [(hpaths t ht).1]
    exact hmem u (Or.inl rfl) t ht
  have hright (p : (segment ℝ (A.edgeLevel v u α) (A.edgeLevel v w α) ×ˢ Icc α β : Set (E × ℝ))) :
      (p : E × ℝ).1 ∈ convexHull ℝ ({v, w} : Set E) ↔
      (H p : E) ∈ convexHull ℝ ({v, w} : Set E) := by
    apply H.edge_membership_iff A hconst hheight
      ((A.injOn_edgeLine (hne w (Or.inr rfl))).mono (convexHull_subset_affineSpan _))
      (right_mem_segment ℝ _ _) (hmem w (Or.inr rfl) α ⟨le_rfl, hαβ.le⟩)
    intro t ht
    rw [(hpaths t ht).2]
    exact hmem w (Or.inr rfl) t ht
  have hmiss : Disjoint (convexHull ℝ ({u, w} : Set E)) {x | A x ∈ Icc α β} := by
    apply disjoint_left.mpr
    intro x hx hAx
    rcases hside with h | h
    · have hstrict : β < A x := convexHull_min
        (by
          rintro z (rfl | rfl)
          · exact h.2.1
          · exact h.2.2)
        ((convex_Ioi β).affine_preimage A) hx
      exact (not_lt_of_ge hAx.2) hstrict
    · have hstrict : A x < α := convexHull_min
        (by
          rintro z (rfl | rfl)
          · exact h.2.1
          · exact h.2.2)
        ((convex_Iio α).affine_preimage A) hx
      exact (not_lt_of_ge hAx.1) hstrict
  refine ⟨hsection, H, hH, hheight, hbase, ?_⟩
  intro e he hes p
  rcases Finset.eq_pair_of_subset_triple he hes with rfl | rfl | rfl
  · simpa only [Finset.coe_pair] using hleft p
  · simpa only [Finset.coe_pair] using hright p
  · simp only [Finset.coe_pair]
    have hsrc : (p : E × ℝ).1 ∉ convexHull ℝ ({u, w} : Set E) := by
      intro hx
      apply disjoint_left.mp hmiss hx
      change A (p : E × ℝ).1 ∈ Icc α β
      rw [hconst _ p.property.1]
      exact ⟨le_rfl, hαβ.le⟩
    exact iff_of_false hsrc (fun hx => disjoint_left.mp hmiss hx (H p).property.2)

end AffineMap
