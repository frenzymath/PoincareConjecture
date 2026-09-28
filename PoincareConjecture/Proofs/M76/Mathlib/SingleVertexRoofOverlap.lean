import PoincareConjecture.Proofs.M76.Mathlib.SingleVertexSlabCommonEdge
import PoincareConjecture.Proofs.M76.Mathlib.SingleVertexSourceRoof

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_crossing_of_singleVertex_section_overlap (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hAq : A q = 0) {β : ℝ} (hβ : 0 ≤ β)
    (hreg : ∀ z ∈ K.vertices, A z ∈ Icc 0 β → z = q)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hsc : s.card = 3) (htc : t.card = 3) (hst : s ≠ t) (hqs : q ∈ s)
    {w : E} (hw : w ∈ convexHull ℝ ((s : Set E) \ {q})) (hAw : A w = 0)
    {x : E} (hxs : x ∈ convexHull ℝ (s : Set E))
    (hxt : x ∈ convexHull ℝ (t : Set E)) (hAx : A x = 0) (hxq : x ≠ q) : x = w := by
  classical
  have hxA : A x ∈ Icc 0 β := by rw [hAx]; exact ⟨le_rfl, hβ⟩
  obtain ⟨e, he, _, hes, _, hxe, hAe⟩ :=
    K.common_edge_of_singleVertexSlab_intersection A hreg hs ht hsc htc hst hxs hxt hxA hxq
  have hqe : q ∉ e := fun h => hxq (hAe hxe (subset_convexHull ℝ (e : Set E) h)
    (hAx.trans hAq.symm))
  have heq : e = s.erase q := Finset.eq_of_subset_of_card_le
    (fun z hz => Finset.mem_erase.mpr ⟨fun h => hqe (h ▸ hz), hes hz⟩)
    (by rw [Finset.card_erase_of_mem hqs, hsc, he])
  have hwe : w ∈ convexHull ℝ (e : Set E) := by
    rw [heq, Finset.coe_erase]
    exact hw
  exact hAe hxe hwe (hAx.trans hAw.symm)

theorem singleVertex_roof_value_at_overlap [DecidableEq E] (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    {β : ℝ} (hβ : 0 ≤ β) (hreg : ∀ z ∈ K.vertices, A z ∈ Icc 0 β → z = q)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hsc : s.card = 3) (htc : t.card = 3) (hst : s ≠ t)
    (a : E →ᴬ[ℝ] ℝ)
    (hroof : (q ∉ s ∧ a = ContinuousAffineMap.const ℝ E β) ∨
      ∃ w : E, q ∈ s ∧ q ≠ w ∧ w ∈ convexHull ℝ ((s : Set E) \ {q}) ∧
        (convexHull ℝ (s : Set E) ∩ {x | A x = 0} = segment ℝ q w) ∧
        a q = 0 ∧ a w = β)
    {x : E} (hxs : x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0})
    (hxt : x ∈ convexHull ℝ (t : Set E) ∩ {x | A x = 0}) :
    a x = if x = q then 0 else β := by
  classical
  by_cases hxq : x = q
  · rw [if_pos hxq, hxq]
    rcases hroof with ⟨hqs, _⟩ | ⟨_, _, _, _, _, haq, _⟩
    · exact (hqs ((K.vertex_mem_convexHull_iff hqK hs).mp (hxq ▸ hxs.1))).elim
    · exact haq
  · rw [if_neg hxq]
    rcases hroof with ⟨_, rfl⟩ | ⟨w, hqs, _, hw, hsec, _, haw⟩
    · rfl
    · have hwA : A w = 0 := (show w ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0} from
        hsec.symm ▸ right_mem_segment ℝ q w).2
      have hxw := K.eq_crossing_of_singleVertex_section_overlap A hAq hβ hreg hs ht
        hsc htc hst hqs hw hwA hxs.1 hxt.1 hxs.2 hxq
      rw [hxw, haw]

end Geometry.SimplicialComplex
