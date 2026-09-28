import PoincareConjecture.Proofs.M76.Mathlib.OneSidedSimplexSlice
import PoincareConjecture.Proofs.M76.Mathlib.CrossingPointSigns











set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]




theorem exists_opposite_vertices_of_regular_zero (A : E →ᵃ[ℝ] ℝ) {s : Set E}
    (hreg : ∀ u ∈ s, A u ≠ 0) {x : E} (hx : x ∈ convexHull ℝ s) (hAx : A x = 0) :
    ∃ u ∈ s, ∃ v ∈ s, A u < 0 ∧ 0 < A v := by
  have hneg : ∃ u ∈ s, A u < 0 := by
    by_contra hn
    have hpos : ∀ u ∈ s, 0 < A u := fun u hu =>
      lt_of_le_of_ne (le_of_not_gt (fun h => hn ⟨u, hu, h⟩)) (hreg u hu).symm
    have hh : 0 < A x := convexHull_min hpos ((convex_Ioi (0 : ℝ)).affine_preimage A) hx
    exact (hAx ▸ hh).false
  have hpos : ∃ v ∈ s, 0 < A v := by
    by_contra hp
    have hneg : ∀ u ∈ s, A u < 0 := fun u hu =>
      lt_of_le_of_ne (le_of_not_gt (fun h => hp ⟨u, hu, h⟩)) (hreg u hu)
    have hh : A x < 0 := convexHull_min hneg ((convex_Iio (0 : ℝ)).affine_preimage A) hx
    exact (hAx ▸ hh).false
  obtain ⟨u, hu, hAu⟩ := hneg
  obtain ⟨v, hv, hAv⟩ := hpos
  exact ⟨u, hu, v, hv, hAu, hAv⟩




theorem convexHull_insert_pair_inter_zero (A : E →ᵃ[ℝ] ℝ) {u w v : E}
    (hu : A u < 0) (hw : A w < 0) (hv : 0 < A v) :
    convexHull ℝ (insert v ({u, w} : Set E)) ∩ {x | A x = 0} =
      segment ℝ (A.zeroCrossing u v) (A.zeroCrossing w v) := by
  classical
  have hs : ∀ z ∈ ({u, w} : Finset E), A z < 0 := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hu
    · exact Finset.mem_singleton.mp hz ▸ hw
  simpa only [Finset.coe_pair, Set.image_pair, convexHull_pair] using
    A.convexHull_insert_inter_zero {u, w} hs hv

private theorem exists_edges_of_two_negative (A : E →ᵃ[ℝ] ℝ) {u w v : E}
    (huw : u ≠ w) (hu : A u < 0) (hw : A w < 0) (hv : 0 < A v)
    {t : Finset E} (ht : (t : Set E) = insert v {u, w}) :
    ∃ (e f : Finset E) (he : A.StraddlesZero e) (hf : A.StraddlesZero f),
      e ⊆ t ∧ f ⊆ t ∧ e ≠ f ∧
        convexHull ℝ (t : Set E) ∩ {x | A x = 0} =
          segment ℝ (A.straddlingPoint e he) (A.straddlingPoint f hf) := by
  classical
  have he : A.StraddlesZero {u, v} := ⟨u, v, hu, hv, Finset.coe_pair⟩
  have hf : A.StraddlesZero {w, v} := ⟨w, v, hw, hv, Finset.coe_pair⟩
  refine ⟨{u, v}, {w, v}, he, hf, ?_, ?_, ?_, ?_⟩
  · intro z hz
    change z ∈ (t : Set E)
    rw [ht]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simp
    · exact Finset.mem_singleton.mp hz ▸ mem_insert v {u, w}
  · intro z hz
    change z ∈ (t : Set E)
    rw [ht]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simp
    · exact Finset.mem_singleton.mp hz ▸ mem_insert v {u, w}
  · intro heq
    have humem : u ∈ ({w, v} : Finset E) := heq ▸ Finset.mem_insert_self u {v}
    rcases Finset.mem_insert.mp humem with heq | heq
    · exact huw heq
    · have huv : u = v := Finset.mem_singleton.mp heq
      exact (huv ▸ hu).not_gt hv
  · rw [A.straddlingPoint_eq_zeroCrossing he hu hv Finset.coe_pair,
      A.straddlingPoint_eq_zeroCrossing hf hw hv Finset.coe_pair, ht]
    exact A.convexHull_insert_pair_inter_zero hu hw hv




theorem exists_straddling_edges_triangle (A : E →ᵃ[ℝ] ℝ) {t : Finset E}
    (ht : t.card = 3) (hreg : ∀ u ∈ t, A u ≠ 0)
    (hslice : (convexHull ℝ (t : Set E) ∩ {x | A x = 0}).Nonempty) :
    ∃ (e f : Finset E) (he : A.StraddlesZero e) (hf : A.StraddlesZero f),
      e ⊆ t ∧ f ⊆ t ∧ e ≠ f ∧
        convexHull ℝ (t : Set E) ∩ {x | A x = 0} =
          segment ℝ (A.straddlingPoint e he) (A.straddlingPoint f hf) := by
  classical
  obtain ⟨x, hx, hAx⟩ := hslice
  obtain ⟨u, hut, v, hvt, hu, hv⟩ := A.exists_opposite_vertices_of_regular_zero hreg hx hAx
  have huv : u ≠ v := fun h => (h ▸ hu).not_gt hv
  have hpair : ({u, v} : Finset E) ⊆ t :=
    Finset.insert_subset_iff.mpr ⟨hut, Finset.singleton_subset_iff.mpr hvt⟩
  have hd : (t \ {u, v}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hpair, ht, Finset.card_pair huv]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hd
  have hwt : w ∈ t \ {u, v} := hw ▸ Finset.mem_singleton_self w
  have htw : t = insert w {u, v} := by
    rw [← Finset.union_sdiff_of_subset hpair, hw, Finset.union_singleton]
  have huw : u ≠ w := fun h => (Finset.mem_sdiff.mp hwt).2
    (h ▸ Finset.mem_insert_self u {v})
  have hvw : v ≠ w := fun h => (Finset.mem_sdiff.mp hwt).2
    (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
  rcases lt_or_gt_of_ne (hreg w (Finset.mem_sdiff.mp hwt).1) with hwneg | hwpos
  · apply exists_edges_of_two_negative A huw hu hwneg hv
    rw [htw, Finset.coe_insert, Finset.coe_pair]
    ext z
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  · have htn : (t : Set E) = insert u {v, w} := by
      rw [htw, Finset.coe_insert, Finset.coe_pair]
      ext z
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    obtain ⟨e, f, he, hf, het, hft, hef, hslice⟩ := exists_edges_of_two_negative (-A)
      hvw (neg_neg_of_pos hv) (neg_neg_of_pos hwpos) (neg_pos.mpr hu) htn
    have heA := (A.straddlesZero_neg_iff e).mp he
    have hfA := (A.straddlesZero_neg_iff f).mp hf
    refine ⟨e, f, heA, hfA, het, hft, hef, ?_⟩
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero,
      A.straddlingPoint_neg heA he, A.straddlingPoint_neg hfA hf] using hslice

end AffineMap
