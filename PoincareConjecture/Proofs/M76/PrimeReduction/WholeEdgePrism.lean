import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import Mathlib.Topology.Order.Compact









set_option autoImplicit false

open Set

namespace PoincareConjecture.M76


def originalEdgePrism (l u r : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  (Icc (-r) r ×ˢ Icc (-r) r) ×ˢ Icc l u

private theorem exists_axis_prism_in_open {l u : ℝ}
    {U : Set ((ℝ × ℝ) × ℝ)} (hU : IsOpen U)
    (haxis : ∀ t ∈ Icc l u, ((0, 0), t) ∈ U) :
    ∃ r ∈ Ioo (0 : ℝ) 1, originalEdgePrism l u r ⊆ U := by
  let C := originalEdgePrism l u 1
  let B := C \ U
  have hC : IsCompact C := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hB : IsCompact B := hC.inter_right hU.isClosed_compl
  let w (z : (ℝ × ℝ) × ℝ) : ℝ := max |z.1.1| |z.1.2|
  have hw : Continuous w :=
    (continuous_fst.fst.abs).max continuous_fst.snd.abs
  have hpos (z : (ℝ × ℝ) × ℝ) (hz : z ∈ B) : 0 < w z := by
    by_contra hn
    have hzle : max |z.1.1| |z.1.2| ≤ 0 := le_of_not_gt hn
    have hx : z.1.1 = 0 := abs_nonpos_iff.mp ((le_max_left _ _).trans hzle)
    have hy : z.1.2 = 0 := abs_nonpos_iff.mp ((le_max_right _ _).trans hzle)
    have he : z = ((0, 0), z.2) := Prod.ext (Prod.ext hx hy) rfl
    apply hz.2
    rw [he]
    exact haxis z.2 hz.1.2
  obtain ⟨m, hm, hbound⟩ := hB.exists_forall_le' hw.continuousOn hpos
  obtain ⟨r, hr, hrsmall⟩ := exists_between (lt_min zero_lt_one hm)
  have hr1 : r < 1 := hrsmall.trans_le (min_le_left _ _)
  have hrm : r < m := hrsmall.trans_le (min_le_right _ _)
  have hinterval : Icc (-r) r ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨(neg_le_neg hr1.le).trans hx.1, hx.2.trans hr1.le⟩
  refine ⟨r, ⟨hr, hr1⟩, ?_⟩
  intro z hz
  have hzC : z ∈ C := ⟨⟨hinterval hz.1.1, hinterval hz.1.2⟩, hz.2⟩
  have hwr : w z ≤ r := max_le (abs_le.mpr hz.1.1) (abs_le.mpr hz.1.2)
  by_contra hnot
  exact (not_le_of_gt hrm) ((hbound z ⟨hzC, hnot⟩).trans hwr)





theorem exists_whole_original_edge_prism
    {S U : Set ((ℝ × ℝ) × ℝ)} (hS : IsClosed S) (hU : IsOpen U)
    (hzero : ((0, 0), (0 : ℝ)) ∉ S) (hone : ((0, 0), (1 : ℝ)) ∉ S)
    (haxis : ∀ t ∈ Ioo (0 : ℝ) 1, ((0, 0), t) ∈ U) :
    ∃ l u r : ℝ, 0 < l ∧ l < u ∧ u < 1 ∧ r ∈ Ioo (0 : ℝ) 1 ∧
      originalEdgePrism l u r ⊆ U ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ((0, 0), t) ∈ S → t ∈ Ioo l u) ∧
      Disjoint (originalEdgePrism l u r ∩ {z | z.2 = l ∨ z.2 = u}) S ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ((0, 0), t) ∈ S →
        ((0, 0), t) ∈ interior (originalEdgePrism l u r)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        ((0, 0), t) ∈ frontier (originalEdgePrism l u r) ↔ t = l ∨ t = u := by
  have hc : Continuous (fun t : ℝ => (((0 : ℝ), (0 : ℝ)), t)) :=
    continuous_const.prodMk continuous_id
  have hO : IsOpen ((fun t : ℝ => (((0 : ℝ), (0 : ℝ)), t)) ⁻¹' Sᶜ) :=
    hS.isOpen_compl.preimage hc
  obtain ⟨d0, hd0, hball0⟩ := Metric.isOpen_iff.mp hO 0 hzero
  obtain ⟨d1, hd1, hball1⟩ := Metric.isOpen_iff.mp hO 1 hone
  obtain ⟨l, hl, hlsmall⟩ :=
    exists_between (lt_min (by norm_num : (0 : ℝ) < 1 / 4) (lt_min hd0 hd1))
  have hlq : l < 1 / 4 := hlsmall.trans_le (min_le_left _ _)
  have hld0 : l < d0 :=
    hlsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hld1 : l < d1 :=
    hlsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let u : ℝ := 1 - l
  have hlu : l < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hl1 : l < 1 := hlq.trans (by norm_num)
  have hu0 : 0 < u := hl.trans hlu
  have hcontacts (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (htS : ((0, 0), t) ∈ S) : t ∈ Ioo l u := by
    constructor
    · by_contra hn
      have htball : t ∈ Metric.ball 0 d0 := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
        exact (le_of_not_gt hn).trans_lt hld0
      exact hball0 htball htS
    · by_contra hn
      have htball : t ∈ Metric.ball 1 d1 := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)]
        have htge : u ≤ t := le_of_not_gt hn
        dsimp [u] at htge
        linarith
      exact hball1 htball htS
  have hlS : ((0, 0), l) ∉ S :=
    fun h => (lt_irrefl l) (hcontacts l ⟨hl.le, hl1.le⟩ h).1
  have huS : ((0, 0), u) ∉ S :=
    fun h => (lt_irrefl u) (hcontacts u ⟨hu0.le, hu1.le⟩ h).2
  let W := U \ (S ∩ {z : (ℝ × ℝ) × ℝ | z.2 = l ∨ z.2 = u})
  have hbad : IsClosed (S ∩ {z : (ℝ × ℝ) × ℝ | z.2 = l ∨ z.2 = u}) :=
    hS.inter ((isClosed_eq continuous_snd continuous_const).union
      (isClosed_eq continuous_snd continuous_const))
  have hW : IsOpen W := hU.sdiff hbad
  have hcore (t : ℝ) (ht : t ∈ Icc l u) : ((0, 0), t) ∈ W := by
    refine ⟨haxis t ⟨hl.trans_le ht.1, ht.2.trans_lt hu1⟩, ?_⟩
    rintro ⟨htS, ht | ht⟩
    · exact hlS (ht ▸ htS)
    · exact huS (ht ▸ htS)
  obtain ⟨r, hr, hJW⟩ := exists_axis_prism_in_open hW hcore
  have hJclosed : IsClosed (originalEdgePrism l u r) :=
    (isClosed_Icc.prod isClosed_Icc).prod isClosed_Icc
  have hinterior (t : ℝ) :
      ((0, 0), t) ∈ interior (originalEdgePrism l u r) ↔ t ∈ Ioo l u := by
    simp only [originalEdgePrism, interior_prod_eq, interior_Icc, mem_prod,
      mem_Ioo, neg_lt_zero, hr.1, and_self, true_and]
  have hmem (t : ℝ) :
      ((0, 0), t) ∈ originalEdgePrism l u r ↔ t ∈ Icc l u := by
    simp only [originalEdgePrism, mem_prod, mem_Icc, neg_nonpos.mpr hr.1.le, hr.1.le,
      and_self, true_and]
  refine ⟨l, u, r, hl, hlu, hu1, hr, fun z hz => (hJW hz).1,
    hcontacts, ?_, ?_, ?_⟩
  · exact disjoint_left.mpr fun z hz hzS => (hJW hz.1).2 ⟨hzS, hz.2⟩
  · intro t ht htS
    exact (hinterior t).mpr (hcontacts t ht htS)
  · intro t _
    rw [hJclosed.frontier_eq, mem_sdiff, hmem, hinterior]
    simp only [mem_Icc, mem_Ioo]
    constructor
    · rintro ⟨⟨hlt, htu⟩, hnot⟩
      by_cases htl : t = l
      · exact Or.inl htl
      · exact Or.inr (le_antisymm htu (le_of_not_gt (fun h =>
          hnot ⟨lt_of_le_of_ne hlt (Ne.symm htl), h⟩)))
    · rintro (rfl | rfl)
      · exact ⟨⟨le_rfl, hlu.le⟩, by simp⟩
      · exact ⟨⟨hlu.le, le_rfl⟩, by simp⟩

end PoincareConjecture.M76
