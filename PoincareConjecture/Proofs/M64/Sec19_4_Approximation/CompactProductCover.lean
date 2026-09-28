import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option autoImplicit false

open Set Metric
open scoped Topology

universe u v

namespace PoincareConjecture

theorem m64_compact_product_cover_vertical_radius
    {X : Type u} {Y : Type v} [TopologicalSpace X] [CompactSpace X]
    [PseudoMetricSpace Y] [CompactSpace Y]
    (V : X × Y → Set (X × Y))
    (hV : ∀ w, IsOpen (V w)) (hself : ∀ w, w ∈ V w) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ w : X × Y,
      ∃ q : X × Y, ∀ y : Y, dist y w.2 < delta → (w.1, y) ∈ V q := by
  classical
  have hrect (w : X × Y) :
      ∃ U : Set X, IsOpen U ∧ w.1 ∈ U ∧
        ∃ r : ℝ, 0 < r ∧ U ×ˢ ball w.2 (2 * r) ⊆ V w := by
    obtain ⟨U, W, hU, hwU, hW, hwW, hprod⟩ :=
      mem_nhds_prod_iff'.mp ((hV w).mem_nhds (hself w))
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hwW)
    refine ⟨U, hU, hwU, r / 2, half_pos hr, ?_⟩
    have heq : 2 * (r / 2) = r := by ring
    rw [heq]
    exact (Set.prod_mono Subset.rfl hball).trans hprod
  choose U hU hmem r hr hrect using hrect
  let W : X × Y → Set (X × Y) := fun w => U w ×ˢ ball w.2 (r w)
  have hW (w : X × Y) : IsOpen (W w) := (hU w).prod isOpen_ball
  have hWself (w : X × Y) : w ∈ W w := ⟨hmem w, mem_ball_self (hr w)⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun w _ => mem_iUnion.mpr ⟨w, hWself w⟩)
  have hmin : ∀ S : Finset (X × Y),
      ∃ delta : ℝ, 0 < delta ∧ ∀ w ∈ S, delta ≤ r w := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert w T hw ih =>
      obtain ⟨delta, hdelta, hle⟩ := ih
      refine ⟨min delta (r w), lt_min hdelta (hr w), ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hle v hv)
  obtain ⟨delta, hdelta, hle⟩ := hmin S
  refine ⟨delta, hdelta, ?_⟩
  intro w
  obtain ⟨q, hqS, hwq⟩ := mem_iUnion₂.mp (hS (mem_univ w))
  refine ⟨q, ?_⟩
  intro y hy
  apply hrect q
  refine ⟨hwq.1, ?_⟩
  have hdist := dist_triangle y w.2 q.2
  have hnear : dist w.2 q.2 < r q := hwq.2
  change dist y q.2 < 2 * r q
  linarith only [hdist, hy, hnear, hle q hqS]

end PoincareConjecture
