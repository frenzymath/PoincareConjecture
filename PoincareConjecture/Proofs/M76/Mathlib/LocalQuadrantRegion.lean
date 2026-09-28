import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Topology

theorem exists_positive_square_subset_region {A U V : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V) (hcover : Aᶜ = U ∪ V)
    (hzero : (0, 0) ∈ closure V)
    (hlocal : ∀ᶠ q in 𝓝 ((0 : ℝ), (0 : ℝ)),
      q ∈ A ↔ 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ (q.1 = 0 ∨ q.2 = 0))
    (hnegative : ∀ t : ℝ, 0 < t → (-t, -t) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ Ioo 0 δ ×ˢ Ioo 0 δ ⊆ V := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  let B : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Ioo (-δ) δ
  let L : Set (ℝ × ℝ) := Ioo (-δ) 0 ×ˢ Ioo (-δ) δ
  let D : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Ioo (-δ) 0
  let R : Set (ℝ × ℝ) := Ioo 0 δ ×ˢ Ioo 0 δ
  have hmodel (q : ℝ × ℝ) (hq : q ∈ B) :
      q ∈ A ↔ 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ (q.1 = 0 ∨ q.2 = 0) := by
    apply hball
    simpa only [B, ← ball_prod_same, Real.ball_eq_Ioo, zero_sub, zero_add] using hq
  have hLcomp : L ⊆ Aᶜ := by
    intro q hq hqa
    have hqb : q ∈ B := ⟨⟨hq.1.1, hq.1.2.trans hδ⟩, hq.2⟩
    exact (not_le_of_gt hq.1.2) ((hmodel q hqb).mp hqa).1
  have hDcomp : D ⊆ Aᶜ := by
    intro q hq hqa
    have hqb : q ∈ B := ⟨hq.1, hq.2.1, hq.2.2.trans hδ⟩
    exact (not_le_of_gt hq.2.2) ((hmodel q hqb).mp hqa).2.1
  have hRcomp : R ⊆ Aᶜ := by
    intro q hq hqa
    have hqb : q ∈ B :=
      ⟨⟨(neg_lt_zero.mpr hδ).trans hq.1.1, hq.1.2⟩,
        (neg_lt_zero.mpr hδ).trans hq.2.1, hq.2.2⟩
    rcases ((hmodel q hqb).mp hqa).2.2 with hx | hy
    · exact hq.1.1.ne' hx
    · exact hq.2.1.ne' hy
  have hpoint : (-δ / 2, -δ / 2) ∈ U := by
    simpa only [neg_div] using hnegative (δ / 2) (half_pos hδ)
  have hL : L ⊆ U :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).subset_left_of_subset_union hU hV hdis
      (hLcomp.trans (by rw [hcover]))
      ⟨(-δ / 2, -δ / 2), by dsimp [L]; constructor <;> constructor <;> linarith, hpoint⟩
  have hD : D ⊆ U :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).subset_left_of_subset_union hU hV hdis
      (hDcomp.trans (by rw [hcover]))
      ⟨(-δ / 2, -δ / 2), by dsimp [D]; constructor <;> constructor <;> linarith, hpoint⟩
  obtain ⟨q, hqB, hqV⟩ := mem_closure_iff.mp hzero B (isOpen_Ioo.prod isOpen_Ioo)
    (by dsimp [B]; exact ⟨⟨neg_lt_zero.mpr hδ, hδ⟩, neg_lt_zero.mpr hδ, hδ⟩)
  have hqx : 0 ≤ q.1 := by
    by_contra h
    exact Set.disjoint_left.mp hdis (hL ⟨⟨hqB.1.1, lt_of_not_ge h⟩, hqB.2⟩) hqV
  have hqy : 0 ≤ q.2 := by
    by_contra h
    exact Set.disjoint_left.mp hdis (hD ⟨hqB.1, hqB.2.1, lt_of_not_ge h⟩) hqV
  have hqoff : q ∉ A := by
    have : q ∈ Aᶜ := by rw [hcover]; exact Or.inr hqV
    exact this
  have hxne : q.1 ≠ 0 := fun hx => hqoff ((hmodel q hqB).mpr ⟨hqx, hqy, Or.inl hx⟩)
  have hyne : q.2 ≠ 0 := fun hy => hqoff ((hmodel q hqB).mpr ⟨hqx, hqy, Or.inr hy⟩)
  refine ⟨δ, hδ, ?_⟩
  exact (isPreconnected_Ioo.prod isPreconnected_Ioo).subset_right_of_subset_union hU hV hdis
    (hRcomp.trans (by rw [hcover]))
    ⟨q, ⟨⟨lt_of_le_of_ne hqx hxne.symm, hqB.1.2⟩,
      lt_of_le_of_ne hqy hyne.symm, hqB.2.2⟩, hqV⟩
