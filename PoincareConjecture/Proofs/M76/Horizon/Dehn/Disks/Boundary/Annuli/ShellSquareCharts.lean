import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedShellDisks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.FourIntervalDiskChart

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)



structure NestedShellSquareCharts {S T : Set P2} (D : NestedShellDissection S T) where
  chart : (j : Fin 2) → Sq ≃ₜ D.disk j
  finitePL : ∀ j, (chart j).IsFinitePL
  left_agree : ∀ t : I,
    (chart 0 ⟨(0, t), by norm_num, t.property⟩ : P2) =
      chart 1 ⟨(0, t), by norm_num, t.property⟩
  right_agree : ∀ t : I,
    (chart 0 ⟨(1, t), by norm_num, t.property⟩ : P2) =
      chart 1 ⟨(1, t), by norm_num, t.property⟩
  outer_iff : ∀ j (z : Sq), (chart j z : P2) ∈ D.outer j ↔ (z : P2).2 = 0
  inner_iff : ∀ j (z : Sq), (chart j z : P2) ∈ D.inner j ↔ (z : P2).2 = 1
  left_iff : ∀ j (z : Sq), (chart j z : P2) ∈ D.left ↔ (z : P2).1 = 0
  right_iff : ∀ j (z : Sq), (chart j z : P2) ∈ D.right ↔ (z : P2).1 = 1

theorem NestedShellDissection.nonempty_square_charts {S T : Set P2}
    (D : NestedShellDissection S T) : Nonempty (NestedShellSquareCharts D) := by
  obtain ⟨l, hl, hl0, hl1⟩ := D.left_ball.exists_unitInterval_chart_with_endpoints D.xa_ne
  obtain ⟨r, hr, hr0, hr1⟩ := D.right_ball.exists_unitInterval_chart_with_endpoints D.yb_ne
  have hex (j : Fin 2) : ∃ H : Sq ≃ₜ D.disk j, H.IsFinitePL ∧
      (∀ t : I, (H ⟨(0, t), by norm_num, t.property⟩ : P2) = l t) ∧
      (∀ t : I, (H ⟨(1, t), by norm_num, t.property⟩ : P2) = r t) ∧
      (∀ z : Sq, (H z : P2) ∈ D.outer j ↔ (z : P2).2 = 0) ∧
      (∀ z : Sq, (H z : P2) ∈ D.inner j ↔ (z : P2).2 = 1) ∧
      (∀ z : Sq, (H z : P2) ∈ D.left ↔ (z : P2).1 = 0) ∧
      (∀ z : Sq, (H z : P2) ∈ D.right ↔ (z : P2).1 = 1) := by
    obtain ⟨p, hp, hp0, hp1⟩ := (D.outer_ball j).exists_unitInterval_chart_with_endpoints D.xy_ne
    obtain ⟨q, hq, hq0, hq1⟩ := (D.inner_ball j).exists_unitInterval_chart_with_endpoints D.ab_ne
    obtain ⟨H, hH, hHp, hHq, hHl, hHr⟩ := exists_four_interval_disk_chart
      (D.disk_ball j) p q l r hp hq hl hr hp0 hp1 hq0 hq1 hl0 hl1 hr0 hr1
      (D.cross_disjoint j) D.sides_disjoint (D.outer_left j) (D.outer_right j)
      (D.inner_left j) (D.inner_right j)
    exact ⟨H, hH, hHl, hHr,
      square_chart_horizontal_mem_iff H p (by norm_num) hHp,
      square_chart_horizontal_mem_iff H q (by norm_num) hHq,
      square_chart_vertical_mem_iff H l (by norm_num) hHl,
      square_chart_vertical_mem_iff H r (by norm_num) hHr⟩
  choose H hH hHl hHr hp hq hl' hr' using hex
  exact ⟨⟨H, hH, fun t ↦ (hHl 0 t).trans (hHl 1 t).symm,
    fun t ↦ (hHr 0 t).trans (hHr 1 t).symm, hp, hq, hl', hr'⟩⟩

namespace NestedShellDissection

variable {S T : Set P2} (D : NestedShellDissection S T)

theorem outer_subset_disk (j : Fin 2) : D.outer j ⊆ D.disk j :=
  fun _ hz ↦ (D.disk_ball j).1 (Or.inl (Or.inl hz))

theorem inner_subset_disk (j : Fin 2) : D.inner j ⊆ D.disk j :=
  fun _ hz ↦ (D.disk_ball j).1 (Or.inl (Or.inr hz))

theorem left_subset_disk (j : Fin 2) : D.left ⊆ D.disk j :=
  fun _ hz ↦ (D.disk_ball j).1 (Or.inr (Or.inl hz))

theorem right_subset_disk (j : Fin 2) : D.right ⊆ D.disk j :=
  fun _ hz ↦ (D.disk_ball j).1 (Or.inr (Or.inr hz))

theorem outer_in_disk_iff (j : Fin 2) (z : D.disk j) :
    (z : P2) ∈ frontier T ↔ (z : P2) ∈ D.outer j := by
  have hcase : ∀ k : Fin 2, ∀ w ∈ D.outer k, w ∈ D.left ∪ D.right → w ∈ D.outer j := by
    intro k w hw hside
    rcases hside with hl | hr
    · have hh : w = D.x := (D.outer_left k).subset ⟨hw, hl⟩
      exact hh ▸ (D.outer_ball j).1 (Or.inl rfl)
    · have hh : w = D.y := (D.outer_right k).subset ⟨hw, hr⟩
      exact hh ▸ (D.outer_ball j).1 (Or.inr rfl)
  constructor
  · intro hz
    rcases D.outer_cover.symm.subset hz with hz | hz
    · fin_cases j
      · exact hz
      · exact hcase 0 _ hz (D.disk_inter.subset ⟨D.outer_subset_disk 0 hz, z.property⟩)
    · fin_cases j
      · exact hcase 1 _ hz (D.disk_inter.subset ⟨z.property, D.outer_subset_disk 1 hz⟩)
      · exact hz
  · intro hz
    apply D.outer_cover.subset
    fin_cases j
    · exact Or.inl hz
    · exact Or.inr hz

theorem inner_in_disk_iff (j : Fin 2) (z : D.disk j) :
    (z : P2) ∈ frontier S ↔ (z : P2) ∈ D.inner j := by
  have hcase : ∀ k : Fin 2, ∀ w ∈ D.inner k, w ∈ D.left ∪ D.right → w ∈ D.inner j := by
    intro k w hw hside
    rcases hside with hl | hr
    · have hh : w = D.a := (D.inner_left k).subset ⟨hw, hl⟩
      exact hh ▸ (D.inner_ball j).1 (Or.inl rfl)
    · have hh : w = D.b := (D.inner_right k).subset ⟨hw, hr⟩
      exact hh ▸ (D.inner_ball j).1 (Or.inr rfl)
  constructor
  · intro hz
    rcases D.inner_cover.symm.subset hz with hz | hz
    · fin_cases j
      · exact hz
      · exact hcase 0 _ hz (D.disk_inter.subset ⟨D.inner_subset_disk 0 hz, z.property⟩)
    · fin_cases j
      · exact hcase 1 _ hz (D.disk_inter.subset ⟨z.property, D.inner_subset_disk 1 hz⟩)
      · exact hz
  · intro hz
    apply D.inner_cover.subset
    fin_cases j
    · exact Or.inl hz
    · exact Or.inr hz

end NestedShellDissection
end PoincareConjecture.M76.Dehn
