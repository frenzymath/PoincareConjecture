import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic


open Set
namespace Metric
theorem exists_open_neighborhood_inter_eq_of_separated
    {X : Type*} [PseudoMetricSpace X] {A E U : Set X}
    (hU : IsOpen U) (hAE : A ⊆ E) (hAU : A ⊆ U)
    {b q : ℝ} (hb : 0 < b) (hq : 0 < q)
    (hsep : ∀ x ∈ A, ∀ y ∈ E, dist x y < q → y ∈ A)
    (hbuffer : ∀ x ∈ A, closedBall x b ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ V ⊆ U ∧ V ∩ E = A ∧
      ∀ x ∈ A, closedBall x (min (b / 2) (q / 8)) ⊆ V := by
  refine ⟨U ∩ thickening (q / 4) A, hU.inter isOpen_thickening, inter_subset_left, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro y ⟨hyV, hyE⟩
      obtain ⟨x, hx, hxy⟩ := mem_thickening_iff.mp hyV.2
      exact hsep x hx y hyE (by rw [dist_comm]; linarith)
    · intro x hx
      exact ⟨⟨hAU hx, self_subset_thickening (by positivity) A hx⟩, hAE hx⟩
  · intro x hx y hy
    have hxy := mem_closedBall.mp hy
    refine ⟨hbuffer x hx (mem_closedBall.mpr ?_), mem_thickening_iff.mpr ⟨x, hx, ?_⟩⟩
    · exact hxy.trans ((min_le_left _ _).trans (by linarith))
    · exact hxy.trans_lt ((min_le_right _ _).trans_lt (by linarith))
end Metric
