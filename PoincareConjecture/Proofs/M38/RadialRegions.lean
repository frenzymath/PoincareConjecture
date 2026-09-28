import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

namespace PoincareConjecture.M38

theorem radial_open_region_eq_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] {U : Set E}
    (hopen : IsOpen U) (hconnected : IsConnected U) (hzero : (0 : E) ∈ U)
    (hbounded : Bornology.IsBounded U)
    (hradial : ∀ x ∈ U, ∀ y : E, ‖y‖ = ‖x‖ → y ∈ U) :
    ∃ r : ℝ, 0 < r ∧ U = Metric.ball 0 r := by
  let R : Set ℝ := (fun x : E => ‖x‖) '' U
  have hRnonempty : R.Nonempty := ⟨0, ⟨0, hzero, norm_zero⟩⟩
  have hRbounded : BddAbove R := by
    obtain ⟨b, hb⟩ := hbounded.exists_norm_le
    exact ⟨b, fun _ ⟨x, hx, heq⟩ => heq ▸ hb x hx⟩
  let r := sSup R
  have hclosed : U ⊆ Metric.closedBall 0 r := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_csSup hRbounded ⟨x, hx, rfl⟩
  have hball : U ⊆ Metric.ball 0 r := by
    rw [← interior_closedBall']
    exact hopen.subset_interior_iff.mpr hclosed
  have hr : 0 < r := by
    simpa only [Metric.mem_ball, dist_self] using hball hzero
  refine ⟨r, hr, Set.Subset.antisymm hball ?_⟩
  intro x hx
  have hxr : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  obtain ⟨b, hb, hxb⟩ := exists_lt_of_lt_csSup hRnonempty hxr
  have hRconnected : IsConnected R := hconnected.image _ continuous_norm.continuousOn
  have hxR : ‖x‖ ∈ R := hRconnected.Icc_subset ⟨0, hzero, norm_zero⟩ hb
    ⟨norm_nonneg x, hxb.le⟩
  obtain ⟨y, hy, heq⟩ := hxR
  exact hradial y hy x heq.symm

end PoincareConjecture.M38
