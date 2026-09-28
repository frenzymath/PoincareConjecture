import PoincareConjecture.Proofs.M47.TerminalGermsBoundedJets
import PoincareConjecture.Proofs.M47.TerminalGermsJointEndpoint
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.DenselyOrdered











set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Topology NNReal

namespace PoincareConjecture.M47




theorem terminalGerms_closed_coefficient_gluing
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {a' a r C : ℝ} (ha' : a' < a) (ha : a < 0)
    (x : E) (hr : 0 < r) (hbuffer : closedBall x r ⊆ U)
    (B0 : E → F) (Bminus : ℝ × E → F)
    (hB0 : ContinuousOn B0 U)
    (hminus : ContDiffOn ℝ ∞ Bminus (Ioo a' 0 ×ˢ U))
    (hendpoint : ∀ t ∈ Ioo a' 0, ∀ y ∈ U,
      ‖Bminus (t, y) - B0 y‖ ≤ C * |t|)
    (source : ℕ → ℝ × E → F)
    (hjets : ∀ m : ℕ, ∀ z ∈ Ioo a 0 ×ˢ ball x r,
      Tendsto (fun k => iteratedFDeriv ℝ (m + 1) (source k) z) atTop
        (𝓝 (iteratedFDeriv ℝ (m + 1) Bminus z)))
    (hbound : ∀ m : ℕ, ∃ K : ℝ≥0, ∀ᶠ k in atTop,
      ∀ z ∈ Ioo a 0 ×ˢ ball x r, ‖iteratedFDeriv ℝ (m + 1) (source k) z‖ ≤ K) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => if z.1 < 0 then Bminus z else B0 z.2)
      (Icc a 0 ×ˢ closedBall x r) := by
  let G : ℝ × E → F := fun z => if z.1 < 0 then Bminus z else B0 z.2
  have hnegative {z : ℝ × E} (hz : z.1 < 0) : G =ᶠ[𝓝 z] Bminus := by
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with y hy
    exact if_pos hy
  have hlocal {z : ℝ × E} (hz : z ∈ Ioo a' 0 ×ˢ U) : ContDiffAt ℝ ∞ G z :=
    (hminus.contDiffAt ((isOpen_Ioo.prod hU).mem_nhds hz)).congr_of_eventuallyEq
      (hnegative hz.1.2)
  have hclosed : ContinuousOn G (Icc a 0 ×ˢ closedBall x r) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    by_cases ht0 : t < 0
    · exact (hlocal ⟨⟨ha'.trans_le ht.1, ht0⟩, hbuffer hy⟩).continuousAt.continuousWithinAt
    · have htzero : t = 0 := le_antisymm ht.2 (le_of_not_gt ht0)
      subst t
      apply (terminalGerms_joint_endpoint_continuity B0 Bminus y
        (hB0 y (hbuffer hy)) hendpoint).mono
      rintro ⟨s, z⟩ ⟨hs, hz⟩
      exact ⟨⟨ha'.trans_le hs.1, hs.2⟩, hbuffer hz⟩
  have hclosure : closure (Ioo a 0 ×ˢ ball x r) = Icc a 0 ×ˢ closedBall x r := by
    rw [closure_prod_eq, closure_Ioo ha.ne, closure_ball x hr.ne']
  rw [← hclosure] at hclosed ⊢
  apply terminalGerms_contDiffOn_closure_of_source_bounds
    (isOpen_Ioo.prod isOpen_ball) ((convex_Ioo a 0).prod (convex_ball x r)) G
    (fun z hz => (hlocal ⟨⟨ha'.trans hz.1.1, hz.1.2⟩,
      hbuffer (ball_subset_closedBall hz.2)⟩).contDiffWithinAt) hclosed source ?_ hbound
  intro m z hz
  have heq := ((hnegative hz.1.2).iteratedFDeriv ℝ (m + 1)).eq_of_nhds
  simpa only [heq] using hjets m z hz

end PoincareConjecture.M47
