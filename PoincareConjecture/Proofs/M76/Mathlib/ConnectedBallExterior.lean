import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isConnected_compl_closedBall_zero (hdim : 1 < Module.rank ℝ E) (r : ℝ) :
    IsConnected (closedBall (0 : E) r)ᶜ := by
  by_cases hr : 0 ≤ r
  · let f : ℝ × E → E := fun p => p.1 • p.2
    have hconn : IsConnected (Ioi r ×ˢ sphere (0 : E) 1) :=
      isConnected_Ioi.prod (isConnected_sphere hdim 0 zero_le_one)
    have himage : f '' (Ioi r ×ˢ sphere (0 : E) 1) = (closedBall (0 : E) r)ᶜ := by
      ext y
      constructor
      · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
        have hnorm : ‖u‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hu
        simp only [mem_compl_iff, mem_closedBall, dist_zero_right]
        change ¬ ‖t • u‖ ≤ r
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hr.trans ht.le), hnorm, mul_one]
        exact not_le.mpr ht
      · intro hy
        have hynorm : r < ‖y‖ := by
          simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hy
        have hpos : 0 < ‖y‖ := hr.trans_lt hynorm
        refine ⟨(‖y‖, ‖y‖⁻¹ • y), ⟨hynorm, ?_⟩, ?_⟩
        · simp only [mem_sphere, dist_zero_right]
          change ‖‖y‖⁻¹ • y‖ = 1
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos.le),
            inv_mul_cancel₀ hpos.ne']
        · change ‖y‖ • (‖y‖⁻¹ • y) = y
          rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    rw [← himage]
    exact hconn.image f (continuous_fst.smul continuous_snd).continuousOn
  · rw [closedBall_eq_empty.mpr (lt_of_not_ge hr), compl_empty]
    exact isConnected_univ
