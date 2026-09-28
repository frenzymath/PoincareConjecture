import PoincareConjecture.Proofs.M34.Thm12_5_Existence.EndTruncation
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

noncomputable def endExhaustion (e : StandardCylindricalEnd g) (x : StandardCapSpace) : ℝ := by
  classical
  exact if x ∈ e.carrier then
    1 + (e.inverse x).2 * Real.smoothTransition ((e.inverse x).2 - 1)
  else 1

theorem one_le_endExhaustion (e : StandardCylindricalEnd g) (x : StandardCapSpace) :
    1 ≤ endExhaustion e x := by
  by_cases hx : x ∈ e.carrier
  · simp only [endExhaustion, if_pos hx, le_add_iff_nonneg_right]
    exact mul_nonneg (e.inverse_domain x hx) (Real.smoothTransition.nonneg _)
  · simp [endExhaustion, hx]

theorem endExhaustion_coordinate (e : StandardCylindricalEnd g)
    {z : StandardCylinderSpace} (hz : 0 ≤ z.2) :
    endExhaustion e (e.coordinate z) = 1 + z.2 * Real.smoothTransition (z.2 - 1) := by
  simp only [endExhaustion, if_pos (end_coordinate_mem_carrier e hz),
    e.coordinate_left_inverse ⟨mem_univ _, hz⟩]

theorem endExhaustion_eq_one_on_truncation (e : StandardCylindricalEnd g)
    {x : StandardCapSpace} (hx : x ∈ endTruncation e 1) : endExhaustion e x = 1 := by
  by_cases hcar : x ∈ e.carrier
  · have hh : (e.inverse x).2 < 1 := by
      apply (endTruncation_coordinate_iff e zero_le_one (e.inverse_domain x hcar)).mp
      simpa only [e.coordinate_right_inverse hcar] using hx
    rw [endExhaustion, if_pos hcar, Real.smoothTransition.zero_of_nonpos (by linarith)]
    ring
  · simp [endExhaustion, hcar]

theorem endExhaustion_coordinate_of_two_le (e : StandardCylindricalEnd g)
    {z : StandardCylinderSpace} (hz : 2 ≤ z.2) :
    endExhaustion e (e.coordinate z) = 1 + z.2 := by
  rw [endExhaustion_coordinate e (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem endExhaustion_contMDiff (e : StandardCylindricalEnd g) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (endExhaustion e) := by
  intro x
  by_cases hx : x ∈ endClosedTail e 1
  · obtain ⟨z, hz, rfl⟩ := hx
    have hzpos : 0 < z.2 := zero_lt_one.trans_le hz.2
    have hi := (end_inverse_contMDiffAt e hzpos).snd
    have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun r : ℝ => 1 + r * Real.smoothTransition (r - 1)) :=
      (show ContDiff ℝ ∞ (fun r : ℝ => 1 + r * Real.smoothTransition (r - 1))
        from by fun_prop).contMDiff
    have hf := hs.contMDiffAt.comp (e.coordinate z) hi
    apply hf.congr_of_eventuallyEq
    have hU := end_isOpen_coordinate_image e (isOpen_univ.prod isOpen_Ioi)
      (fun w (hw : w ∈ univ ×ˢ Ioi (0 : ℝ)) => hw.2)
    filter_upwards [hU.mem_nhds ⟨z, ⟨mem_univ _, hzpos⟩, rfl⟩] with y hy
    obtain ⟨w, hw, rfl⟩ := hy
    simp only [Function.comp_apply, endExhaustion,
      if_pos (end_coordinate_mem_carrier e hw.2.le)]
  · have hopen := endTruncation_isOpen e (L := 1) zero_le_one
    have heq : endExhaustion e =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact endExhaustion_eq_one_on_truncation e hy
    exact contMDiffAt_const.congr_of_eventuallyEq heq

theorem endExhaustion_sublevel_isCompact (e : StandardCylindricalEnd g) (R : ℝ) :
    IsCompact {x : StandardCapSpace | endExhaustion e x ≤ R} := by
  have hpos : 0 ≤ max 2 R := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  have hcompact := endTruncatedCore_isCompact e hpos
  apply hcompact.of_isClosed_subset
  · exact isClosed_le (endExhaustion_contMDiff e).continuous continuous_const
  · intro x hx htail
    obtain ⟨z, hz, rfl⟩ := htail
    have htwo : 2 ≤ z.2 := (le_max_left _ _).trans hz.2.le
    change endExhaustion e (e.coordinate z) ≤ R at hx
    rw [endExhaustion_coordinate_of_two_le e htwo] at hx
    have hR : R < z.2 := (le_max_right _ _).trans_lt hz.2
    linarith

end PoincareConjecture.M34
