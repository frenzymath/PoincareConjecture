import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.Compact










set_option autoImplicit false

open Set

private theorem norm_sub_lt_two_of_no_opposite_unit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v w : E}
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hne : ‖v‖ = 1 → ‖w‖ = 1 → w ≠ -v) : ‖w - v‖ < 2 := by
  by_contra h
  have htwo : 2 ≤ ‖w - v‖ := le_of_not_gt h
  have htri := norm_sub_le w v
  have hv' : ‖v‖ = 1 := by linarith
  have hw' : ‖w‖ = 1 := by linarith
  have hd : ‖w - v‖ = 2 := by linarith
  have heq : ‖(-v) + w‖ = ‖-v‖ + ‖w‖ := by
    simpa only [sub_eq_add_neg, add_comm, norm_neg, hv', hw', one_add_one_eq_two] using hd
  have hsame := (norm_add_eq_iff_real.mp heq).symm
  exact hne hv' hw' (by simpa only [norm_neg, hv', hw', one_smul] using hsame)





theorem m64Compact_exists_uniform_strict_chord_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S T : Set E} (hS : IsCompact S) (hT : IsCompact T)
    (hneS : S.Nonempty) (hneT : T.Nonempty)
    (hSball : ∀ v ∈ S, ‖v‖ ≤ 1) (hTball : ∀ w ∈ T, ‖w‖ ≤ 1)
    (hopp : ∀ v ∈ S, ∀ w ∈ T, ‖v‖ = 1 → ‖w‖ = 1 → w ≠ -v) :
    ∃ d : ℝ, 0 ≤ d ∧ d < 2 ∧ ∀ v ∈ S, ∀ w ∈ T, ‖w - v‖ ≤ d := by
  obtain ⟨p, hp, hmax⟩ := (hS.prod hT).exists_isMaxOn (hneS.prod hneT)
    (show ContinuousOn (fun q : E × E => ‖q.2 - q.1‖) (S ×ˢ T) from
      (continuous_snd.sub continuous_fst).norm.continuousOn)
  refine ⟨‖p.2 - p.1‖, norm_nonneg _,
    norm_sub_lt_two_of_no_opposite_unit (hSball _ hp.1) (hTball _ hp.2)
      (hopp _ hp.1 _ hp.2), ?_⟩
  intro v hv w hw
  exact hmax (show (v, w) ∈ S ×ˢ T from ⟨hv, hw⟩)
