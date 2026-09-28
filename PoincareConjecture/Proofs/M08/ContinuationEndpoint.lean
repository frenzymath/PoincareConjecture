import PoincareConjecture.Proofs.M08.ContinuationLocalODE

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace PoincareConjecture.M08

theorem smooth_phase_eqOn_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) {z w : ℝ → E} {a b : ℝ} (hab : a < b)
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (a, z a))
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (f t (z t)) (Icc a b) t)
    (hw : ∀ t ∈ Icc a b, HasDerivWithinAt w (f t (w t)) (Icc a b) t)
    (heq : z a = w a) :
    ∃ d : ℝ, a < d ∧ d < b ∧ EqOn z w (Icc a d) := by
  obtain ⟨K, S, hS, hLip⟩ := hf.exists_lipschitzOnWith
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hzc : ContinuousOn z (Icc a b) := HasDerivWithinAt.continuousOn hz
  have hwc : ContinuousOn w (Icc a b) := HasDerivWithinAt.continuousOn hw
  have hzS : ∀ᶠ t in 𝓝[Icc a b] a, (t, z t) ∈ S :=
    (continuousWithinAt_id.prodMk (hzc a ha)) hS
  have hwS : ∀ᶠ t in 𝓝[Icc a b] a, (t, w t) ∈ S := by
    apply (continuousWithinAt_id.prodMk (hwc a ha))
    simpa only [heq, id_eq] using hS
  obtain ⟨U, hU, haU, hUS⟩ := mem_nhdsWithin.mp (hzS.and hwS)
  obtain ⟨l, r, ⟨hla, har⟩, hUr⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds haU)
  obtain ⟨d, had, hdm⟩ := exists_between (lt_min hab har)
  have hdb := hdm.trans_le (min_le_left b r)
  have hsub : Icc a d ⊆ Icc a b := Icc_subset_Icc_right hdb.le
  have hmem (t : ℝ) (ht : t ∈ Icc a d) : (t, z t) ∈ S ∧ (t, w t) ∈ S :=
    hUS ⟨hUr ⟨hla.trans_le ht.1, ht.2.trans_lt (hdm.trans_le (min_le_right b r))⟩, hsub ht⟩
  refine ⟨d, had, hdb, ?_⟩
  apply ODE_solution_unique_of_mem_Icc_right (K := K) (v := f)
    (s := fun t ↦ {y | (t, y) ∈ S}) ?_ (hzc.mono hsub) ?_
    (fun t ht ↦ (hmem t (Ico_subset_Icc_self ht)).1) (hwc.mono hsub) ?_
    (fun t ht ↦ (hmem t (Ico_subset_Icc_self ht)).2) heq
  · intro t _ht
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy y' hy'
    simpa only [Function.uncurry_apply_pair, Prod.dist_eq, dist_self,
      max_eq_right dist_nonneg] using hLip.dist_le_mul (x := (t, y)) (y := (t, y')) hy hy'
  · intro t ht
    exact (hz t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2.trans hdb⟩)
  · intro t ht
    exact (hw t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2.trans hdb⟩)

end PoincareConjecture.M08
