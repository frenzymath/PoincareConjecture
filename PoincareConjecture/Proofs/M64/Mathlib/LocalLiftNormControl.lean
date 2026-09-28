import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Instances.Real.Lemmas





set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture





theorem m64_eventually_lift_contact_norm_le
    {E X : Type*} [NormedAddCommGroup E] [TopologicalSpace X] [T2Space X]
    (F : OpenPartialHomeomorph E X) {v : E} (hv : v ∈ F.source)
    {beta : ℝ → X} {s : ℝ} (hs : 0 ≤ s)
    (hb : ContinuousOn beta (Icc 0 s)) (hi : InjOn beta (Icc 0 s))
    (hend : F v = beta s)
    (hshort : ∀ᶠ b in 𝓝[<] s, ‖F.symm (beta b)‖ < ‖v‖) :
    ∀ᶠ w in 𝓝 v, ∀ b ∈ Icc 0 s, F w = beta b → ‖w‖ ≤ ‖v‖ := by
  obtain ⟨l, hls, hbound⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hshort
  have hsub : Icc 0 l ⊆ Icc 0 s := Icc_subset_Icc le_rfl hls.le
  have htail : IsClosed (beta '' Icc 0 l) :=
    (isCompact_Icc.image_of_continuousOn (hb.mono hsub)).isClosed
  have havoid : F v ∉ beta '' Icc 0 l := by
    rintro ⟨b, hbI, heq⟩
    have hbs := hi (hsub hbI) ⟨hs, le_rfl⟩ (heq.trans hend)
    exact hls.not_ge (hbs ▸ hbI.2)
  have hnear : ∀ᶠ w in 𝓝 v, F w ∉ beta '' Icc 0 l :=
    ((F.continuousOn v hv).continuousAt (F.open_source.mem_nhds hv)).eventually
      (htail.isOpen_compl.mem_nhds havoid)
  filter_upwards [hnear, F.open_source.mem_nhds hv] with w hw hws
  intro b hbI heq
  rcases hbI.2.eq_or_lt with rfl | hbs
  · have hwv : w = v := F.injOn hws hv (heq.trans hend.symm)
    exact hwv ▸ le_rfl
  · have hlb : l < b := by
      by_contra hn
      exact hw ⟨b, ⟨hbI.1, le_of_not_gt hn⟩, heq.symm⟩
    have h : ‖F.symm (beta b)‖ < ‖v‖ := hbound ⟨hlb, hbs⟩
    rw [← heq, F.left_inv hws] at h
    exact h.le





theorem m64_exists_radial_contact_neighborhood
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : IsOpen S) {v : E} (hv : v ≠ 0) {R : ℝ} (hR : ‖v‖ ≤ R)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ S)
    {e : E → X} {beta : ℝ → X} {s : ℝ}
    (hlocal : ∀ᶠ w in 𝓝 v, ∀ b ∈ Icc 0 s, e w = beta b → ‖w‖ ≤ ‖v‖) :
    ∃ O : Set E, IsOpen O ∧ O ⊆ S ∧
      (∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ O) ∧
      ∀ w ∈ O, ∀ b ∈ Icc 0 s, e w = beta b → ‖w‖ ≤ R := by
  obtain ⟨V, hVsub, hV, hvV⟩ := _root_.mem_nhds_iff.mp hlocal
  refine ⟨S ∩ (ball 0 R ∪ V), hS.inter (isOpen_ball.union hV), inter_subset_left, ?_, ?_⟩
  · intro t ht
    refine ⟨hsegment t ht, ?_⟩
    rcases ht.2.eq_or_lt with rfl | ht1
    · rw [one_smul]
      exact Or.inr hvV
    · left
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_lt_mul_of_pos_right ht1 (norm_pos_iff.mpr hv)).trans_le (by simpa using hR)
  · intro w hw b hb heq
    rcases hw.2 with hball | hVw
    · exact (show ‖w‖ < R by simpa only [mem_ball, dist_zero_right] using hball).le
    · exact (hVsub hVw b hb heq).trans hR

end PoincareConjecture
