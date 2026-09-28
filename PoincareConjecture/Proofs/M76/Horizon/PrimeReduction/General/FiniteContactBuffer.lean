import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set Metric
open scoped Topology

namespace PoincareConjecture.M76

theorem exists_finite_contact_buffer {S : Set ℝ} (hS : S.Finite)
    {u v : ℝ} (hcontact : Icc u v ∩ S = {u, v}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ,
      u - δ < a → a ≤ u → v ≤ b → b < v + δ →
      Icc a b ∩ S = {u, v} := by
  have hclosed : IsClosed (S \ {u, v}) := hS.sdiff.isClosed
  have hu : u ∈ (S \ {u, v})ᶜ := by simp
  have hv : v ∈ (S \ {u, v})ᶜ := by simp
  obtain ⟨εu, hεu, hballu⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl u hu
  obtain ⟨εv, hεv, hballv⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl v hv
  refine ⟨min εu εv, lt_min hεu hεv, ?_⟩
  intro a b ha hau hvb hb
  apply Subset.antisymm
  · rintro x ⟨hx, hxS⟩
    by_cases hxu : x < u
    · have hdist : dist x u < εu := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hxu)]
        linarith [min_le_left εu εv, hx.1]
      by_contra hn
      exact hballu hdist ⟨hxS, hn⟩
    · by_cases hvx : v < x
      · have hdist : dist x v < εv := by
          rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hvx)]
          linarith [min_le_right εu εv, hx.2]
        by_contra hn
        exact hballv hdist ⟨hxS, hn⟩
      · exact hcontact.subset ⟨⟨le_of_not_gt hxu, le_of_not_gt hvx⟩, hxS⟩
  · intro x hx
    have hxi := hcontact.symm.subset hx
    exact ⟨⟨hau.trans hxi.1.1, hxi.1.2.trans hvb⟩, hxi.2⟩

theorem exists_continuous_endpoint_contact_buffer {S : Set ℝ} (hS : S.Finite)
    {f g : ℝ → ℝ} (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (hcontact : Icc (f 0) (g 0) ∩ S = {f 0, g 0}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, |c| < ε →
      f c ≤ f 0 → g 0 ≤ g c → Icc (f c) (g c) ∩ S = {f 0, g 0} := by
  obtain ⟨δ, hδ, hbuffer⟩ := exists_finite_contact_buffer hS hcontact
  have hlo : ∀ᶠ c in 𝓝 (0 : ℝ), f 0 - δ < f c :=
    hf.eventually (lt_mem_nhds (by linarith))
  have hhi : ∀ᶠ c in 𝓝 (0 : ℝ), g c < g 0 + δ :=
    hg.eventually (gt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp (hlo.and hhi)
  refine ⟨ε, hε, ?_⟩
  intro c hc hfc hgc
  have h := hnear (by simpa only [Real.dist_eq, sub_zero] using hc)
  exact hbuffer (f c) (g c) h.1 hfc hgc h.2

end PoincareConjecture.M76
