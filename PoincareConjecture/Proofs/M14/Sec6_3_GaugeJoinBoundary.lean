import PoincareConjecture.Proofs.M14.Sec6_3_GaugeJoinRegularity










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b)
  (α β : ℝ → G.Point)




theorem oneSidedGaugeJoin_clock {A B c r d : ℝ} (hr : 0 < r) (θ : ℝ → ℝ)
    (hα : ∀ s ∈ Icc A c, G.spacetime.timeFunction (α s) = θ s)
    (hβ : ∀ s ∈ Icc (c - r) B, G.spacetime.timeFunction (β s) = θ s)
    (hβrec : ∀ s ∈ Icc (c - r) c,
      (G.gaugeCover.cylinder b).toSpacetime (lift (β s)) = β s)
    {s : ℝ} (hs : s ∈ Icc A B) :
    G.spacetime.timeFunction (oneSidedGaugeJoin b lift α β c r d s) = θ s := by
  by_cases hl : s < c - r
  · rw [oneSidedGaugeJoin, if_pos hl]
    exact hα s ⟨hs.1, by linarith⟩
  have hleft : c - r ≤ s := le_of_not_gt hl
  by_cases hh : c ≤ s
  · rw [oneSidedGaugeJoin, if_neg hl, if_pos hh]
    exact hβ s ⟨hleft, hs.2⟩
  have hsc : s < c := lt_of_not_ge hh
  rw [oneSidedGaugeJoin_eq_middle b lift α β ⟨hleft, hsc⟩,
    gaugeBlend_time b lift α β _ _ _ (hβrec s ⟨hleft, hsc.le⟩)]
  exact hβ s ⟨hleft, hs.2⟩




theorem oneSidedGaugeJoin_continuousOn {A B c r d : ℝ} (hr : 0 < r)
    (hA : A < c - r) (hB : c < B)
    (hα : ContinuousOn α (Icc A c)) (hβ : ContinuousOn β (Icc (c - r) B))
    (hreg : ContinuousOn (oneSidedGaugeJoin b lift α β c r d) (Ioo A B)) :
    ContinuousOn (oneSidedGaugeJoin b lift α β c r d) (Icc A B) := by
  intro s hs
  rcases hs.1.eq_or_lt with heq | hAs
  · subst s
    have hAc : A < c := by linarith
    have hnear : Icc A c ∈ 𝓝[Icc A B] A := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hAc)] with t ht htc
      exact ⟨ht.1, htc.le⟩
    have hcont := (hα A ⟨le_rfl, hAc.le⟩).mono_of_mem_nhdsWithin hnear
    have hEq : oneSidedGaugeJoin b lift α β c r d =ᶠ[𝓝 A] α := by
      filter_upwards [gt_mem_nhds hA] with t ht
      simp only [oneSidedGaugeJoin, if_pos ht]
    exact hcont.congr_of_eventuallyEq (hEq.filter_mono nhdsWithin_le_nhds) hEq.eq_of_nhds
  rcases hs.2.eq_or_lt with heq | hsB
  · subst s
    have hBc : c - r < B := by linarith
    have hnear : Icc (c - r) B ∈ 𝓝[Icc A B] B := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hBc)] with t ht htc
      exact ⟨htc.le, ht.2⟩
    have hcont := (hβ B ⟨hBc.le, le_rfl⟩).mono_of_mem_nhdsWithin hnear
    have hEq : oneSidedGaugeJoin b lift α β c r d =ᶠ[𝓝 B] β := by
      filter_upwards [lt_mem_nhds hB] with t ht
      have hn : ¬t < c - r := by linarith
      simp only [oneSidedGaugeJoin, if_neg hn, if_pos ht.le]
    exact hcont.congr_of_eventuallyEq (hEq.filter_mono nhdsWithin_le_nhds) hEq.eq_of_nhds
  exact (hreg.continuousAt (isOpen_Ioo.mem_nhds ⟨hAs, hsB⟩)).continuousWithinAt

end PoincareConjecture.M14
