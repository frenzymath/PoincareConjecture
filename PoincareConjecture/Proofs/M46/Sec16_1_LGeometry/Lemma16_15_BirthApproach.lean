import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_BirthNeighborhood
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_WindowAvoidance









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12




theorem backwardPath_reaches_future_neighborhood
    {F : GeneralizedRicciFlowData.{u}} (G : FlowBoxRicciGeometry F)
    {T tau a b origin width : ℝ} {x y : G.toLGeometry.Point}
    (p : M14BackwardPath G.toLGeometry T 0 tau x y)
    (ha : 0 ≤ a) (hab : a < b) (hbtau : b ≤ tau) (hwidth : 0 < width)
    (hclock : T - b = origin) {O : Set G.toLGeometry.Point}
    (hnear : O ∈ 𝓝[G.realization.spacetime.timeFunction ⁻¹'
      Ioc origin (origin + width)] (p.curve b)) :
    ∃ r ∈ Ioo a b, p.curve r ∈ O := by
  have hsub : Ioo a b ⊆ Icc 0 tau := by
    intro r hr
    exact ⟨ha.trans hr.1.le, hr.2.le.trans hbtau⟩
  have : NeBot (𝓝[Ioo a b] b) := right_nhdsWithin_Ioo_neBot hab
  have hcont : Tendsto p.curve (𝓝[Ioo a b] b) (𝓝 (p.curve b)) :=
    (p.curve_continuous b ⟨ha.trans hab.le, hbtau⟩).mono hsub
  have htend : Tendsto (fun r : ℝ => T - r) (𝓝[Ioo a b] b) (𝓝 origin) := by
    rw [← hclock]
    exact (continuous_const.sub continuous_id).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hupper : ∀ᶠ r in 𝓝[Ioo a b] b, T - r < origin + width :=
    htend (Iio_mem_nhds (by linarith : origin < origin + width))
  have htimes : ∀ᶠ r in 𝓝[Ioo a b] b,
      p.curve r ∈ G.realization.spacetime.timeFunction ⁻¹' Ioc origin (origin + width) := by
    filter_upwards [hupper, self_mem_nhdsWithin] with r hr ht
    change G.toLGeometry.spacetime.timeFunction (p.curve r) ∈ Ioc origin (origin + width)
    rw [p.curve_time r (hsub ht)]
    exact ⟨by linarith [ht.2], hr.le⟩
  have hcapture := (tendsto_nhdsWithin_iff.mpr ⟨hcont, htimes⟩) hnear
  have hmem : ∀ᶠ r in 𝓝[Ioo a b] b, r ∈ Ioo a b := self_mem_nhdsWithin
  obtain ⟨r, hr, hcaptured⟩ := (hmem.and hcapture).exists
  exact ⟨r, hr, hcaptured⟩

end PoincareConjecture.Proofs.M46
