import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Tactic.Linarith









set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Topology



theorem eventually_region_iff_of_transverse_coordinates
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    (e : OpenPartialHomeomorph (E × ℝ) X) {x : E} (hx : (x, 0) ∈ e.source)
    {q : X → ℝ} {C : Set X} (hC : IsClosed C)
    (htime : ∀ᶠ p in 𝓝 (x, (0 : ℝ)), q (e p) = -p.2)
    (hfront : ∀ᶠ z in 𝓝 (e (x, 0)), z ∈ frontier C ↔ q z = 0)
    (hside : ∀ᶠ z in 𝓝 (e (x, 0)), z ∈ interior C → q z < 0)
    (hacc : e (x, 0) ∈ closure (interior C)) :
    ∀ᶠ z in 𝓝 (e (x, 0)),
      (z ∈ C ↔ q z ≤ 0) ∧ (z ∈ interior C ↔ q z < 0) := by
  have hnear : ∀ᶠ p in 𝓝 (x, (0 : ℝ)),
      p ∈ e.source ∧ q (e p) = -p.2 ∧
        (e p ∈ frontier C ↔ q (e p) = 0) ∧
        (e p ∈ interior C → q (e p) < 0) := by
    filter_upwards [e.open_source.mem_nhds hx, htime,
      (e.continuousAt hx).eventually hfront, (e.continuousAt hx).eventually hside]
      with p hp ht hf hs
    exact ⟨hp, ht, hf, hs⟩
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp hnear
  let r := R / 2
  have hr : 0 < r := half_pos hR
  let V₀ := Metric.ball x r ×ˢ Ioo (-r) r
  let A₀ := Metric.ball x r ×ˢ Ioo (0 : ℝ) r
  have hAV : A₀ ⊆ V₀ := by
    intro p hp
    exact ⟨hp.1, ⟨by linarith [hp.2.1], hp.2.2⟩⟩
  have hVdata (p : E × ℝ) (hp : p ∈ V₀) :
      p ∈ e.source ∧ q (e p) = -p.2 ∧
        (e p ∈ frontier C ↔ q (e p) = 0) ∧
        (e p ∈ interior C → q (e p) < 0) := by
    apply hRsub
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨(Metric.mem_ball.mp hp.1).trans (half_lt_self hR), ?_⟩
    rw [Real.dist_eq, sub_zero]
    exact (abs_lt.mpr hp.2).trans (half_lt_self hR)
  have hVsrc : V₀ ⊆ e.source := fun p hp => (hVdata p hp).1
  have hAsrc : A₀ ⊆ e.source := hAV.trans hVsrc
  let V := e '' V₀
  let A := e '' A₀
  have hVo : IsOpen V := e.isOpen_image_of_subset_source
    (Metric.isOpen_ball.prod isOpen_Ioo) hVsrc
  have hxV : e (x, 0) ∈ V :=
    ⟨(x, 0), ⟨Metric.mem_ball_self hr, by constructor <;> linarith⟩, rfl⟩
  have hAconn : IsPreconnected A :=
    ((convex_ball x r).isPreconnected.prod isPreconnected_Ioo).image e
      (e.continuousOn.mono hAsrc)
  have hAavoid : Disjoint A (frontier C) := by
    apply disjoint_left.mpr
    rintro _ ⟨p, hp, rfl⟩ hf
    have hh := (hVdata p (hAV hp)).2.2.1.mp hf
    rw [(hVdata p (hAV hp)).2.1] at hh
    exact hp.2.1.ne' (neg_eq_zero.mp hh)
  have hAmeet : (A ∩ interior C).Nonempty := by
    obtain ⟨z, hzV, hzC⟩ := mem_closure_iff.mp hacc V hVo hxV
    obtain ⟨p, hp, rfl⟩ := hzV
    have hneg := (hVdata p hp).2.2.2 hzC
    rw [(hVdata p hp).2.1] at hneg
    exact ⟨e p, ⟨p, ⟨hp.1, neg_neg_iff_pos.mp hneg, hp.2.2⟩, rfl⟩, hzC⟩
  have hAinside : A ⊆ interior C :=
    preconnected_subset_interior_of_disjoint_frontier hAconn hAavoid hAmeet
  filter_upwards [hVo.mem_nhds hxV] with z hz
  obtain ⟨p, hp, rfl⟩ := hz
  have hd := hVdata p hp
  have hi : e p ∈ interior C ↔ q (e p) < 0 := by
    refine ⟨hd.2.2.2, fun hneg => ?_⟩
    rw [hd.2.1] at hneg
    exact hAinside ⟨p, ⟨hp.1, neg_neg_iff_pos.mp hneg, hp.2.2⟩, rfl⟩
  refine ⟨?_, hi⟩
  constructor
  · intro hmem
    by_cases hint : e p ∈ interior C
    · exact (hi.mp hint).le
    · exact (hd.2.2.1.mp ⟨subset_closure hmem, hint⟩).le
  · intro hq
    rcases lt_or_eq_of_le hq with hlt | heq
    · exact interior_subset (hi.mpr hlt)
    · exact hC.frontier_subset (hd.2.2.1.mpr heq)

end Poincare.Topology
