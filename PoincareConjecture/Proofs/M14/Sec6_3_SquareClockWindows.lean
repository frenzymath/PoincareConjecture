import PoincareConjecture.Proofs.M14.Sec6_3_GaugeClockNeighborhood
import PoincareConjecture.Proofs.M14.Mathlib.ClosedLeftNeighborhood

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M14

theorem squareClock_admissible_prefix {I : SpacetimeInterval} {T b : ℝ}
    (hT : T ∈ I.domain) (hb : 0 ≤ b) (hclock : T - b ^ 2 ∈ I.domain) :
    ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ I.domain := by
  intro s hs
  have hsq : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb).mpr hs.2
  exact I.ordConnected.out hclock hT ⟨by linarith, sub_le_self _ (sq_nonneg s)⟩

theorem exists_squareClock_prefix_neighborhood {I : SpacetimeInterval} {T s : ℝ}
    (hT : T ∈ I.domain) (hs : 0 < s) (hclock : T - s ^ 2 ∈ I.domain) :
    ∃ b : ℝ, s ≤ b ∧ (∀ r ∈ Icc 0 b, T - r ^ 2 ∈ I.domain) ∧
      Icc 0 b ∈ 𝓝[{r | 0 ≤ r ∧ T - r ^ 2 ∈ I.domain}] s := by
  by_cases hnext : ∃ b : ℝ, 0 ≤ b ∧ T - b ^ 2 ∈ I.domain ∧ s < b
  · obtain ⟨b, hb, htime, hsb⟩ := hnext
    exact ⟨b, hsb.le, squareClock_admissible_prefix hT hb htime,
      mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hs hsb)⟩
  · refine ⟨s, le_rfl, squareClock_admissible_prefix hT hs.le hclock, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ⟨hr.1, le_of_not_gt (fun hsr => hnext ⟨r, hr.1, hr.2, hsr⟩)⟩

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem exists_gauge_positive_squareClock_window (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b) {T s : ℝ} (hT : T ∈ I.domain) (hs : 0 < s)
    (hclock : T - s ^ 2 = t₀.val) :
    ∃ a c : ℝ, 0 < a ∧ a < s ∧ s ≤ c ∧
      (∀ r ∈ Icc a c, T - r ^ 2 ∈ (G.gaugeCover.interval b).domain) ∧
      Icc a c ∈ 𝓝[{r | 0 ≤ r ∧ T - r ^ 2 ∈ I.domain}] s := by
  have hphysical : T - s ^ 2 ∈ I.domain :=
    hclock ▸ (G.gaugeCover.cylinder b).interval_subset t₀.property
  obtain ⟨m, hsm, htime, hnear⟩ := exists_squareClock_prefix_neighborhood hT hs hphysical
  have hlocal := gauge_squareClock_mem_nhdsWithin b t₀ x₀ hclock htime
  obtain ⟨a, c, ha, has, hsc, _, hsub, hC⟩ := exists_closed_left_neighborhood hs hsm hlocal
  exact ⟨a, c, ha, has, hsc, fun r hr => hsub hr, nhdsWithin_le_of_mem hnear hC⟩

end PoincareConjecture.M14
