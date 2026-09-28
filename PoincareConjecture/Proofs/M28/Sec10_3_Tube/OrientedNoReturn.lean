import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckQuarterOverlap
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceNeckNoReturn

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckSegment

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}

theorem exists_oriented_frontier_no_return_accuracy
    (S : CounterexampleNeckSegment E) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (_hscalar : 0 < E.flow.scalar ⟨E.time, E.basepoint⟩)
        (_hsmall : epsilon ≤ epsilon₀)
        {N : EpsilonNeck (E.flow.metric E.time)} {s t u : ℝ},
        s ∈ Icc S.lower S.upper →
        t ∈ Icc S.lower S.upper →
        u ∈ Icc S.lower S.upper →
        N ∈ S.cover.necks →
        N.center = S.path s →
        s < t → t ≤ u →
        S.path t ∈ frontier N.carrier →
        S.path u ∉ N.central_sphere := by
  obtain ⟨epsilonR, hRpos, hRsmall, hR⟩ :=
    exists_source_neck_no_return_accuracy.{u}
  let epsilon₀ := min epsilonR (1 / 200 : ℝ)
  refine ⟨epsilon₀, lt_min hRpos (by norm_num),
    min_le_right _ _, ?_⟩
  intro hscalar hsmall N s t u hs ht hu hN hcenter hst htu hfront
  have hs01 : s ∈ Icc (0 : ℝ) 1 :=
    ⟨S.lower_pos.le.trans hs.1, hs.2.trans S.upper_lt_one.le⟩
  have hu01 : u ∈ Icc (0 : ℝ) 1 :=
    ⟨S.lower_pos.le.trans hu.1, hu.2.trans S.upper_lt_one.le⟩
  have hsphere : S.path s ∈ N.central_sphere := by
    rw [← hcenter]
    exact N.center_on_central_sphere
  intro hreturn
  have hmiddle := hR E S hscalar
    (hsmall.trans (min_le_left _ _)) N hN s hs01 u hu01 hsphere hreturn
  have hfrontmiddle := hmiddle ⟨hst.le, htu⟩
  have hfrontcarrier : S.path t ∈ N.carrier :=
    N.region_subset_carrier _ _ hfrontmiddle
  rw [frontier, N.carrier_open.interior_eq] at hfront
  exact hfront.2 hfrontcarrier

end PoincareConjecture.M28.CounterexampleNeckSegment
