import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeNormalization
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalRadius

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem exists_actual_source_tube_critical_radius_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)} (H : CounterexampleNeckFamily E),
        epsilon ≤ epsilon₀ →
        ∃ T : ∀ k, SourceTubeData (H.segment k),
          ∃ A₁ : ℝ, 0 < A₁ ∧ (4 * max C 2)⁻¹ * epsilon⁻¹ / 8 ≤ A₁ ∧
            A₁ ≤ A + 2 * endpointConnectorBudget epsilon C ∧
            (∀ r < A₁, tube.eventuallyRadiusBound
              (fun k x => ((H.tubeMetric T k).edist (H.tubeBase T k) x).toReal)
              (fun k x => (H.tubeConnection T k).scalarCurvature x) r) ∧
            ∃ φ : ℕ → ℕ, StrictMono φ ∧
              ∃ x : ∀ j, (T (φ j)).carrierOpen, ∀ j,
                ((H.tubeMetric T (φ j)).edist (H.tubeBase T (φ j)) (x j)).toReal <
                    A₁ + 1 / ((j : ℝ) + 1) ∧
                  (j : ℝ) < (H.tubeConnection T (φ j)).scalarCurvature (x j) := by
  obtain ⟨epsilonT, hTpos, hTsmall, hT⟩ := exists_source_tube_family_accuracy.{u}
  obtain ⟨epsilonB, hBpos, _, hB⟩ := exists_source_tube_initial_bound_accuracy.{u}
  refine ⟨min epsilonT epsilonB, lt_min hTpos hBpos,
    (min_le_left _ _).trans hTsmall, ?_⟩
  intro epsilon C A E H hsmall
  obtain ⟨T⟩ := hT H (hsmall.trans (min_le_left _ _))
  obtain ⟨hr₀, hbound⟩ := hB H T (hsmall.trans (min_le_right _ _))
  let d : ∀ k, (T k).carrierOpen → ℝ :=
    fun k x => ((H.tubeMetric T k).edist (H.tubeBase T k) x).toReal
  let q : ∀ k, (T k).carrierOpen → ℝ :=
    fun k x => (H.tubeConnection T k).scalarCurvature x
  have hlocal : tube.eventuallyRadiusBound d q
      ((4 * max C 2)⁻¹ * epsilon⁻¹ / 8) := by
    refine ⟨32 * (max C 2) ^ 2, Eventually.of_forall ?_⟩
    intro k x hx
    apply hbound k x
    change (H.tubeMetric T k).edist (H.tubeBase T k) x < _
    have h := (ENNReal.ofReal_lt_ofReal_iff hr₀).mpr hx
    simpa only [d, ENNReal.ofReal_toReal (H.tube_edist_ne_top T k _ _)] using h
  have hhigh : ∀ K : ℝ, ∃ᶠ k in atTop, ∃ x : (T k).carrierOpen,
      d k x < A + 2 * endpointConnectorBudget epsilon C ∧ K < q k x := by
    intro K
    have hq := (H.tube_high_scalar_tendsto T).eventually (eventually_gt_atTop K)
    apply (hq.mono ?_).frequently
    intro k hk
    exact ⟨H.tubeHigh T k,
      ENNReal.toReal_lt_of_lt_ofReal (H.tube_high_distance_lt T k), hk⟩
  obtain ⟨A₁, hA₁, hAL, hinterior, φ, hφ, x, hx⟩ :=
    tube.exists_critical_radius_witnesses d q hr₀ hlocal hhigh
  have hbase : (4 * max C 2)⁻¹ * epsilon⁻¹ / 8 ≤ A₁ := by
    by_contra hnot
    have hAr := lt_of_not_ge hnot
    obtain ⟨K, hK⟩ := hlocal
    have hsmall : ∀ᶠ j : ℕ in atTop,
        A₁ + 1 / ((j : ℝ) + 1) < (4 * max C 2)⁻¹ * epsilon⁻¹ / 8 := by
      have ht : Tendsto (fun j : ℕ => A₁ + 1 / ((j : ℝ) + 1))
          atTop (𝓝 A₁) := by
        simpa only [add_zero] using
          (tendsto_const_nhds (x := A₁)).add
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact ht.eventually (gt_mem_nhds hAr)
    have hlarge : ∀ᶠ j : ℕ in atTop, K < (j : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop K)
    obtain ⟨j, hk, hs, hl⟩ :=
      ((hφ.tendsto_atTop.eventually hK).and (hsmall.and hlarge)).exists
    exact (not_lt_of_ge (hk (x j) ((hx j).1.trans hs))) (hl.trans (hx j).2)
  exact ⟨T, A₁, hA₁, hbase, hAL, hinterior, φ, hφ, x, hx⟩

end PoincareConjecture.M28
