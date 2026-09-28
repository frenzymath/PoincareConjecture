import PoincareConjecture.Proofs.M28.Sec10_3_Tube.FirstTwoNeckBall
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.FirstTwoNeckScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeInitialPair
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCriticalRadius

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem exists_source_tube_large_initial_bound_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)} (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)), epsilon ≤ epsilon₀ →
        ∀ᶠ k in atTop, ∀ x : (T k).carrierOpen,
          x ∈ (H.tubeMetric T k).ball (H.tubeBase T k)
            ((7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹) →
          (H.tubeConnection T k).scalarCurvature x ≤ 64 * (max C 2) ^ 2 := by
  obtain ⟨epsilonS, hSpos, _, hsuccessor⟩ := exists_source_tube_successor_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hratio⟩ := exists_initial_pair_scalar_accuracy.{u}
  let epsilon₀ := min epsilonS (min epsilonR (1 / 1000))
  refine ⟨epsilon₀, lt_min hSpos (lt_min hRpos (by norm_num)),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro epsilon C A E H T hsmall
  have hεS : epsilon ≤ epsilonS := hsmall.trans (min_le_left _ _)
  have hεR : epsilon ≤ epsilonR :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε : epsilon ≤ 1 / 1000 :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  filter_upwards [hsuccessor H T hεS] with k hk
  intro x hx
  let g := (E (k + H.shift)).flow.metric (E (k + H.shift)).time
  let c := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hc : 0 < c := H.base_scalar_pos k
  let N := ((T k).list.node 0).2
  let Q := ((T k).list.node 1).2
  obtain ⟨hNchain, _, hleast, _, hcenter, hQε, hclose, hscale, _⟩ :=
    (T k).initial_pair hk
  have hNε : N.epsilon = epsilon := by
    change ((T k).list.node 0).2.epsilon = epsilon
    rw [← hNchain, (T k).tube.chain.epsilon_eq 0 hleast.1, (T k).epsilon_eq]
  have hnormdist : intrinsicEDist (H.normalizedSliceMetric k) (T k).tube.carrier
      N.center x.val < ENNReal.ofReal
        ((7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹) := by
    change (H.tubeMetric T k).edist (H.tubeBase T k) x < _ at hx
    rw [CounterexampleNeckFamily.tubeMetric, intrinsicOpenMetric_edist] at hx
    rw [show N.center = (H.segment k).path (H.segment k).lower from hcenter]
    exact hx
  have hrawdist : intrinsicEDist g (T k).tube.carrier N.center x.val <
      ENNReal.ofReal ((7 / 4 : ℝ) * N.scale * epsilon⁻¹) := by
    obtain ⟨L, ⟨γ, hγ, h0, h1, hγT, rfl⟩, hlength⟩ := sInf_lt_iff.mp hnormdist
    have hscale0 : Real.sqrt c * N.scale = (4 * max C 2)⁻¹ :=
      H.normalizedSlice_low_neck_scale k N hcenter
    have hradius : (7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ =
        Real.sqrt c * ((7 / 4 : ℝ) * N.scale * epsilon⁻¹) := by
      rw [← hscale0]
      ring
    have hhom := M13.homothety_pathELength g (H.normalizedSliceMetric k)
      (Diffeomorph.refl (𝓡 3) _ ∞) c hc
      (M13.identity_metricHomothety g c hc) γ 0 1 hγ
    change (H.normalizedSliceMetric k).pathELength γ 0 1 =
      ENNReal.ofReal (Real.sqrt c) * g.pathELength γ 0 1 at hhom
    rw [hhom, hradius, ENNReal.ofReal_mul (Real.sqrt_nonneg c)] at hlength
    have hshort : g.pathELength γ 0 1 <
        ENNReal.ofReal ((7 / 4 : ℝ) * N.scale * epsilon⁻¹) :=
      (ENNReal.mul_right_strictMono
        (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne'
        ENNReal.ofReal_ne_top).lt_iff_lt.mp hlength
    have hle : intrinsicEDist g (T k).tube.carrier N.center x.val ≤
        g.pathELength γ 0 1 := sInf_le ⟨γ, hγ, h0, h1, hγT, rfl⟩
    exact hle.trans_lt hshort
  have htwo : x.val ∈ N.carrier ∪ Q.carrier := by
    have h := intrinsic_ball_subset_first_two_necks (T k).tube hleast Q
      (by rw [(T k).epsilon_eq]; exact hε) hQε
      (by simpa only [hNchain] using hscale.1)
      (by simpa only [hNchain] using hclose)
      (by simpa only [hNchain, (T k).epsilon_eq] using hrawdist)
    simpa only [hNchain] using h
  have hscalar := hratio ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier
    g ((E (k + H.shift)).flow.connection (E (k + H.shift)).time) N Q
    (by rw [hNε]; exact hεR)
    (hQε.trans ((T k).epsilon_eq.trans hNε.symm)) hscale.1 x.val htwo
  change (E (k + H.shift)).flow.scalar ⟨(E (k + H.shift)).time, x.val⟩ ≤
    4 * (E (k + H.shift)).flow.scalar ⟨(E (k + H.shift)).time, N.center⟩ at hscalar
  rw [hcenter, (H.segment k).lower_scalar] at hscalar
  rw [H.tube_scalar_eq, H.normalizedSlice_scalar_eq]
  apply (div_le_iff₀ hc).mpr
  nlinarith only [hscalar]

theorem exists_actual_source_tube_large_critical_radius_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)} (H : CounterexampleNeckFamily E),
        epsilon ≤ epsilon₀ →
        ∃ T : ∀ k, SourceTubeData (H.segment k),
          ∃ A₁ : ℝ, 0 < A₁ ∧ (7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ ≤ A₁ ∧
            A₁ ≤ A + 2 * endpointConnectorBudget epsilon C ∧
            (∀ r < A₁, tube.eventuallyRadiusBound
              (fun k x => ((H.tubeMetric T k).edist (H.tubeBase T k) x).toReal)
              (fun k x => (H.tubeConnection T k).scalarCurvature x) r) ∧
            ∃ φ : ℕ → ℕ, StrictMono φ ∧
              ∃ x : ∀ j, (T (φ j)).carrierOpen, ∀ j,
                ((H.tubeMetric T (φ j)).edist (H.tubeBase T (φ j)) (x j)).toReal <
                    A₁ + 1 / ((j : ℝ) + 1) ∧
                  (j : ℝ) < (H.tubeConnection T (φ j)).scalarCurvature (x j) := by
  obtain ⟨epsilonT, hTpos, hTsmall, hT⟩ :=
    exists_actual_source_tube_critical_radius_accuracy.{u}
  obtain ⟨epsilonB, hBpos, _, hB⟩ := exists_source_tube_large_initial_bound_accuracy.{u}
  refine ⟨min epsilonT epsilonB, lt_min hTpos hBpos,
    (min_le_left _ _).trans hTsmall, ?_⟩
  intro epsilon C A E H hsmall
  obtain ⟨T, A₁, hA₁, _, hAL, hinterior, φ, hφ, x, hx⟩ :=
    hT H (hsmall.trans (min_le_left _ _))
  have hbound := hB H T (hsmall.trans (min_le_right _ _))
  have hlarge : (7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ ≤ A₁ := by
    by_contra hnot
    have hAr := lt_of_not_ge hnot
    have hsmall : ∀ᶠ j : ℕ in atTop,
        A₁ + 1 / ((j : ℝ) + 1) < (7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ := by
      have ht : Tendsto (fun j : ℕ => A₁ + 1 / ((j : ℝ) + 1))
          atTop (𝓝 A₁) := by
        simpa only [add_zero] using
          (tendsto_const_nhds (x := A₁)).add
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact ht.eventually (gt_mem_nhds hAr)
    have hdiv : ∀ᶠ j : ℕ in atTop, 64 * (max C 2) ^ 2 < (j : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
    obtain ⟨j, hbj, hs, hd⟩ :=
      ((hφ.tendsto_atTop.eventually hbound).and (hsmall.and hdiv)).exists
    have hrpos : 0 < (7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ :=
      hA₁.trans hAr
    have hball : x j ∈ (H.tubeMetric T (φ j)).ball (H.tubeBase T (φ j))
        ((7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹) := by
      change (H.tubeMetric T (φ j)).edist (H.tubeBase T (φ j)) (x j) < _
      have he := (ENNReal.ofReal_lt_ofReal_iff hrpos).mpr ((hx j).1.trans hs)
      simpa only [ENNReal.ofReal_toReal (H.tube_edist_ne_top T (φ j) _ _)] using he
    exact (not_lt_of_ge (hbj (x j) hball)) (hd.trans (hx j).2)
  exact ⟨T, A₁, hA₁, hlarge, hAL, hinterior, φ, hφ, x, hx⟩

end PoincareConjecture.M28
