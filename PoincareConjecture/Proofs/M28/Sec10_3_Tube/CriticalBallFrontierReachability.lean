import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallCurvature
import Mathlib.Topology.Sequences















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}


def CriticalBallFrontierAccess
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ)
    (hA1 : 0 < A1) : Prop :=
  ∀ {delta : ℝ}, 0 < delta ->
    ∀ᶠ k in atTop, ∀ x ∈ regularComponent
      (H.tubeCriticalMetric T A1 k)
      (H.tubeCriticalBase T A1 hA1 k) delta,
      A1 - delta / 2 <
          ((H.tubeMetric T k).edist (H.tubeBase T k)
            (x : (T k).carrierOpen)).toReal ->
      ∀ n : ℕ, ∃ y : H.tubeCriticalRegion T A1 k,
        A1 - 1 / ((n : ℝ) + 1) <
            ((H.tubeMetric T k).edist (H.tubeBase T k)
              (y : (T k).carrierOpen)).toReal ∧
        (H.tubeCriticalMetric T A1 k).edist x y <
          ENNReal.ofReal (3 * delta / 4)




theorem critical_radius_witnesses_eventually_near
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {A1 : ℝ}
    (hcrit : ∀ r < A1, tube.eventuallyRadiusBound
      (fun k x => ((H.tubeMetric T k).edist (H.tubeBase T k) x).toReal)
      (fun k x => (H.tubeConnection T k).scalarCurvature x) r)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (x : ∀ j, (T (φ j)).carrierOpen)
    (hx : ∀ j,
      ((H.tubeMetric T (φ j)).edist (H.tubeBase T (φ j)) (x j)).toReal <
        A1 + 1 / ((j : ℝ) + 1) ∧
      (j : ℝ) < (H.tubeConnection T (φ j)).scalarCurvature (x j)) :
    ∀ n : ℕ, ∀ᶠ j in atTop,
      A1 - 1 / ((n : ℝ) + 1) ≤
        ((H.tubeMetric T (φ j)).edist (H.tubeBase T (φ j)) (x j)).toReal := by
  intro n
  have hr : A1 - 1 / ((n : ℝ) + 1) < A1 := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    linarith [one_div_pos.mpr hn]
  obtain ⟨K, hK⟩ := hcrit _ hr
  have hKφ : ∀ᶠ j in atTop, ∀ y : (T (φ j)).carrierOpen,
      ((H.tubeMetric T (φ j)).edist (H.tubeBase T (φ j)) y).toReal <
        A1 - 1 / ((n : ℝ) + 1) →
      (H.tubeConnection T (φ j)).scalarCurvature y ≤ K := by
    exact hφ.tendsto_atTop.eventually hK
  have hKn : ∀ᶠ j : ℕ in atTop, K < (j : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop K)
  filter_upwards [hKφ, hKn] with j hKj hKjn
  by_contra hnot
  have hlt :
      ((H.tubeMetric T (φ j)).edist (H.tubeBase T (φ j)) (x j)).toReal <
        A1 - 1 / ((n : ℝ) + 1) := lt_of_not_ge hnot
  have hq : (H.tubeConnection T (φ j)).scalarCurvature (x j) ≤ K :=
    hKj (x j) hlt
  exact (not_lt_of_ge hq) (hKjn.trans (hx j).2)





theorem tube_high_eventually_near
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {A1 : ℝ}
    (hcrit : ∀ r < A1, tube.eventuallyRadiusBound
      (fun k x => ((H.tubeMetric T k).edist (H.tubeBase T k) x).toReal)
      (fun k x => (H.tubeConnection T k).scalarCurvature x) r) :
    ∀ n : ℕ, ∀ᶠ k in atTop,
      A1 - 1 / ((n : ℝ) + 1) <
        ((H.tubeMetric T k).edist (H.tubeBase T k)
          (H.tubeHigh T k)).toReal := by
  intro n
  let r : ℝ := A1 - 1 / (2 * ((n : ℝ) + 1))
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hr : r < A1 := by
    dsimp [r]
    have hpos : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    linarith
  obtain ⟨K, hK⟩ := hcrit r hr
  have hK' : ∀ᶠ k in atTop, ∀ y : (T k).carrierOpen,
      ((H.tubeMetric T k).edist (H.tubeBase T k) y).toReal < r →
        (H.tubeConnection T k).scalarCurvature y ≤ K := hK
  have hhigh : ∀ᶠ k in atTop, K <
      (H.tubeConnection T k).scalarCurvature (H.tubeHigh T k) :=
    (H.tube_high_scalar_tendsto T).eventually (eventually_gt_atTop K)
  filter_upwards [hK', hhigh] with k hk hhighk
  by_contra hnot
  have hle : ((H.tubeMetric T k).edist (H.tubeBase T k)
      (H.tubeHigh T k)).toReal ≤ A1 - 1 / ((n : ℝ) + 1) :=
    le_of_not_gt hnot
  have hlt : ((H.tubeMetric T k).edist (H.tubeBase T k)
      (H.tubeHigh T k)).toReal < r := by
    dsimp [r]
    have hhalf : 1 / (2 * ((n : ℝ) + 1)) <
        1 / ((n : ℝ) + 1) := by
      apply one_div_lt_one_div_of_lt hn
      linarith
    linarith
  have hbound := hk (H.tubeHigh T k) hlt
  exact (not_lt_of_ge hbound) hhighk

private theorem not_regular_of_frontier_access
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {A1 delta : ℝ}
    (_hA1 : 0 < A1) (hdelta : 0 < delta) {k : ℕ}
    {x : H.tubeCriticalRegion T A1 k}
    (haccess : ∀ n : ℕ, ∃ y : H.tubeCriticalRegion T A1 k,
      A1 - 1 / ((n : ℝ) + 1) <
          ((H.tubeMetric T k).edist (H.tubeBase T k)
            (y : (T k).carrierOpen)).toReal ∧
      (H.tubeCriticalMetric T A1 k).edist x y <
        ENNReal.ofReal (3 * delta / 4)) :
    x ∉ regularPoints (H.tubeCriticalMetric T A1 k) delta := by
  let r : ℝ := 3 * delta / 4
  have hr : r < delta := by
    dsimp [r]
    linarith
  intro hxreg
  have hcompact : IsCompact (closure
      ((H.tubeCriticalMetric T A1 k).ball x r)) := hxreg r hr
  choose y hyfront hydist using haccess
  have hyball : ∀ n, y n ∈ (H.tubeCriticalMetric T A1 k).ball x r := by
    intro n
    change (H.tubeCriticalMetric T A1 k).edist x (y n) < ENNReal.ofReal r
    simpa only [r] using hydist n
  have hyclosure : ∀ n, y n ∈ closure
      ((H.tubeCriticalMetric T A1 k).ball x r) := fun n =>
    subset_closure (hyball n)
  obtain ⟨z, hz, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hyclosure
  let d : H.tubeCriticalRegion T A1 k → ℝ := fun q =>
    ((H.tubeMetric T k).edist (H.tubeBase T k)
      (q : (T k).carrierOpen)).toReal
  have hcont : Continuous d := by
    let : PreconnectedSpace (T k).carrierOpen := (T k).preconnected
    have hambient := (H.tubeMetric T k).continuous_toReal_edist
      (H.tubeBase T k)
    exact hambient.comp continuous_subtype_val
  have hlimd : Tendsto (d ∘ y ∘ φ) atTop (𝓝 (d z)) := by
    exact (hcont.tendsto z).comp hlim
  have hlower : Tendsto (fun n => A1 - 1 / ((φ n : ℝ) + 1)) atTop
      (𝓝 A1) := by
    have hzero : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop
        (𝓝 0) := by
      exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        hφ.tendsto_atTop
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := A1)).sub hzero
  have hlower' : ∀ n, A1 - 1 / ((φ n : ℝ) + 1) ≤ d (y (φ n)) := by
    intro n
    exact le_of_lt (hyfront (φ n))
  have hupper : ∀ n, d (y (φ n)) ≤ A1 := by
    intro n
    have hycrit := (y (φ n)).property
    change (H.tubeMetric T k).edist (H.tubeBase T k)
      (y (φ n) : (T k).carrierOpen) < ENNReal.ofReal A1 at hycrit
    exact le_of_lt (ENNReal.toReal_lt_of_lt_ofReal hycrit)
  have hlimA : Tendsto (d ∘ y ∘ φ) atTop (𝓝 A1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower
      tendsto_const_nhds
    · exact hlower'
    · intro n
      exact hupper n
  have hEq : d z = A1 := tendsto_nhds_unique hlimd hlimA
  have hzfront : d z < A1 := by
    have hzcrit := z.property
    change (H.tubeMetric T k).edist (H.tubeBase T k)
      (z : (T k).carrierOpen) < ENNReal.ofReal A1 at hzcrit
    exact ENNReal.toReal_lt_of_lt_ofReal hzcrit
  exact (lt_irrefl A1) (hEq ▸ hzfront)



theorem criticalBallFrontierMargin_of_access
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {A1 : ℝ}
    (hA1 : 0 < A1)
    (haccess : CriticalBallFrontierAccess H T A1 hA1) :
    CriticalBallFrontierMargin H T A1 hA1 := by
  intro delta hdelta
  have hreach := haccess (delta := delta) hdelta
  filter_upwards [hreach] with k hk x hx
  change ((H.tubeMetric T k).edist (H.tubeBase T k)
      (x : (T k).carrierOpen)).toReal ≤ A1 - delta / 2
  by_contra hnot
  have hnear : A1 - delta / 2 <
      ((H.tubeMetric T k).edist (H.tubeBase T k)
        (x : (T k).carrierOpen)).toReal := lt_of_not_ge hnot
  have haccessX := hk x hx hnear
  exact (not_regular_of_frontier_access H T hA1 hdelta haccessX)
    (regularComponent_subset (H.tubeCriticalMetric T A1 k)
      (H.tubeCriticalBase T A1 hA1 k) delta hx)

end PoincareConjecture.M28.CounterexampleNeckFamily
