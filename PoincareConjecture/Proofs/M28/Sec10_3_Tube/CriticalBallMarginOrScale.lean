import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallCurvature
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeScaleBudget

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

private abbrev criticalTubeDistance
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) :
    ∀ k, (T k).carrierOpen → ℝ :=
  fun k x => ((H.tubeMetric T k).edist (H.tubeBase T k) x).toReal

private abbrev criticalTubeScalar
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) :
    ∀ k, (T k).carrierOpen → ℝ :=
  fun k x => (H.tubeConnection T k).scalarCurvature x

def CriticalBallModerateWitness
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {A1 delta : ℝ}
    (k : ℕ) (x : H.tubeCriticalRegion T A1 k) : Prop :=
  ∃ i : ℤ, i ∈ (T k).chain.shape.active ∧
    (x : (T k).carrierOpen).val
      ∈ ((T k).chain.neck i).carrier ∧
    |(((T k).chain.neck i).coordinate_inverse
        (x : (T k).carrierOpen).val).2| ≤
      3 * ((T k).chain.neck i).epsilon⁻¹ / 4 ∧
    delta / 48 ≤ H.tubeNodeScale T k i ∧
    (H.tubeMetric T k).ball (x : (T k).carrierOpen) (delta / 48) ⊆
      (Subtype.val : (T k).carrierOpen → _) ⁻¹'
        ((T k).chain.neck i).carrier ∧
    ∀ y ∈ (Subtype.val : (T k).carrierOpen → _) ⁻¹'
        ((T k).chain.neck i).carrier,
      |H.tubeNodeScale T k i ^ 2 * criticalTubeScalar H T k y - 1| <
        (1 / 100 : ℝ)

def CriticalBallMarginOrScale
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ)
    (hA1 : 0 < A1) : Prop :=
  ∀ {delta : ℝ}, 0 < delta ->
    ∀ᶠ k in atTop, ∀ x ∈ regularComponent
      (H.tubeCriticalMetric T A1 k)
      (H.tubeCriticalBase T A1 hA1 k) delta,
      criticalTubeDistance H T k x ≤ A1 - delta / 2 ∨
        CriticalBallModerateWitness H T (A1 := A1) (delta := delta) k x

theorem scalar_le_of_scale_lower_of_accuracy
    {delta scale scalar : ℝ}
    (hdelta : 0 < delta) (hscale : delta / 48 ≤ scale)
    (haccuracy : |scale ^ 2 * scalar - 1| < (1 / 100 : ℝ)) :
    scalar ≤ 2328 / delta ^ 2 := by
  have htop : scale ^ 2 * scalar < (101 / 100 : ℝ) := by
    have h := (abs_lt.mp haccuracy).2
    linarith
  have hscale_pos : 0 < scale := by
    have : 0 < delta / 48 := by positivity
    exact lt_of_lt_of_le this hscale
  have hscale_sq : delta ^ 2 / 2304 ≤ scale ^ 2 := by
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ delta / 48)
      hscale_pos.le).mpr hscale
    nlinarith only [hsq]
  have hdelta_sq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  by_cases hscalar : scalar ≤ 0
  · have htarget : 0 ≤ 2328 / delta ^ 2 := by positivity
    exact hscalar.trans htarget
  · have hscalar_pos : 0 < scalar := lt_of_not_ge hscalar
    have hprod : (delta ^ 2 / 2304) * scalar ≤ scale ^ 2 * scalar :=
      mul_le_mul_of_nonneg_right hscale_sq hscalar_pos.le
    have hsmall : (delta ^ 2 / 2304) * scalar < (101 / 100 : ℝ) :=
      hprod.trans_lt htop
    have hmul : scalar * delta ^ 2 < 2328 := by
      nlinarith only [hsmall]
    have hlt : scalar < 2328 / delta ^ 2 := by
      apply (lt_div_iff₀ hdelta_sq).2
      simpa only [mul_comm] using hmul
    exact hlt.le

theorem small_scale_budget
    {delta localScale tail : ℝ}
    (_hdelta : 0 < delta) (hlocal : localScale < delta / 48)
    (htail : tail < delta / 200) :
    2 * (5858 / 1000 : ℝ) * localScale + delta / 2 + tail <
      (3 / 4 : ℝ) * delta := by
  nlinarith

theorem moderate_witness_scalar_bound
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {A1 delta : ℝ}
    {k : ℕ} {x : H.tubeCriticalRegion T A1 k}
    (hdelta : 0 < delta)
    (hw : CriticalBallModerateWitness H T (A1 := A1) (delta := delta) k x) :
    ∀ y ∈ (H.tubeMetric T k).ball (x : (T k).carrierOpen) (delta / 48),
      criticalTubeScalar H T k y ≤ 2328 / delta ^ 2 := by
  obtain ⟨i, _hi, _hx, _hquarter, hscale, hball, haccuracy⟩ := hw
  intro y hy
  have hyN : y ∈ (Subtype.val : (T k).carrierOpen → _) ⁻¹'
      ((T k).chain.neck i).carrier := hball hy
  exact scalar_le_of_scale_lower_of_accuracy hdelta hscale (haccuracy y hyN)

private theorem critical_tube_distance_lt_of_ball_of_margin
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {A1 delta : ℝ}
    (hdelta : 0 < delta) {k : ℕ} {x : H.tubeCriticalRegion T A1 k}
    (hx : criticalTubeDistance H T k x ≤ A1 - delta / 2)
    {y : (T k).carrierOpen}
    (hy : y ∈ (H.tubeMetric T k).ball (x : (T k).carrierOpen) (delta / 48)) :
    criticalTubeDistance H T k y < A1 - delta / 4 := by
  have hxe : (H.tubeMetric T k).edist (H.tubeBase T k)
      (x : (T k).carrierOpen) ≠ ⊤ := H.tube_edist_ne_top T k _ _
  have hxof : (H.tubeMetric T k).edist (H.tubeBase T k)
      (x : (T k).carrierOpen) ≤ ENNReal.ofReal (A1 - delta / 2) := by
    rw [← ENNReal.ofReal_toReal hxe]
    exact ENNReal.ofReal_le_ofReal hx
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : (T k).carrierOpen → Type _) :=
    ⟨(H.tubeMetric T k).toRiemannianMetric⟩
  have htri : (H.tubeMetric T k).edist (H.tubeBase T k) y ≤
      (H.tubeMetric T k).edist (H.tubeBase T k) (x : (T k).carrierOpen) +
        (H.tubeMetric T k).edist (x : (T k).carrierOpen) y :=
    Manifold.riemannianEDist_triangle
  have hsum : (H.tubeMetric T k).edist (H.tubeBase T k) y <
      ENNReal.ofReal (A1 - delta / 4) := by
    have hdelta48 : 0 ≤ delta / 48 := by linarith
    have hA_delta : 0 ≤ A1 - delta / 2 := by
      have hnonneg : 0 ≤ criticalTubeDistance H T k x := ENNReal.toReal_nonneg
      linarith
    have hxy : (H.tubeMetric T k).edist (x : (T k).carrierOpen) y <
        ENNReal.ofReal (delta / 48) := hy
    calc
      _ ≤ (H.tubeMetric T k).edist (H.tubeBase T k) (x : (T k).carrierOpen) +
          (H.tubeMetric T k).edist (x : (T k).carrierOpen) y := htri
      _ ≤ ENNReal.ofReal (A1 - delta / 2) +
          (H.tubeMetric T k).edist (x : (T k).carrierOpen) y :=
        add_le_add hxof (le_refl _)
      _ < ENNReal.ofReal (A1 - delta / 2) + ENNReal.ofReal (delta / 48) :=
        ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hxy
      _ = ENNReal.ofReal (A1 - delta / 2 + delta / 48) := by
        rw [ENNReal.ofReal_add hA_delta hdelta48]
      _ < ENNReal.ofReal (A1 - delta / 4) := by
        apply (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr
        linarith
  exact ENNReal.toReal_lt_of_lt_ofReal hsum

theorem hcurv_on_criticalBall_of_margin_or_scale
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {A1 : ℝ}
    (hA1 : 0 < A1)
    (hsplit : CriticalBallMarginOrScale H T A1 hA1)
    (hcrit : ∀ r < A1, tube.eventuallyRadiusBound
      (criticalTubeDistance H T) (criticalTubeScalar H T) r)
    (hshi : CriticalBallLocalShi H T) :
    ∀ delta : ℝ, 0 < delta -> ∀ l : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      ∀ x ∈ regularComponent (H.tubeCriticalMetric T A1 k)
        (H.tubeCriticalBase T A1 hA1 k) delta,
        (H.tubeConnection T k).curvatureDerivativeNorm l x ≤ B := by
  intro delta hdelta l
  obtain ⟨K, hK⟩ := hcrit (A1 - delta / 4) (by linarith)
  obtain ⟨Bmargin, hBmargin, hBmargin_bound⟩ :=
    hshi K (delta / 48) (by positivity) l
  obtain ⟨Bscale, hBscale, hBscale_bound⟩ :=
    hshi (2328 / delta ^ 2) (delta / 48) (by positivity) l
  refine ⟨max Bmargin Bscale,
    (hBmargin.trans (le_max_left _ _)), ?_⟩
  have hsplit_delta := hsplit (delta := delta) hdelta
  filter_upwards [hK, hsplit_delta] with k hk hsplit_k x hx
  rcases hsplit_k x hx with hmargin | hmoderate
  · have hbound : ∀ y ∈ (H.tubeMetric T k).ball (x : (T k).carrierOpen)
        (delta / 48), criticalTubeScalar H T k y ≤ K := by
      intro y hy
      exact hk y (critical_tube_distance_lt_of_ball_of_margin H T hdelta hmargin hy)
    exact (hBmargin_bound k (x : (T k).carrierOpen) hbound).trans
      (le_max_left _ _)
  · have hbound := moderate_witness_scalar_bound H T hdelta hmoderate
    exact (hBscale_bound k (x : (T k).carrierOpen) hbound).trans
      (le_max_right _ _)

end PoincareConjecture.M28.CounterexampleNeckFamily
