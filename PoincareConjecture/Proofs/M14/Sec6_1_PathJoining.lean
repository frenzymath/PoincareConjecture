import PoincareConjecture.Proofs.M14.Sec6_1_CompactPerturbation

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ c τ₂ : ℝ} {x z₁ z₂ y : G.Point}

theorem joinedCurve_action_integrable (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (p : M14BackwardPath G T τ₁ c x z₁) (q : M14BackwardPath G T c τ₂ z₂ y)
    (γ : ℝ → G.Point) {a b : ℝ}
    (ha : τ₁ < a) (hac : a < c) (hcb : c < b) (hb : b < τ₂)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 γ (Ioo τ₁ τ₂))
    (hleft : ∀ t ≤ a, γ t = p.curve t) (hright : ∀ t, b ≤ t → γ t = q.curve t) :
    IntervalIntegrable (M14RawLIntegrand G γ (projectedCurveVelocity G γ)) volume τ₁ τ₂ := by
  have hab : a < b := hac.trans hcb
  have hmiddle : IntervalIntegrable (M14RawLIntegrand G γ (projectedCurveVelocity G γ))
      volume a b := ((rawLIntegrand_projectedVelocity_continuousOn hM12 isOpen_Ioo hγ).mono
        (fun _ ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩)).intervalIntegrable_of_Icc hab.le
  have hleftOld := p.action_integrable.mono_set
    (show uIcc τ₁ a ⊆ uIcc τ₁ c by
      rw [uIcc_of_le ha.le, uIcc_of_le p.tau_lt.le]
      exact Icc_subset_Icc_right hac.le)
  have hleftNew : IntervalIntegrable (M14RawLIntegrand G γ (projectedCurveVelocity G γ))
      volume τ₁ a := hleftOld.congr_uIoo (by
    intro s hs
    rw [uIoo_of_le ha.le] at hs
    symm
    apply rawLIntegrand_eq_backward_of_eventuallyEq p ⟨hs.1, hs.2.trans hac⟩
    filter_upwards [gt_mem_nhds hs.2] with t ht
    exact hleft t ht.le)
  have hrightOld := q.action_integrable.mono_set
    (show uIcc b τ₂ ⊆ uIcc c τ₂ by
      rw [uIcc_of_le hb.le, uIcc_of_le q.tau_lt.le]
      exact Icc_subset_Icc_left hcb.le)
  have hrightNew : IntervalIntegrable (M14RawLIntegrand G γ (projectedCurveVelocity G γ))
      volume b τ₂ := hrightOld.congr_uIoo (by
    intro s hs
    rw [uIoo_of_le hb.le] at hs
    symm
    apply rawLIntegrand_eq_backward_of_eventuallyEq q ⟨hcb.trans hs.1, hs.2⟩
    filter_upwards [lt_mem_nhds hs.1] with t ht
    exact hright t ht.le)
  exact hleftNew.trans (hmiddle.trans hrightNew)

noncomputable def pathOfC1Join (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (p : M14BackwardPath G T τ₁ c x z₁) (q : M14BackwardPath G T c τ₂ z₂ y)
    (γ : ℝ → G.Point) {a b : ℝ}
    (ha : τ₁ < a) (hac : a < c) (hcb : c < b) (hb : b < τ₂)
    (hcont : ContinuousOn γ (Icc τ₁ τ₂))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 γ (Ioo τ₁ τ₂))
    (hclock : ∀ t ∈ Icc τ₁ τ₂, G.spacetime.timeFunction (γ t) = T - t)
    (hleft : ∀ t ≤ a, γ t = p.curve t) (hright : ∀ t, b ≤ t → γ t = q.curve t) :
    M14BackwardPath G T τ₁ τ₂ x y where
  tau_nonneg := p.tau_nonneg
  tau_lt := p.tau_lt.trans q.tau_lt
  base_time := p.base_time
  endpoint_time := q.endpoint_time
  curve := γ
  curve_start := (hleft τ₁ ha.le).trans p.curve_start
  curve_end := (hright τ₂ hb.le).trans q.curve_end
  curve_time := hclock
  curve_continuous := hcont
  curve_regular := hγ
  horizontal_velocity := projectedCurveVelocity G γ
  derivative_eq := by
    intro s hs
    apply projectedCurveVelocity_derivative_eq (T := T)
      (((hγ s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt (by simp))
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact hclock t (Ioo_subset_Icc_self ht)
  action_integrable := joinedCurve_action_integrable hM12 p q γ ha hac hcb hb hγ hleft hright

theorem action_pathOfC1Join (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (p : M14BackwardPath G T τ₁ c x z₁) (q : M14BackwardPath G T c τ₂ z₂ y)
    (γ : ℝ → G.Point) {a b : ℝ}
    (ha : τ₁ < a) (hac : a < c) (hcb : c < b) (hb : b < τ₂)
    (hcont : ContinuousOn γ (Icc τ₁ τ₂))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 γ (Ioo τ₁ τ₂))
    (hclock : ∀ t ∈ Icc τ₁ τ₂, G.spacetime.timeFunction (γ t) = T - t)
    (hleft : ∀ t ≤ a, γ t = p.curve t) (hright : ∀ t, b ≤ t → γ t = q.curve t) :
    M14BackwardLAction G (pathOfC1Join hM12 p q γ ha hac hcb hb hcont hγ hclock hleft hright) =
      (∫ t in τ₁..a, M14BackwardLIntegrand G p t) +
        (∫ t in a..b, M14RawLIntegrand G γ (projectedCurveVelocity G γ) t) +
        ∫ t in b..τ₂, M14BackwardLIntegrand G q t := by
  let F := M14RawLIntegrand G γ (projectedCurveVelocity G γ)
  have hab : a < b := hac.trans hcb
  have hwhole := joinedCurve_action_integrable hM12 p q γ ha hac hcb hb hγ hleft hright
  have ht : τ₁ < τ₂ := p.tau_lt.trans q.tau_lt
  have hleftI : IntervalIntegrable F volume τ₁ a := hwhole.mono_set (by
    rw [uIcc_of_le ha.le, uIcc_of_le ht.le]
    exact Icc_subset_Icc_right (hab.le.trans hb.le))
  have hmiddleI : IntervalIntegrable F volume a b := hwhole.mono_set (by
    rw [uIcc_of_le hab.le, uIcc_of_le ht.le]
    exact Icc_subset_Icc ha.le hb.le)
  have hrightI : IntervalIntegrable F volume b τ₂ := hwhole.mono_set (by
    rw [uIcc_of_le hb.le, uIcc_of_le ht.le]
    exact Icc_subset_Icc_left (ha.le.trans hab.le))
  have hleftEq : (∫ t in τ₁..a, F t) = ∫ t in τ₁..a, M14BackwardLIntegrand G p t := by
    apply intervalIntegral.integral_congr_Ioo_of_le ha.le
    intro s hs
    apply rawLIntegrand_eq_backward_of_eventuallyEq p ⟨hs.1, hs.2.trans hac⟩
    filter_upwards [gt_mem_nhds hs.2] with t ht
    exact hleft t ht.le
  have hrightEq : (∫ t in b..τ₂, F t) = ∫ t in b..τ₂, M14BackwardLIntegrand G q t := by
    apply intervalIntegral.integral_congr_Ioo_of_le hb.le
    intro s hs
    apply rawLIntegrand_eq_backward_of_eventuallyEq q ⟨hcb.trans hs.1, hs.2⟩
    filter_upwards [lt_mem_nhds hs.1] with t ht
    exact hright t ht.le
  change (∫ t in τ₁..τ₂, F t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hleftI.trans hmiddleI) hrightI,
    ← intervalIntegral.integral_add_adjacent_intervals hleftI hmiddleI, hleftEq, hrightEq]

end PoincareConjecture.M14
