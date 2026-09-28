import PoincareConjecture.Proofs.M14.Sec6_1_InteriorDensity











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}




theorem rawLIntegrand_eq_backward_of_eventuallyEq
    (p : M14BackwardPath G T τ₁ τ₂ x y) {γ : ℝ → G.Point} {s : ℝ}
    (hs : s ∈ Ioo τ₁ τ₂) (h : γ =ᶠ[𝓝 s] p.curve) :
    M14RawLIntegrand G γ (projectedCurveVelocity G γ) s = M14BackwardLIntegrand G p s := by
  rw [rawLIntegrand_projectedVelocity_congr h]
  unfold M14BackwardLIntegrand M14RawLIntegrand
  rw [backwardPath_velocity_eq_projected p hs]



theorem rawLIntegrand_eq_outside_compact (p : M14BackwardPath G T τ₁ τ₂ x y)
    {γ : ℝ → G.Point} {a b : ℝ} (houtside : ∀ t ∉ Icc a b, γ t = p.curve t)
    {s : ℝ} (hs : s ∈ Ioo τ₁ τ₂) (hsab : s ∉ Icc a b) :
    M14RawLIntegrand G γ (projectedCurveVelocity G γ) s = M14BackwardLIntegrand G p s := by
  apply rawLIntegrand_eq_backward_of_eventuallyEq p hs
  filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hsab] with t ht
  exact houtside t ht




theorem compactPerturbation_action_integrable (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (p : M14BackwardPath G T τ₁ τ₂ x y) (γ : ℝ → G.Point) {a b : ℝ}
    (ha : τ₁ < a) (hab : a < b) (hb : b < τ₂)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 γ (Ioo τ₁ τ₂))
    (houtside : ∀ t ∉ Icc a b, γ t = p.curve t) :
    IntervalIntegrable (M14RawLIntegrand G γ (projectedCurveVelocity G γ)) volume τ₁ τ₂ := by
  have hmiddle : IntervalIntegrable (M14RawLIntegrand G γ (projectedCurveVelocity G γ))
      volume a b := ((rawLIntegrand_projectedVelocity_continuousOn hM12 isOpen_Ioo hγ).mono
        (fun _ ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩)).intervalIntegrable_of_Icc hab.le
  have hleftOld := p.action_integrable.mono_set
    (show uIcc τ₁ a ⊆ uIcc τ₁ τ₂ by
      rw [uIcc_of_le ha.le, uIcc_of_le p.tau_lt.le]
      exact Icc_subset_Icc_right (hab.le.trans hb.le))
  have hleft : IntervalIntegrable (M14RawLIntegrand G γ (projectedCurveVelocity G γ))
      volume τ₁ a := hleftOld.congr_uIoo (by
    intro s hs
    rw [uIoo_of_le ha.le] at hs
    exact (rawLIntegrand_eq_outside_compact p houtside
      ⟨hs.1, hs.2.trans (hab.trans hb)⟩ (fun h => (not_le_of_gt hs.2) h.1)).symm)
  have hrightOld := p.action_integrable.mono_set
    (show uIcc b τ₂ ⊆ uIcc τ₁ τ₂ by
      rw [uIcc_of_le hb.le, uIcc_of_le p.tau_lt.le]
      exact Icc_subset_Icc_left (ha.le.trans hab.le))
  have hright : IntervalIntegrable (M14RawLIntegrand G γ (projectedCurveVelocity G γ))
      volume b τ₂ := hrightOld.congr_uIoo (by
    intro s hs
    rw [uIoo_of_le hb.le] at hs
    exact (rawLIntegrand_eq_outside_compact p houtside
      ⟨(ha.trans hab).trans hs.1, hs.2⟩ (fun h => (not_le_of_gt hs.1) h.2)).symm)
  exact hleft.trans (hmiddle.trans hright)



noncomputable def pathOfCompactPerturbation (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (p : M14BackwardPath G T τ₁ τ₂ x y) (γ : ℝ → G.Point) {a b : ℝ}
    (ha : τ₁ < a) (hab : a < b) (hb : b < τ₂)
    (hcont : ContinuousOn γ (Icc τ₁ τ₂))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 γ (Ioo τ₁ τ₂))
    (hclock : ∀ t ∈ Icc τ₁ τ₂, G.spacetime.timeFunction (γ t) = T - t)
    (houtside : ∀ t ∉ Icc a b, γ t = p.curve t) : M14BackwardPath G T τ₁ τ₂ x y where
  tau_nonneg := p.tau_nonneg
  tau_lt := p.tau_lt
  base_time := p.base_time
  endpoint_time := p.endpoint_time
  curve := γ
  curve_start := (houtside τ₁ (fun h => (not_le_of_gt ha) h.1)).trans p.curve_start
  curve_end := (houtside τ₂ (fun h => (not_le_of_gt hb) h.2)).trans p.curve_end
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
  action_integrable := compactPerturbation_action_integrable hM12 p γ ha hab hb hγ houtside



theorem action_pathOfCompactPerturbation (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (p : M14BackwardPath G T τ₁ τ₂ x y) (γ : ℝ → G.Point) {a b : ℝ}
    (ha : τ₁ < a) (hab : a < b) (hb : b < τ₂)
    (hcont : ContinuousOn γ (Icc τ₁ τ₂))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 γ (Ioo τ₁ τ₂))
    (hclock : ∀ t ∈ Icc τ₁ τ₂, G.spacetime.timeFunction (γ t) = T - t)
    (houtside : ∀ t ∉ Icc a b, γ t = p.curve t) :
    M14BackwardLAction G (pathOfCompactPerturbation hM12 p γ ha hab hb hcont hγ hclock houtside) =
      (∫ t in τ₁..a, M14BackwardLIntegrand G p t) +
        (∫ t in a..b, M14RawLIntegrand G γ (projectedCurveVelocity G γ) t) +
        ∫ t in b..τ₂, M14BackwardLIntegrand G p t := by
  let f := M14RawLIntegrand G γ (projectedCurveVelocity G γ)
  have hint := compactPerturbation_action_integrable hM12 p γ ha hab hb hγ houtside
  have hleft : IntervalIntegrable f volume τ₁ a := hint.mono_set (by
    rw [uIcc_of_le ha.le, uIcc_of_le p.tau_lt.le]
    exact Icc_subset_Icc_right (hab.le.trans hb.le))
  have hmiddle : IntervalIntegrable f volume a b := hint.mono_set (by
    rw [uIcc_of_le hab.le, uIcc_of_le p.tau_lt.le]
    exact Icc_subset_Icc ha.le hb.le)
  have hright : IntervalIntegrable f volume b τ₂ := hint.mono_set (by
    rw [uIcc_of_le hb.le, uIcc_of_le p.tau_lt.le]
    exact Icc_subset_Icc_left (ha.le.trans hab.le))
  have hleftEq : (∫ t in τ₁..a, f t) = ∫ t in τ₁..a, M14BackwardLIntegrand G p t :=
    intervalIntegral.integral_congr_Ioo_of_le ha.le (fun s hs =>
      rawLIntegrand_eq_outside_compact p houtside ⟨hs.1, hs.2.trans (hab.trans hb)⟩
        (fun h => (not_le_of_gt hs.2) h.1))
  have hrightEq : (∫ t in b..τ₂, f t) = ∫ t in b..τ₂, M14BackwardLIntegrand G p t :=
    intervalIntegral.integral_congr_Ioo_of_le hb.le (fun s hs =>
      rawLIntegrand_eq_outside_compact p houtside ⟨(ha.trans hab).trans hs.1, hs.2⟩
        (fun h => (not_le_of_gt hs.1) h.2))
  change (∫ t in τ₁..τ₂, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmiddle) hright,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hmiddle, hleftEq, hrightEq]



theorem middleAction_le_compactPerturbation (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (p : M14BackwardPath G T τ₁ τ₂ x y) (hmin : M14IsMinimizing p)
    (γ : ℝ → G.Point) {a b : ℝ} (ha : τ₁ < a) (hab : a < b) (hb : b < τ₂)
    (hcont : ContinuousOn γ (Icc τ₁ τ₂))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 γ (Ioo τ₁ τ₂))
    (hclock : ∀ t ∈ Icc τ₁ τ₂, G.spacetime.timeFunction (γ t) = T - t)
    (houtside : ∀ t ∉ Icc a b, γ t = p.curve t) :
    (∫ t in a..b, M14BackwardLIntegrand G p t) ≤
      ∫ t in a..b, M14RawLIntegrand G γ (projectedCurveVelocity G γ) t := by
  have hleft := p.action_integrable.mono_set (show uIcc τ₁ a ⊆ uIcc τ₁ τ₂ by
    rw [uIcc_of_le ha.le, uIcc_of_le p.tau_lt.le]
    exact Icc_subset_Icc_right (hab.le.trans hb.le))
  have hmiddle := p.action_integrable.mono_set (show uIcc a b ⊆ uIcc τ₁ τ₂ by
    rw [uIcc_of_le hab.le, uIcc_of_le p.tau_lt.le]
    exact Icc_subset_Icc ha.le hb.le)
  have hright := p.action_integrable.mono_set (show uIcc b τ₂ ⊆ uIcc τ₁ τ₂ by
    rw [uIcc_of_le hb.le, uIcc_of_le p.tau_lt.le]
    exact Icc_subset_Icc_left (ha.le.trans hab.le))
  change IntervalIntegrable (M14BackwardLIntegrand G p) volume τ₁ a at hleft
  change IntervalIntegrable (M14BackwardLIntegrand G p) volume a b at hmiddle
  change IntervalIntegrable (M14BackwardLIntegrand G p) volume b τ₂ at hright
  have hineq := hmin (pathOfCompactPerturbation hM12 p γ ha hab hb hcont hγ hclock houtside)
  rw [action_pathOfCompactPerturbation, M14BackwardLAction,
    ← intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmiddle) hright,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hmiddle] at hineq
  linarith

end PoincareConjecture.M14
