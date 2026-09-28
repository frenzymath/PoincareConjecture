import PoincareConjecture.Proofs.M47.BlowupControlsSourceSearch
import PoincareConjecture.Proofs.M47.GeneralizedBridgeDense
import PoincareConjecture.Proofs.M33.GuardedCylinders










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem search_terminal_scalar_of_bounded_distance
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {base Q a A D : ℝ}
    (ht : base ∈ H.generalized.interval) (hQ : 0 < Q) (ha : a < 0)
    (x : (H.generalized.slice base).carrier)
    (hscale : H.generalized.scalar ⟨base, x⟩ = Q)
    (e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0)
      ((F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q)))
    (hbased : ∀ hs y,
      y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) →
        HEq (e.forward 0 hs y) y)
    (hestimate : RepairedBoundedDistanceEstimate H.generalized A D base x) :
    ∀ y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q),
      (F.connection base).scalarCurvature y ≤ D * Q := by
  have hzero : (0 : ℝ) ∈ Icc a 0 := ⟨ha.le, le_rfl⟩
  have hreg := e.regular_image_of_earlier hzero ⟨a, ⟨le_rfl, ha.le⟩, ha⟩
  have hball : (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) ⊆
      range (H.history.forward base ht) := by
    rw [H.regular_range]
    intro y hy
    have hp : (⟨base + 0 / Q, e.forward 0 hzero y⟩ : Σ s, (F.slice s).carrier) =
        ⟨base, y⟩ := Sigma.ext (by simp) (hbased hzero y hy)
    exact (congrArg (fun p : Σ s, (F.slice s).carrier =>
      p.2 ∈ m33RegularRegion F p.1) hp).mp (hreg ⟨y, hy, rfl⟩)
  have himage := H.history.ball_image_of_subset base ht x (A / Real.sqrt Q) hball
  have hradius : A / Real.sqrt Q = A * Q ^ (-1 / 2 : ℝ) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hQ.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  intro y hy
  obtain ⟨z, hz, rfl⟩ := himage.symm ▸ hy
  rw [H.scalar_pullback]
  have h := hestimate z (by simpa only [hscale, hradius] using hz)
  rw [hscale] at h
  exact h



theorem exists_search_terminal_scalar_bound
    (S : RepairedControlledSchedulesData.{u}) {epsilon C A : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ S.calibration.epsilon₁₀)
    (hC : 0 < C) (hA : 0 ≤ A) :
    ∃ D0 D : ℝ, 0 < D0 ∧ 0 < D ∧
      ∀ (F : SurgeryFlowData.{u}) (W : M33RegularHistoryWindow F)
        (H : M33RegularHistoryData W) {base Q r a : ℝ}
        (ht : base ∈ H.generalized.interval), 0 < base → 0 < Q → a < 0 →
      F.parameters.epsilon = epsilon → F.parameters.C = C →
      SurgeryFlowPinched F → SurgeryCanonicalOn F (Ico 0 base) r →
      r⁻¹ ^ 2 ≤ Q → ∀ x : (H.generalized.slice base).carrier,
      H.generalized.scalar ⟨base, x⟩ = Q → D0 ≤ Q →
      ∀ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0)
        ((F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q)),
      (∀ hs y,
        y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) →
          HEq (e.forward 0 hs y) y) →
      ∀ y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q),
        (F.connection base).scalarCurvature y ≤ D * Q := by
  obtain ⟨D0, D, hD0, hD, estimate⟩ :=
    exists_regular_history_bounded_distance S epsilon hepsilon hepsilonSmall C hC A hA
  refine ⟨D0, D, hD0, hD, ?_⟩
  intro F W H base Q r a ht htpos hQ ha he hCeq hpinch hpast hthreshold x hscale
    hlarge e hbased
  apply search_terminal_scalar_of_bounded_distance H ht hQ ha x hscale e hbased
  apply estimate F W H (fun s hs => hpinch s (W.time_subset hs)) base ht htpos x
    (by simpa only [hscale] using hlarge)
  intro s hs hsb _hregular y hy
  have hQle : Q ≤ (F.connection s).scalarCurvature y := by
    rw [hscale] at hy
    linarith only [hy, hQ]
  have hc := hpast s ⟨F.time_domain_nonnegative (W.time_subset hs), hsb⟩
    (W.time_subset hs) y (hthreshold.trans hQle)
  simpa only [he, hCeq] using hc

end PoincareConjecture.M47
