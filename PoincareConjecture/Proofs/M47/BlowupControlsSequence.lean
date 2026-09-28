import PoincareConjecture.Proofs.M47.GeneralizedBridgeDense

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (H : ∀ k, M33RegularHistoryData (W k)) (t : ℕ → ℝ)
  (ht : ∀ k, t k ∈ (H k).generalized.interval)
  (x : ∀ k, ((H k).generalized.slice (t k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (t k)).scalarCurvature
    ((H k).history.forward (t k) (ht k) (x k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (t k)).scalarCurvature
    ((H k).history.forward (t k) (ht k) (x k))) atTop atTop)

noncomputable def regularHistoryBlowupSequence : GeneralizedBlowupSequence.{u} where
  flow k := (H k).generalized
  base k := ⟨t k, x k⟩
  base_scalar_pos k := by
    simpa only [GeneralizedRicciFlowData.scalar, (H k).scalar_pullback (t k) (ht k)]
      using hPositive k
  scalar_diverges := by
    simpa only [GeneralizedRicciFlowData.scalar, (H _).scalar_pullback] using hDiverges

theorem regular_history_blowup_bounded_distance
    (S : RepairedControlledSchedulesData.{u}) {epsilon C : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon₀ : epsilon ≤ S.calibration.epsilon₁₀)
    (hC : 0 < C) (htPositive : ∀ k, 0 < t k)
    (hPinched : ∀ k, ∀ s ∈ (W k).interval, SurgeryPinchedAt ((F k).connection s) s)
    (hCanonical : ∀ k, ∀ s ∈ (W k).interval, s < t k → s ∉ (F k).surgery_times →
      ∀ y : ((F k).slice s).carrier,
        4 * (H k).generalized.scalar ⟨t k, x k⟩ ≤ ((F k).connection s).scalarCurvature y →
          SurgeryCanonicalControl (F k) s y epsilon C) :
    GeneralizedBlowupBoundedDistance
      (regularHistoryBlowupSequence F W H t ht x hPositive hDiverges) := by
  let V := regularHistoryBlowupSequence F W H t ht x hPositive hDiverges
  intro A hA
  obtain ⟨D₀, D, _hD₀, hD, hEstimate⟩ :=
    exists_regular_history_bounded_distance S epsilon hepsilon hepsilon₀ C hC A hA.le
  refine ⟨D, hD, ?_⟩
  have hLarge : ∀ᶠ k in atTop, D₀ ≤ V.scale k :=
    V.scalar_diverges.eventually (eventually_ge_atTop D₀)
  filter_upwards [hLarge] with k hk
  have h := hEstimate (F k) (W k) (H k) (hPinched k) (t k) (ht k)
    (htPositive k) (x k) hk (hCanonical k)
  intro y hy
  apply h y
  have hScale : 0 ≤ V.scale k := (V.base_scalar_pos k).le
  have hRadius : A / Real.sqrt (V.scale k) = A * V.scale k ^ (-1 / 2 : ℝ) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hScale, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  change y ∈ ((H k).generalized.metric (t k)).ball (x k)
    (A / Real.sqrt (V.scale k)) at hy
  rwa [hRadius] at hy

end PoincareConjecture.M47
