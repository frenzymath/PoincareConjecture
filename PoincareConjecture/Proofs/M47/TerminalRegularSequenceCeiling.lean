import PoincareConjecture.Proofs.M47.TerminalRegularRetainedCeiling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem terminalSource_regular_sequence_ceiling
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (F : ℕ → SurgeryFlowData.{u}) (O : ∀ n, SurgeryObservation (F n))
    (W : ∀ n, M33RegularHistoryWindow (F n)) (H : ∀ n, M33RegularHistoryData (W n))
    (base r delta : ℕ → ℝ) (ht : ∀ n, base n ∈ (H n).generalized.interval)
    (x : ∀ n, ((H n).generalized.slice (base n)).carrier)
    (old : ∀ n, SurgeryPrefixControls p (F n) (O n))
    (hBase : ∀ n, base n ∈ Ico (surgeryEpochStart p.i) (O n).H)
    (hPinched : ∀ n, SurgeryFlowPinched (F n))
    (hEarlier : ∀ n, SurgeryCanonicalOn (F n) (Ico 0 (base n)) (r n))
    (hFloor : ∀ n, (r n)⁻¹ ^ 2 ≤ ((F n).connection (base n)).scalarCurvature
      ((H n).history.forward (base n) (ht n) (x n)))
    (hOverlap : ∀ n t, t ∈ surgeryObservationInterval (O n) ∩
      Ico (surgeryEpochStart (p.i - 1)) (O n).H → (F n).parameters.delta t ≤ delta n)
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hDiverges : Tendsto (fun n => ((F n).connection (base n)).scalarCurvature
      ((H n).history.forward (base n) (ht n) (x n))) atTop atTop)
    (A tau0 K : ℕ → ℝ) (hA : ∀ j, 0 < A j) (htau0 : ∀ j, 0 < tau0 j)
    (hK : ∀ j, 0 ≤ K j) (hcofinal : ∀ a : ℝ, 0 < a → ∃ j, a ≤ A j)
    {rvol vvol : ℝ} (hrvol : 0 < rvol) (hvvol : 0 < vvol) :
    let Q : ℕ → ℝ := fun n => (H n).generalized.scalar ⟨base n, x n⟩
    let center := fun n => (H n).history.forward (base n) (ht n) (x n)
    (∀ᶠ n in atTop, ENNReal.ofReal (vvol / Real.sqrt (Q n) ^ 3) ≤
      calibratedMetricVolume ((H n).generalized.metric (base n))
        (((H n).generalized.metric (base n)).ball (x n) (rvol / Real.sqrt (Q n)))) →
    ∀ alpha : ℕ → ℕ, StrictMono alpha →
    (∀ k j, j ≤ k →
      ∃ e : SurgeryFlowCylinder (F (alpha k)) ((F (alpha k)).slice (base (alpha k)))
        (base (alpha k)) (Q (alpha k)) (Icc (-(tau0 j)) 0)
        (terminalRegularStageSource (F (alpha k)) (base (alpha k)) (Q (alpha k)) (A j)
          (center (alpha k))),
        (∀ hs z, z ∈ terminalRegularStageSource (F (alpha k)) (base (alpha k))
          (Q (alpha k)) (A j) (center (alpha k)) → HEq (e.forward 0 hs z) z) ∧
        ∀ s hs z, z ∈ terminalRegularStageSource (F (alpha k)) (base (alpha k))
          (Q (alpha k)) (A j) (center (alpha k)) →
          ((F (alpha k)).connection (base (alpha k) + s / Q (alpha k))).curvatureTensorNorm
            (e.forward s hs z) ≤ K j * Q (alpha k)) →
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∃ K0 : ℝ, 1 ≤ K0 ∧
      ∀ a : ℝ, 0 < a → ∀ᶠ k in atTop,
        ∀ z ∈ ((F (nu k)).metric (base (nu k))).ball (center (nu k))
            (a / Real.sqrt (Q (nu k))),
          ((F (nu k)).connection (base (nu k))).scalarCurvature z ≤ (2 * K0) * Q (nu k) := by
  dsimp only
  intro hvolume alpha halpha hsource
  obtain ⟨xi, hxi, K0, hK0, hceiling, _hcompact⟩ := terminalSource_regular_retained_ceiling
    P S B p hp F O W H base r delta ht x old hBase hPinched hEarlier hFloor hOverlap
    hdelta hDiverges A tau0 K hA htau0 hK hcofinal hrvol hvvol hvolume alpha halpha hsource
  exact ⟨alpha ∘ xi, halpha.comp hxi, K0, hK0, hceiling⟩

end PoincareConjecture.M47
