import PoincareConjecture.Proofs.M47.SeedBlowupVolume
import PoincareConjecture.Proofs.M47.BlowupControlsSequence









set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M47



theorem seed_blowup_sequence_terminal_volume
    (F : ℕ → SurgeryFlowData.{u}) (W : ∀ n, M33RegularHistoryWindow (F n))
    (H : ∀ n, M33RegularHistoryData (W n)) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ (H n).generalized.interval)
    (x : ∀ n, ((H n).generalized.slice (t n)).carrier)
    (hPositive : ∀ n, 0 < ((F n).connection (t n)).scalarCurvature
      ((H n).history.forward (t n) (ht n) (x n)))
    (hDiverges : Tendsto (fun n => ((F n).connection (t n)).scalarCurvature
      ((H n).history.forward (t n) (ht n) (x n))) atTop atTop)
    {k tau B epsilon : ℝ} (hk : 0 < k) (htau : 0 < tau) (hB : 0 ≤ B)
    (hepsilon : 0 < epsilon) (hEpsilon : ∀ n, (F n).parameters.epsilon = epsilon)
    (J : ℕ → Set ℝ)
    (hVolume : ∀ᶠ n in atTop,
      SurgeryVolumeControlOn (F n) (J n) k (fun _ _ => True) ∧ t n ∈ J n) :
    let V := PoincareConjecture.M47.regularHistoryBlowupSequence F W H t ht x hPositive hDiverges
    (∀ rho : ℝ, 0 < rho → ∀ᶠ n in atTop,
      ∃ e : SurgeryFlowCylinder (F n) ((F n).slice (t n)) (t n) (V.scale n)
          (Icc (-tau) 0) (((F n).metric (t n)).ball
            ((H n).history.forward (t n) (ht n) (x n)) (rho / Real.sqrt (V.scale n))),
        (∀ h y, y ∈ ((F n).metric (t n)).ball
          ((H n).history.forward (t n) (ht n) (x n)) (rho / Real.sqrt (V.scale n)) →
            HEq (e.forward 0 h y) y) ∧
        ∀ s hs y, y ∈ ((F n).metric (t n)).ball
            ((H n).history.forward (t n) (ht n) (x n)) (rho / Real.sqrt (V.scale n)) →
          ((F n).connection (t n + s / V.scale n)).curvatureTensorNorm
            (e.forward s hs y) ≤ B * V.scale n) →
    ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (v / (Real.sqrt (V.scale n)) ^ 3) ≤
        calibratedMetricVolume ((V.flow n).metric (V.base n).1) (V.baseBall n rho) := by
  intro V cylinders
  obtain ⟨rho, hrho, htime, hbound⟩ := exists_seed_blowup_test_radius htau hB
  refine ⟨rho, k * rho ^ 3, hrho, mul_pos hk (pow_pos hrho _), ?_⟩
  have hsmall := seed_blowup_eventually_radius_le hrho hepsilon V.scale V.scalar_diverges
  filter_upwards [hVolume, cylinders rho hrho, hsmall] with n hn he hs
  obtain ⟨e, hbase, hcurv⟩ := he
  have hradius : rho / Real.sqrt (V.scale n) ≤ (F n).parameters.epsilon :=
    (hEpsilon n).symm ▸ hs.2
  exact seed_blowup_terminal_volume (H n) hn.1 hn.2 (ht n) hs.1 hrho htime hbound
    hradius (x n) e hbase hcurv

end PoincareConjecture.Proofs.M47
