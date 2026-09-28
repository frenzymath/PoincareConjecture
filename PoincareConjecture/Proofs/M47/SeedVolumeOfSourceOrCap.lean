import PoincareConjecture.Proofs.M47.SeedPreliminaryVolume










set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M47

theorem seed_preliminary_sequence_terminal_volume_of_source_or_cap
    (F : ℕ → SurgeryFlowData.{u}) (W : ∀ n, M33RegularHistoryWindow (F n))
    (H : ∀ n, M33RegularHistoryData (W n)) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ (H n).generalized.interval)
    (x : ∀ n, ((H n).generalized.slice (t n)).carrier)
    (hPositive : ∀ n, 0 < ((F n).connection (t n)).scalarCurvature
      ((H n).history.forward (t n) (ht n) (x n)))
    (hDiverges : Tendsto (fun n => ((F n).connection (t n)).scalarCurvature
      ((H n).history.forward (t n) (ht n) (x n))) atTop atTop)
    {k A tau K epsilon : ℝ} (hk : 0 < k) (hA : 0 < A)
    (htau : 0 < tau) (hK : 0 ≤ K) (hepsilon : 0 < epsilon)
    (hEpsilon : ∀ n, (F n).parameters.epsilon = epsilon)
    (J : ℕ → Set ℝ)
    (hVolume : ∀ᶠ n in atTop,
      SurgeryVolumeControlOn (F n) (J n) k (fun _ _ => True) ∧ t n ∈ J n)
    (capBranch : ℕ → Prop)
    (hsearch : ∀ᶠ n in atTop,
      (∃ e : SurgeryFlowCylinder (F n) ((F n).slice (t n)) (t n)
          ((H n).generalized.scalar ⟨t n, x n⟩) (Icc (-tau) 0)
          (((F n).metric (t n)).ball ((H n).history.forward (t n) (ht n) (x n))
            (A / Real.sqrt ((H n).generalized.scalar ⟨t n, x n⟩))),
        (∀ hs y, y ∈ ((F n).metric (t n)).ball ((H n).history.forward (t n) (ht n) (x n))
            (A / Real.sqrt ((H n).generalized.scalar ⟨t n, x n⟩)) →
          HEq (e.forward 0 hs y) y) ∧
        ∀ s hs y, y ∈ ((F n).metric (t n)).ball ((H n).history.forward (t n) (ht n) (x n))
            (A / Real.sqrt ((H n).generalized.scalar ⟨t n, x n⟩)) →
          ((F n).connection (t n + s / (H n).generalized.scalar ⟨t n, x n⟩)).curvatureTensorNorm
            (e.forward s hs y) ≤ K * (H n).generalized.scalar ⟨t n, x n⟩) ∨
      capBranch n)
    (hnoCap : ∀ᶠ n in atTop, ¬ capBranch n) :
    let V := PoincareConjecture.M47.regularHistoryBlowupSequence F W H t ht x hPositive hDiverges
    ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (v / (Real.sqrt (V.scale n)) ^ 3) ≤
        calibratedMetricVolume ((V.flow n).metric (V.base n).1) (V.baseBall n rho) := by
  intro V
  have cylinders : ∀ᶠ n in atTop,
      ∃ e : SurgeryFlowCylinder (F n) ((F n).slice (t n)) (t n) (V.scale n)
          (Icc (-tau) 0) (((F n).metric (t n)).ball
            ((H n).history.forward (t n) (ht n) (x n)) (A / Real.sqrt (V.scale n))),
        (∀ h y, y ∈ ((F n).metric (t n)).ball
          ((H n).history.forward (t n) (ht n) (x n)) (A / Real.sqrt (V.scale n)) →
            HEq (e.forward 0 h y) y) ∧
        ∀ s hs y, y ∈ ((F n).metric (t n)).ball
            ((H n).history.forward (t n) (ht n) (x n)) (A / Real.sqrt (V.scale n)) →
          ((F n).connection (t n + s / V.scale n)).curvatureTensorNorm
            (e.forward s hs y) ≤ K * V.scale n := by
    filter_upwards [hsearch, hnoCap] with n hn hc
    exact hn.resolve_right hc
  exact seed_preliminary_sequence_terminal_volume F W H t ht x hPositive hDiverges
    hk hA htau hK hepsilon hEpsilon J hVolume cylinders

end PoincareConjecture.Proofs.M47
