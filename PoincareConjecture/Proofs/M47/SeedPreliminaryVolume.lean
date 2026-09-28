import PoincareConjecture.Proofs.M47.SeedBlowupVolumeSequence
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction










set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_seed_blowup_test_radius_below {A tau B : ℝ}
    (hA : 0 < A) (htau : 0 < tau) (hB : 0 ≤ B) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ A ∧ rho ^ 2 ≤ tau ∧ B ≤ rho⁻¹ ^ 2 := by
  obtain ⟨r, hr, htime, hbound⟩ := exists_seed_blowup_test_radius htau hB
  let rho := min A r
  have hpositive : 0 < rho := lt_min hA hr
  have hle : rho ≤ r := min_le_right _ _
  have hinverse : r⁻¹ ≤ rho⁻¹ := (inv_le_inv₀ hr hpositive).mpr hle
  refine ⟨rho, hpositive, min_le_left _ _, ?_, ?_⟩
  · exact (pow_le_pow_left₀ hpositive.le hle 2).trans htime
  · exact hbound.trans (pow_le_pow_left₀ (inv_pos.mpr hr).le hinverse 2)



theorem seed_preliminary_sequence_terminal_volume
    (F : ℕ → SurgeryFlowData.{u}) (W : ∀ n, M33RegularHistoryWindow (F n))
    (H : ∀ n, M33RegularHistoryData (W n)) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ (H n).generalized.interval)
    (x : ∀ n, ((H n).generalized.slice (t n)).carrier)
    (hPositive : ∀ n, 0 < ((F n).connection (t n)).scalarCurvature
      ((H n).history.forward (t n) (ht n) (x n)))
    (hDiverges : Tendsto (fun n => ((F n).connection (t n)).scalarCurvature
      ((H n).history.forward (t n) (ht n) (x n))) atTop atTop)
    {k A tau B epsilon : ℝ} (hk : 0 < k) (hA : 0 < A)
    (htau : 0 < tau) (hB : 0 ≤ B) (hepsilon : 0 < epsilon)
    (hEpsilon : ∀ n, (F n).parameters.epsilon = epsilon)
    (J : ℕ → Set ℝ)
    (hVolume : ∀ᶠ n in atTop,
      SurgeryVolumeControlOn (F n) (J n) k (fun _ _ => True) ∧ t n ∈ J n) :
    let V := PoincareConjecture.M47.regularHistoryBlowupSequence F W H t ht x hPositive hDiverges
    (∀ᶠ n in atTop,
      ∃ e : SurgeryFlowCylinder (F n) ((F n).slice (t n)) (t n) (V.scale n)
          (Icc (-tau) 0) (((F n).metric (t n)).ball
            ((H n).history.forward (t n) (ht n) (x n)) (A / Real.sqrt (V.scale n))),
        (∀ h y, y ∈ ((F n).metric (t n)).ball
          ((H n).history.forward (t n) (ht n) (x n)) (A / Real.sqrt (V.scale n)) →
            HEq (e.forward 0 h y) y) ∧
        ∀ s hs y, y ∈ ((F n).metric (t n)).ball
            ((H n).history.forward (t n) (ht n) (x n)) (A / Real.sqrt (V.scale n)) →
          ((F n).connection (t n + s / V.scale n)).curvatureTensorNorm
            (e.forward s hs y) ≤ B * V.scale n) →
    ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (v / (Real.sqrt (V.scale n)) ^ 3) ≤
        calibratedMetricVolume ((V.flow n).metric (V.base n).1) (V.baseBall n rho) := by
  intro V cylinders
  obtain ⟨rho, hrho, hAor, htime, hbound⟩ :=
    exists_seed_blowup_test_radius_below hA htau hB
  refine ⟨rho, k * rho ^ 3, hrho, mul_pos hk (pow_pos hrho _), ?_⟩
  have hsmall := seed_blowup_eventually_radius_le hrho hepsilon V.scale V.scalar_diverges
  filter_upwards [hVolume, cylinders, hsmall] with n hn he hs
  obtain ⟨e, hbase, hcurv⟩ := he
  have hspace : ((F n).metric (t n)).ball
      ((H n).history.forward (t n) (ht n) (x n)) (rho / Real.sqrt (V.scale n)) ⊆
      ((F n).metric (t n)).ball
      ((H n).history.forward (t n) (ht n) (x n)) (A / Real.sqrt (V.scale n)) := by
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hAor (Real.sqrt_nonneg _)))
  let eSmall := e.restrict (Subset.refl (Icc (-tau) 0)) ordConnected_Icc hspace
  have hradius : rho / Real.sqrt (V.scale n) ≤ (F n).parameters.epsilon :=
    (hEpsilon n).symm ▸ hs.2
  exact seed_blowup_terminal_volume (H n) hn.1 hn.2 (ht n) hs.1 hrho htime hbound
    hradius (x n) eSmall (fun h y hy => hbase h y (hspace hy))
    (fun s hs y hy => hcurv s hs y (hspace hy))

end PoincareConjecture.Proofs.M47
