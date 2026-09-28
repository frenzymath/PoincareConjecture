import PoincareConjecture.Proofs.M47.SeedLowTest
import PoincareConjecture.Proofs.M47.SeedPositiveSafeVolume
import PoincareConjecture.Proofs.M47.SeedSmallVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47 M46

theorem exists_positive_low_center_volume_constant
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ k : ℝ, 0 < k ∧ ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          ObservedInputs p rNext cutoff F O →
          ∀ T : ℝ, T ∈ surgeryObservationInterval O → surgeryEpochStart p.i ≤ T →
            ∀ x : (F.slice T).carrier, SurgeryPositiveComponentAt F T x →
              (F.connection T).scalarCurvature x ≤ rNext⁻¹ ^ 2 →
              ∀ r : ℝ, 0 < r → r ≤ p.setup.epsilon →
                ∀ test : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
                  ((F.metric T).ball x r),
                  (∀ hs y, y ∈ (F.metric T).ball x r → HEq (test.forward 0 hs y) y) →
                  (∀ s hs y, y ∈ (F.metric T).ball x r →
                    (F.connection (T + s / 1)).curvatureTensorNorm
                      (test.forward s hs y) ≤ r⁻¹ ^ 2) →
                  ENNReal.ofReal (k * r ^ 3) ≤
                    calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  obtain ⟨kLarge, hkLarge, large⟩ := exists_positive_large_test_volume_constant P S p hp
  let k := min kLarge (smallBallLoss * kLarge)
  have hk : 0 < k := lt_min hkLarge (mul_pos smallBallLoss_pos hkLarge)
  refine ⟨k, hk, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨rho, hrho, hrhoNext, deltaLow, hdeltaLow, hlowLast, low⟩ :=
    exists_seed_low_center_test P S p hp hrNext hrLast
  obtain ⟨deltaLarge, hdeltaLarge, _hlargeLast, volume⟩ :=
    large rNext rho hrNext hrLast hrho
  let cutoff := min deltaLow deltaLarge
  have hsmallLow : cutoff ≤ deltaLow := min_le_left _ _
  have hsmallLarge : cutoff ≤ deltaLarge := min_le_right _ _
  refine ⟨cutoff, lt_min hdeltaLow hdeltaLarge, hsmallLow.trans hlowLast, ?_⟩
  intro F O inputs T hTO hTi x hpositive hlow r hr hrEpsilon test hbased hcurv
  have hT : 0 < T := (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 32)
    (epochStart_ge_initial p.i)).trans_le hTi
  have hTF : T ∈ F.time_domain := O.interval_subset hTO
  by_cases hlarge : rho ≤ r
  · have hvolume := volume F O (inputs.cutoff_mono hsmallLarge) T hT hTF hTO hTi
      x hpositive r hr hrEpsilon hlarge test hbased hcurv
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_left kLarge (smallBallLoss * kLarge)) (pow_nonneg hr.le 3))).trans hvolume
  · obtain ⟨e, hebased, hecurv⟩ := low F O (inputs.cutoff_mono hsmallLow) T hTO hTi x hlow
    have hsubset : (F.metric T).ball x rho ⊆ (F.metric T).ball x (2 * rho) := by
      intro y hy
      exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith only [hrho]))
    let eSmall := e.restrict (Subset.refl (Icc (-rho ^ 2) 0)) ordConnected_Icc hsubset
    have hrhoEpsilon : rho ≤ p.setup.epsilon :=
      hrhoNext.trans (hrLast.trans (p.r_le_epsilon _))
    have hvolume := volume F O (inputs.cutoff_mono hsmallLarge) T hT hTF hTO hTi
      x hpositive rho hrho hrhoEpsilon le_rfl eSmall
      (fun hs y hy => hebased hs y (hsubset hy))
      (fun s hs y hy => hecurv s hs y (hsubset hy))
    have hsmall := seed_small_volume_of_larger_cylinder hTF x hrho hr
      (le_of_not_ge hlarge) hkLarge e hebased hecurv hvolume
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_right kLarge (smallBallLoss * kLarge)) (pow_nonneg hr.le 3))).trans hsmall

end PoincareConjecture.Proofs.M47
