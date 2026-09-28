import PoincareConjecture.Proofs.M47.SeedCanonicalVolume
import PoincareConjecture.Proofs.M47.SeedLowVolume









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47 M46



theorem exists_positive_volume_or_small_component
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ k : ℝ, 0 < k ∧ ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          ObservedInputs p rNext cutoff F O →
          ∀ T : ℝ, T ∈ surgeryObservationInterval O → surgeryEpochStart p.i ≤ T →
            ∀ x : (F.slice T).carrier, SurgeryPositiveComponentAt F T x →
              ∀ r : ℝ, 0 < r → r ≤ p.setup.epsilon →
                ∀ test : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
                  ((F.metric T).ball x r),
                  (∀ hs y, y ∈ (F.metric T).ball x r → HEq (test.forward 0 hs y) y) →
                  (∀ s hs y, y ∈ (F.metric T).ball x r →
                    (F.connection (T + s / 1)).curvatureTensorNorm
                      (test.forward s hs y) ≤ r⁻¹ ^ 2) →
                  ENNReal.ofReal (k * r ^ 3) ≤
                    calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) ∨
                  (r < rNext ∧ rNext⁻¹ ^ 2 < (F.connection T).scalarCurvature x ∧
                    ((∃ N : SingularCComponent (F.metric T) (F.connection T) F.parameters.C,
                      x ∈ N.carrier) ∨
                    ∃ N : SingularRoundComponent (F.metric T) F.parameters.epsilon,
                      x ∈ N.carrier)) := by
  obtain ⟨kLow, hkLow, low⟩ := exists_positive_low_center_volume_constant P S p hp
  obtain ⟨kLarge, hkLarge, large⟩ := exists_positive_large_test_volume_constant P S p hp
  let k := min kLow (min kLarge (canonicalSeedDensity p.setup.C))
  have hk : 0 < k := lt_min hkLow (lt_min hkLarge (canonicalSeedDensity_pos _))
  refine ⟨k, hk, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨deltaLow, hdeltaLow, hlowLast, lowVolume⟩ := low rNext hrNext hrLast
  obtain ⟨deltaLarge, hdeltaLarge, _hlargeLast, largeVolume⟩ :=
    large rNext rNext hrNext hrLast hrNext
  let cutoff := min deltaLow deltaLarge
  have hlow : cutoff ≤ deltaLow := min_le_left _ _
  have hlarge : cutoff ≤ deltaLarge := min_le_right _ _
  refine ⟨cutoff, lt_min hdeltaLow hdeltaLarge, hlow.trans hlowLast, ?_⟩
  intro F O inputs T hTO hTi x hpositive r hr hrEpsilon test hbased hcurv
  have hT : 0 < T := (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 32)
    (epochStart_ge_initial p.i)).trans_le hTi
  have hTF := O.interval_subset hTO
  have hmono (k' : ℝ) (hle : k ≤ k')
      (hv : ENNReal.ofReal (k' * r ^ 3) ≤
        calibratedMetricVolume (F.metric T) ((F.metric T).ball x r)) :
      ENNReal.ofReal (k * r ^ 3) ≤
        calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (pow_nonneg hr.le 3))).trans hv
  by_cases hsmall : rNext ≤ r
  · left
    exact hmono kLarge ((min_le_right _ _).trans (min_le_left _ _))
      (largeVolume F O (inputs.cutoff_mono hlarge) T hT hTF hTO hTi x hpositive
        r hr hrEpsilon hsmall test hbased hcurv)
  · by_cases hcenter : (F.connection T).scalarCurvature x ≤ rNext⁻¹ ^ 2
    · left
      exact hmono kLow (min_le_left _ _)
        (lowVolume F O (inputs.cutoff_mono hlow) T hTO hTi x hpositive hcenter
          r hr hrEpsilon test hbased hcurv)
    · have hhigh := (lt_of_not_ge hcenter).le
      have hcanonical := inputs.canonical T hTO hTF x hhigh
      have hrsmall : rNext ≤ 1 / 200 := hrLast.trans
        ((p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _)))
      rcases canonical_test_volume_or_component P hcanonical hrNext hrsmall hhigh
          (inputs.pinched T hTF) hr test hbased hcurv with hvolume | hcomponent
      · left
        rw [inputs.old.C_eq] at hvolume
        exact hmono _ ((min_le_right _ _).trans (min_le_right _ _)) hvolume
      · exact Or.inr ⟨lt_of_not_ge hsmall, lt_of_not_ge hcenter, hcomponent⟩

end PoincareConjecture.Proofs.M47
