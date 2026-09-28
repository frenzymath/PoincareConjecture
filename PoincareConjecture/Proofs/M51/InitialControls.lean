import PoincareConjecture.Proofs.M51.Parameters
import PoincareConjecture.Proofs.M45.InitialGeometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M51Initial

variable (S : RepairedControlledSchedulesData.{u})
  (N : RepairedNoncollapseInductionData S) (C : RepairedCanonicalInductionData S N)
  (delta : ℝ → ℝ) (hmono : AntitoneOn delta (Ici 0))
  (hpos : ∀ t, 0 ≤ t → 0 < delta t)
  (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
    delta t ≤ (M51Numerical.schedule S N C).Delta j)

include hcut in

theorem prefix_controls (F : SurgeryFlowData.{u})
    (hP : F.parameters = (M51Numerical.schedule S N C).parameters delta hmono hpos)
    (hstd : F.standard_initial = S.setup.standard_initial)
    (hK : F.local_constants = S.constants) (hAd : SurgeryFlowAdmissible F)
    (hPin : SurgeryFlowPinched F) (O : SurgeryObservation F) (hH : O.H = 1 / 16) :
    SurgeryPrefixControls S.initialPrefix F O := by
  have hEps : F.parameters.epsilon = S.setup.epsilon := by rw [hP]; rfl
  have hAgreement (j : Fin (S.initialPrefix.i + 1)) :
      (M51Numerical.schedule S N C).r j.val = S.initialPrefix.r j ∧
      (M51Numerical.schedule S N C).kappa j.val = S.initialPrefix.kappa j ∧
      (M51Numerical.schedule S N C).Delta j.val ≤ S.initialPrefix.Delta j :=
    M51Numerical.prefix_agreement S N C 0 j
  have hTime {t : ℝ} (ht : t ∈ surgeryObservationInterval O) : t ≤ 1 / 16 := by
    exact (ht.2.trans_le hH.le).le
  refine {
    standard_initial_eq := hstd
    local_constants_eq := hK
    epsilon_eq := hEps
    C_eq := by rw [hP]; rfl
    admissible := hAd
    pinched := fun t _ ht => hPin t ht
    canonical := ?_
    noncollapsed := ?_
    delta_bound := ?_
    r_schedule := ?_
    kappa_schedule := ?_
    h_schedule := ?_ }
  · intro j _ t ht hDomain x hCurv
    have hScalar := ((S.calibration.initial_capture F).2 t hDomain (hTime ht.1) x).2.1
    have hInv : 200 ≤ S.setup.epsilon⁻¹ := by
      have h := one_div_le_one_div_of_le S.setup.epsilon_pos
        (S.setup.epsilon_le.trans (min_le_left _ _))
      norm_num [one_div] at h
      exact h
    change S.setup.epsilon⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x at hCurv
    exfalso
    nlinarith [le_abs_self ((F.connection t).scalarCurvature x)]
  · intro j _ t ht hDomain x _ r hr hrEps _ _ _
    exact ((S.calibration.initial_capture F).2 t hDomain (hTime ht.1) x).2.2 r hr
      (hrEps.trans_eq hEps)
  · intro j _ t ht
    rw [hP]
    exact (hcut j.val t ht.2 ht.1.1).trans (hAgreement j).2.2
  · intro j _ t ht
    rw [hP, GlobalSurgerySchedule.parameters_r _ _ _ _ ht.2]
    exact (hAgreement j).1
  · intro j _ t ht
    rw [hP, GlobalSurgerySchedule.parameters_kappa _ _ _ _ ht.2]
    exact (hAgreement j).2.1
  · intro j _ t ht
    rw [hP]
    rfl

end PoincareConjecture.M51Initial
