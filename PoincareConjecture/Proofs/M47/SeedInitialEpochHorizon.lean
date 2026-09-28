import PoincareConjecture.Proofs.M47.SeedFirstFailureObservation










set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47



theorem seed_high_point_after_initial_epoch
    (S : RepairedControlledSchedulesData.{u}) (F : SurgeryFlowData.{u})
    {t r : ℝ} (ht : t ∈ F.time_domain) (hr : 0 < r) (hsmall : r ≤ 1 / 200)
    (x : (F.slice t).carrier)
    (hhigh : r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x) :
    1 / 16 < t := by
  by_contra hnot
  have hscalar := ((S.calibration.initial_capture F).2 t ht (le_of_not_gt hnot) x).2.1
  have hinverse : (200 : ℝ) ≤ r⁻¹ := by
    simpa using one_div_le_one_div_of_le hr hsmall
  have hlarge : (40000 : ℝ) ≤ r⁻¹ ^ 2 := by nlinarith
  have hupper := (le_abs_self ((F.connection t).scalarCurvature x)).trans hscalar
  linarith



theorem seed_high_point_after_first_prefix
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants)
    (hi : p.i = 1) (F : SurgeryFlowData.{u}) {t rNext : ℝ}
    (ht : t ∈ F.time_domain) (hr : 0 < rNext)
    (hlast : rNext ≤ p.r (Fin.last p.i)) (x : (F.slice t).carrier)
    (hhigh : rNext⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x) :
    surgeryEpochStart p.i < t := by
  have hsmall : rNext ≤ 1 / 200 :=
    hlast.trans ((p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _)))
  have h := seed_high_point_after_initial_epoch S F ht hr hsmall x hhigh
  simpa only [hi, surgeryEpochStart, pow_one, show (2 : ℝ) / 32 = 1 / 16 by norm_num]
    using h



theorem seed_initial_epoch_volume
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants)
    (hp : S.SeedCompatible p) (hi : p.i = 1)
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
    (old : SurgeryPrefixControls p F O) :
    SurgeryVolumeControlOn F (Icc 0 (surgeryEpochStart p.i)) S.kappa0
      (fun _ _ => True) := by
  intro t htime ht x _ r hr hepsilon _ _ _
  have htInitial : t ≤ 1 / 16 := by
    simpa only [hi, surgeryEpochStart, pow_one, show (2 : ℝ) / 32 = 1 / 16 by norm_num]
      using htime.2
  have hrSetup : r ≤ S.setup.epsilon := by
    rwa [old.epsilon_eq, hp.setup_eq] at hepsilon
  exact ((S.calibration.initial_capture F).2 t ht htInitial x).2.2 r hr hrSetup

end PoincareConjecture.Proofs.M47
