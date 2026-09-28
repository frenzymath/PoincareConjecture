import PoincareConjecture.Statements.M51GlobalSchedule
import PoincareConjecture.Proofs.M51.InductionPreparation
import PoincareConjecture.Proofs.M51.GlobalAssembly

































set_option autoImplicit false

universe u

namespace PoincareConjecture




theorem repairedGlobalSchedule : RepairedGlobalScheduleTheory.{u} := by
  constructor
  intro _m28 m34 m35 m36 m44 _m15 _m43 m45 m46 m47 m48 P m49 m50 epsilon hepsilon
  obtain ⟨S₀, hsmall⟩ := m45.schedules m34 m35 m36 m44 epsilon hepsilon
  obtain ⟨d, hd, B, N, C, _E, _hupper, hseed, _hstandard, _hconstants,
      hsetupEpsilon, losses, count⟩ :=
    m51InductionPreparation S₀ P m49 m46 m47 m48
  let S := (S₀.calibrateForEpoch B).restrictDelta d hd
  let A : M48AnalyticCalibration S := (S₀.epochCalibration B).restrictDelta d hd
  have hcutoff : (M51Numerical.schedule S N C).Delta 0 ≤ d := hseed
  refine ⟨S.constants, M51Numerical.schedule S N C, ?_, ?_, ?_⟩
  · change 2 * S.setup.epsilon ≤ epsilon
    rw [hsetupEpsilon]
    exact hsmall
  · intro delta _hmono _hpositive hcut F H pref
    exact M51.givenPrefixAssembly S N C A P m50 d hcutoff losses count
      delta hcut F H pref
  · intro M _ _ _ _ _ _ _ _ _ _ I hRP delta hmono hpositive hcut
    exact M51.normalizedFlowAssembly S N C A P m50 d hcutoff losses count
      I hRP delta hmono hpositive hcut

end PoincareConjecture
