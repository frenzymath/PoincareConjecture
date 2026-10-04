import PoincareLib.Geometry.RicciFlow.Surgery.Global.ScheduleTheory
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Induction.InductionPreparation
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Global.GlobalAssembly
/-!
# M51 global parameter schedule induction

Natural-language theorem: for every prescribed positive bound, choose one
global schedule whose doubled setup epsilon is at most that bound. For every
already given
finite controlled flow on `[0,T)` satisfying the Definition 15.8 event policy,
source controls and schedule bounds, return a changing-carrier extension of that same flow to
`[0,∞)` preserving admissibility, pinching, canonical/noncollapsing controls,
terminal event policy, schedule agreement, and compact-interval surgery
finiteness. Separately, for
every nonempty compact normalized initial metric with no embedded projective
plane of trivial normal bundle, and every positive non-increasing control
function bounded by the schedule, return a changing-carrier flow on all
nonnegative times with exact finite-prefix
witnesses, schedule agreement, initial metric identification, compact-interval
surgery finiteness, whole-domain controls and constructed terminal event
policy. The same setup epsilon and C
are retained. One application of `m51InductionPreparation` fixes the M49
cutoff, calibrated setup, M46/M47 packages and both volume services before
either flow is chosen. `M51Numerical.schedule` retains the literal recursive
choices. Completed epoch chains assemble the actual global representatives,
ordinary slabs and terminal events; every old flow embeds by its complete
extension ledger. The normalized output stores its actual selected volume
certificate and passes that same certificate to M50.
Source: Morgan--Tian Theorem 15.9 and Corollary 15.10, printed pp. 363--366,
and the schedule/finite-prefix argument in Section 17.2, pp. 408--411
(arXiv V2 pp. 395--397).  The corrected surgery-volume erratum remains an
upstream obligation in M49.

Earlier milestone theories remain exactly the frozen provider hypotheses.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- One schedule supports both given-flow extension and normalized metrics.
Morgan--Tian Theorem 15.9, Corollary 15.10 and Section 17.2,
pp. 363-366 and 408-411. -/
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

end PoincareMT
