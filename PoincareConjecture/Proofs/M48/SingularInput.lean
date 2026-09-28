import PoincareConjecture.Proofs.M48.CanonicalTransport
import PoincareConjecture.Proofs.M48.RegularTimeAnalytics
import PoincareConjecture.Proofs.M48.RegularReference
import PoincareConjecture.Proofs.M48.LimitCalibration









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture
namespace M48AnalyticCalibration

variable {S : RepairedControlledSchedulesData.{u}} (A : M48AnalyticCalibration S)
  (P : M48Predecessors.{u}) {p : SurgeryParameterPrefix S.constants}
  {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
  (hp : S.SeedCompatible p) (old : SurgeryPrefixControls p F O)
  {Q : SurgeryNoncollapseExtension.{u} p} {N : SurgeryCanonicalExtension p Q}
  (controls : SurgeryEpochContinuationControls p F O Q N)
  {L : RepairedPreterminalSlab F O.H} (R : M48RegularSpacetimeData L)

include P hp old controls in

theorem regular_canonical (t : ℝ) (ht : t ∈ R.history.generalized.interval)
    (hregular : t = 0 ∨ t ∉ L.singularCatalog)
    (x : (R.history.generalized.slice t).carrier)
    (hQ : (A.historyRadius N.rNext)⁻¹ ^ 2 ≤ R.history.generalized.scalar ⟨t, x⟩) :
    GeneralizedCanonicalControl (F := R.history.generalized) t x S.setup.epsilon S.setup.C := by
  have htO : t ∈ surgeryObservationInterval O :=
    (show t ∈ L.regularHistoryWindow.interval from R.history.interval_eq ▸ ht)
  have hreg : t ∉ F.surgery_times := by
    rcases hregular with rfl | hreg
    · exact F.zero_not_surgery
    · exact fun hs => hreg ((L.mem_singularCatalog_iff htO).mpr hs)
  have hr : A.historyRadius N.rNext ≤ N.rNext :=
    (A.historyRadius_lt N.r_pos).le.trans (A.limitRadius_le N.rNext)
  have hi : N.rNext⁻¹ ≤ (A.historyRadius N.rNext)⁻¹ :=
    (inv_le_inv₀ N.r_pos (A.historyRadius_pos N.r_pos)).2 hr
  have hthreshold : N.rNext⁻¹ ^ 2 ≤ (A.historyRadius N.rNext)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr N.r_pos.le) hi 2
  have hactual : N.rNext⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature
      (R.history.history.forward t ht x) := by
    rw [R.history.scalar_pullback]
    exact hthreshold.trans hQ
  have h := R.history.canonical_control P.m13 t ht hreg x
    (controls.canonical t htO (O.interval_subset htO) _ hactual)
  simpa only [old.epsilon_eq, old.C_eq, hp.setup_eq] using h

include P hp old controls in

theorem singular_input
    (reference : M48RegularReferenceData L R.history) :
    ∃ I : SingularTimeAssumptions R.history.generalized O.H (F.slice L.start).carrier,
      I.reference = reference.reference ∧ I.r₀ = A.historyRadius N.rNext ∧
        I.epsilon = S.setup.epsilon ∧ I.constant = S.setup.C ∧
        I.analytic_constant = S.calibration.analytic_constant ∧
        I.singularTimes = L.singularCatalog := by
  refine ⟨{
  reference := reference.reference
  interval_nonnegative := by
    intro t ht
    have h : t ∈ L.regularHistoryWindow.interval := R.history.interval_eq ▸ ht
    exact h.1
  interval_preterminal := by
    intro t ht
    exact (show t ∈ L.regularHistoryWindow.interval from R.history.interval_eq ▸ ht)
  interval_exhausts_preterminal := by
    intro t ht
    exact R.history.interval_eq.symm ▸ (show t ∈ L.regularHistoryWindow.interval from ht)
  terminal_not_in_interval := by
    rw [R.history.interval_eq]
    exact fun h => lt_irrefl O.H h.2
  singularTimes := L.singularCatalog
  terminal_is_singular := L.terminal_mem_singularCatalog
  singularTimes_discrete := L.singularCatalog_discrete
  regular_slices_compact := R.regular_slices_compact
  positive_pinching := by
    intro q hq
    have h := (regular_pinched old R q.1 hq).2.1 q.2 (mem_univ _)
    change 0 ≤ (R.history.generalized.connection q.1).scalarCurvature q.2 + _
    rw [neg_div] at h
    linarith
  hamilton_ivey_pinching := by
    intro q hq hnegative
    exact (regular_pinched old R q.1 hq).2.2 q.2 (mem_univ _) hnegative
  curvature_lower_bound := ⟨-6, fun q hq => regular_scalar_lower_bound old R q.1 hq q.2⟩
  r₀ := A.historyRadius N.rNext
  r₀_pos := A.historyRadius_pos N.r_pos
  epsilon := S.setup.epsilon
  epsilon_pos := S.setup.epsilon_pos
  epsilon_lt_quarter := by
    have h := S.setup.epsilon_le.trans (min_le_left _ _)
    linarith
  terminal_epsilon_le_threshold := by
    simpa only [old.epsilon_eq, hp.setup_eq] using old.terminal_epsilon_le_threshold hp
  constant := S.setup.C
  constant_pos := S.setup.C_pos
  analytic_constant := S.calibration.analytic_constant
  analytic_constant_pos := S.calibration.analytic_constant_pos
  scalar_time_derivative_bound := A.regular_time_derivative P hp old controls R
  scalar_gradient_bound := A.regular_gradient hp old controls R
  canonical_control := A.regular_canonical P hp old controls R },
    rfl, rfl, rfl, rfl, rfl, rfl⟩

include P hp old controls in

theorem regular_limit :
    ∃ reference : M48RegularReferenceData L R.history,
      ∃ I : SingularTimeAssumptions R.history.generalized O.H (F.slice L.start).carrier,
        I.reference = reference.reference ∧ I.r₀ = A.historyRadius N.rNext ∧
          I.epsilon = S.setup.epsilon ∧ I.constant = S.setup.C ∧
          I.analytic_constant = S.calibration.analytic_constant ∧
          I.singularTimes = L.singularCatalog ∧
          ∃ limit : RepairedSingularRegularLimitData I,
          ∃ horn : RepairedHornSelectionData I,
            horn.limit = limit ∧
              terminalAccuracyFactor * S.setup.epsilon ≤ S.calibration.appendixA.epsilon₀ := by
  obtain ⟨reference⟩ := P.regular_reference_exists R
  obtain ⟨I, href, hr, he, hC, hA, htimes⟩ := A.singular_input P hp old controls R reference
  refine ⟨reference, I, href, hr, he, hC, hA, htimes, ?_⟩
  have hsmall : I.epsilon ≤ S.calibration.common_epsilon := by
    rw [he]
    linarith [S.calibration.two_epsilon_le_common, S.setup.epsilon_pos]
  simpa only [he] using m48CalibratedLimit S I hsmall

end M48AnalyticCalibration
end PoincareConjecture
