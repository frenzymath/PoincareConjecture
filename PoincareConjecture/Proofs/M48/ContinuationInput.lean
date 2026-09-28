import PoincareConjecture.Proofs.M48.PrefixControls
import PoincareConjecture.Proofs.M48.RegularAnalytics
import PoincareConjecture.Proofs.M45.Calibration

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M48AnalyticCalibration

variable {S : RepairedControlledSchedulesData.{u}} (A : M48AnalyticCalibration S)
  {p : SurgeryParameterPrefix S.constants} {F : SurgeryFlowData.{u}}
  {O : SurgeryObservation F} (hp : S.SeedCompatible p)
  (old : SurgeryPrefixControls p F O)
  {Q : SurgeryNoncollapseExtension.{u} p} {N : SurgeryCanonicalExtension p Q}
  (controls : SurgeryEpochContinuationControls p F O Q N)
  (hstart : surgeryEpochStart p.i ≤ O.H)
  (hend : O.H < surgeryEpochStart (p.i + 1))

include hp old controls hstart hend in

theorem terminal_height_bounds :
    F.parameters.h O.H ≤ F.local_constants.R₀ ^ (-1 / 2 : ℝ) ∧
      F.parameters.h O.H ≤
        (F.parameters.delta O.H * F.parameters.r O.H) * F.parameters.delta O.H ∧
      F.parameters.h O.H ≤
        (F.parameters.delta O.H * F.parameters.r O.H) / (2 * F.parameters.C) := by
  have hr := controls.next_r O.H ⟨hstart, hend⟩
  have hh : F.parameters.h O.H = S.setup.selector.h
      (F.parameters.delta O.H * F.parameters.r O.H) (F.parameters.delta O.H) := by
    simpa only [hp.setup_eq] using controls.next_h O.H ⟨hstart, hend⟩
  have hd := F.parameters.delta_pos O.H O.H_pos.le
  have hdle := old.delta_le_initial hp O.H O.H_pos.le
  have hD : 0 < S.Delta0 := by rw [← hp.Delta_zero_eq]; exact p.Delta_pos 0
  have hre : F.parameters.r O.H ≤ S.setup.epsilon := by
    rw [hr]
    exact N.r_le_last.trans ((p.r_le_epsilon _).trans_eq
      (congrArg SurgeryControlSetup.epsilon hp.setup_eq))
  have hrpos := F.parameters.r_pos O.H O.H_pos.le
  have hrho := mul_pos hd hrpos
  have hrhole : F.parameters.delta O.H * F.parameters.r O.H ≤
      S.Delta0 * S.setup.epsilon := mul_le_mul hdle hre hrpos.le hD.le
  have hm := S.setup.selector.h_mono_rho (F.parameters.delta O.H) hd.le
    hrho.le (mul_pos hD S.setup.epsilon_pos).le hrhole
  have hm' := S.setup.selector.h_mono_delta (S.Delta0 * S.setup.epsilon)
    (mul_pos hD S.setup.epsilon_pos).le hd.le hD.le hdle
  have hsmall := le_min_iff.mp (S.selector_deep_horn _ _ hrho hd)
  rw [hh]
  refine ⟨?_, hsmall.1, ?_⟩
  · rw [old.local_constants_eq]
    exact hm.trans (hm'.trans S.calibration.selector_initial_bound)
  · simpa only [old.C_eq, hp.setup_eq] using hsmall.2

noncomputable def continuationInput
    (hdomain : F.time_domain = Ico 0 O.H)
    (L : RepairedPreterminalSlab F O.H) (core : Set (F.slice L.start).carrier) :
    RepairedContinuationInput F O.H := by
  classical
  have hfront := A.frontier_history_scale hp old controls hstart hend
  have hrho : F.parameters.delta O.H * F.parameters.r O.H < A.historyRadius N.rNext := by
    simpa only [hfront.1] using hfront.2.2
  have hbounds := terminal_height_bounds hp old controls hstart hend
  exact {
    terminal_pos := O.H_pos
    time_domain_eq := hdomain
    last_slab := L
    admissible := old.admissible
    pinched := fun t ht => old.pinched t
      (by simpa only [hdomain, surgeryObservationInterval] using ht) ht
    canonical := fun t ht => old.canonicalAssumptionOn hend.le
      controls.canonical controls.next_r t
      (by simpa only [hdomain, surgeryObservationInterval] using ht) ht
    noncollapsed := fun t ht => controls.noncollapsed t
      (by simpa only [hdomain, surgeryObservationInterval] using ht) ht
    rho := F.parameters.delta O.H * F.parameters.r O.H
    rho_eq := rfl
    rho_pos := mul_pos (F.parameters.delta_pos O.H O.H_pos.le)
      (F.parameters.r_pos O.H O.H_pos.le)
    rho_lt_r := by
      simpa only [hfront.1] using
        hrho.trans_le ((A.historyRadius_lt N.r_pos).le.trans (A.limitRadius_le N.rNext))
    r₀ := A.historyRadius N.rNext
    r₀_pos := A.historyRadius_pos N.r_pos
    rho_lt_r₀ := hrho
    controlled_core := core
    core_status := by
      by_cases h : core.Nonempty
      · exact .nonempty h
      · exact .empty (Set.not_nonempty_iff_eq_empty.mp h)
    terminal_delta_bound := by
      rw [old.local_constants_eq]
      exact (old.delta_le_initial hp O.H O.H_pos.le).trans
        (hp.Delta_zero_eq ▸ p.Delta_le_setup 0)
    terminal_height_bound := hbounds.1
    terminal_height_rho_delta := hbounds.2.1
    terminal_height_rho_constant := hbounds.2.2 }

end PoincareConjecture.M48AnalyticCalibration
