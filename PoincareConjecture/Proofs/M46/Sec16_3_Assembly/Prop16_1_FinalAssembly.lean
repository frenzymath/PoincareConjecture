import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_1_BarrierParameters
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.MinimizingRegion
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CommonCapSources
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_RegularSource











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace PoincareConjecture.Proofs.M46





theorem induction_of_actionBarrierProducer
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (avoid : ∀ (p : SurgeryParameterPrefix S.constants), S.SeedCompatible p →
      ∀ (rNext : ℝ), 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∀ (rho : ℝ), 0 < rho → rho ≤ rNext →
      ∀ (Q : ActionBarrierParameters S p rho) (cutoff : ℝ),
      cutoff ≤ capScalarCutoff p.setup.epsilon Q.c (rho / 2) →
        CapAvoidanceProducer.{u} p rNext cutoff rho Q.A Q.eta Q.theta) :
    Nonempty (RepairedNoncollapseInductionData.{u} S) := by
  let P44 : M44CapPersistencePredecessors.{u} := {
    curvature := P.m04
    ordinary_flow := P.m13.ordinary_flow
  }
  apply induction_of_regular_sources_and_cylinders P S
  intro p hp
  let B := max 1 (seedAnalyticConstant S)
  have hB : 1 ≤ B := le_max_left _ _
  have hBanalytic : seedAnalyticConstant S ≤ B := le_max_right _ _
  have ht : 0 < surgeryEpochStart (p.i + 1) := by unfold surgeryEpochStart; positivity
  have hbudget : 0 < actionBudget p := by unfold actionBudget; positivity
  have hl : 0 < actionBudget p / (4 * p.setup.epsilon) :=
    div_pos hbudget (mul_pos (by norm_num) p.setup.epsilon_pos)
  have hseed : 0 < seedImageRadius B (p.r (Fin.last p.i)) :=
    seedImageRadius_pos hB (p.r_pos _)
  have hV : 0 < p.kappa (Fin.last p.i) *
      seedImageRadius B (p.r (Fin.last p.i)) ^ 3 / 8 :=
    div_pos (mul_pos (p.kappa_pos _) (pow_pos hseed _)) (by norm_num)
  obtain ⟨U⟩ := P.uniformConfigurationData _ _ _ ht hl hV
  refine ⟨_, _, _, U, ?_⟩
  intro rNext hr hrLast
  let rho := smallTestRadius B rNext
  have hrho : 0 < rho := smallTestRadius_pos hB hr
  have hrho_le : rho ≤ rNext := smallTestRadius_le hB hr
  obtain ⟨Q⟩ := exists_actionBarrierParameters S p hrho
  have htheta : 0 < Q.theta := by linarith [Q.theta_half]
  have hA : S.standard_initial.cylindrical_end.radius + 5 < Q.A := by
    linarith [Q.A_buffer, Q.A_pos]
  obtain ⟨delta0, hdelta0, hlast, hfloor, hcontrols, hlow⟩ :=
    exists_common_cap_cutoff_with_seed_bounds P P44 S p hp hB hBanalytic Q.c_pos
      htheta Q.theta_one hA Q.eta_pos hr hrLast Q.scalar_bound
  let delta := min delta0 (capScalarCutoff p.setup.epsilon Q.c (rho / 2))
  have hdelta : 0 < delta :=
    lt_min hdelta0 (capScalarCutoff_pos p.setup.epsilon_pos Q.c_pos (by positivity))
  have hsmall : delta ≤ delta0 := min_le_left _ _
  have hsafe : delta ≤ capScalarCutoff p.setup.epsilon Q.c (rho / 2) := min_le_right _ _
  refine ⟨rho, hrho, hrho_le, delta, hdelta, hsmall.trans hlast, ?_,
    hlow.cutoff_mono hsmall⟩
  apply regularSourceProducer_of_selected_cap_bounds P P44 S p hp hB hBanalytic
    Q.c_pos hr hrLast (hsmall.trans hfloor)
  · intro F O inputs
    exact (hcontrols F O (inputs.cutoff_mono hsmall)).2
  · exact avoid p hp rNext hr hrLast rho hrho hrho_le Q delta hsafe
  · exact minimizingRegionProducer P p rNext delta rho
  · intro F O inputs
    exact (hcontrols F O (inputs.cutoff_mono hsmall)).1

end PoincareConjecture.Proofs.M46
