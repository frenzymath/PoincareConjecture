import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Seed.StableSource
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.Volume.SmallRadiusAssembly
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.HalfRadiusHistory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.PositiveComponents.PositiveAncestor

/-!
# The actual regular source at the selected common cutoff

Morgan--Tian Proposition 16.1, pp. 391-394. Construct the actual
half-radius history, then substitute cap confinement, the minimizing
region and positive-component propagation into the checked stable
source. The shared birth bound is supplied by the same selected
cutoff and scalar-rate comparison as the small-test cylinder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareMT.Proofs.M46

/-- The selected-cutoff producer used by the final three-radius
assembly. Its source constants are fixed from the old prefix before
the next radius, cutoff, observed flow and actual test. -/
theorem regularSourceProducer_of_selected_cap_bounds
    (P : M46Predecessors.{u}) (P44 : M44CapPersistencePredecessors.{u})
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants)
    (hp : S.SeedCompatible p) {B c rNext cutoff rho A eta theta : ℝ}
    (hB : 1 ≤ B) (hBanalytic : seedAnalyticConstant S ≤ B) (hc : 0 < c)
    (hr : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i))
    (hcutoff : cutoff ≤ capScalarCutoff p.setup.epsilon c rNext)
    (hbirth : ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
      ObservedInputs p rNext cutoff F O →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
      t ∈ surgeryObservationInterval O → surgeryEpochStart (p.i - 1) ≤ t →
      ∀ i : Fin (F.event t hT).cap_count,
      ∀ x ∈ ((F.event t hT).caps i).carrier,
        c / (2 * (F.parameters.h t) ^ 2) ≤ (F.connection t).scalarCurvature x)
    (avoid : CapAvoidanceProducer.{u} p rNext cutoff rho A eta theta)
    (minimize : MinimizingRegionProducer.{u} p rNext cutoff rho)
    (caps : ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
      (inputs : ObservedInputs p rNext cutoff F O),
      OverlapCapControl p O inputs.old A eta theta) :
    RegularSourceProducer.{u} p rNext cutoff rho (surgeryEpochStart (p.i + 1))
      (actionBudget p / (4 * p.setup.epsilon))
      (p.kappa (Fin.last p.i) * seedImageRadius B (p.r (Fin.last p.i)) ^ 3 / 8) := by
  intro F O inputs D hnew _hlow hlarge
  obtain ⟨H⟩ := halfRadiusHistory P D
  obtain ⟨C, hbarrier⟩ := avoid F O inputs D H hnew hlarge (caps F O inputs)
  obtain ⟨M⟩ := minimize F O inputs D H hnew hlarge C hbarrier
  exact ⟨H, stableSource_of_observed_cap_birth P P44 S p hp hB hBanalytic hc
    hr hrLast hcutoff inputs H hnew C hbarrier M (positiveAncestorExclusion H)
      (hbirth F O inputs)⟩

end PoincareMT.Proofs.M46
