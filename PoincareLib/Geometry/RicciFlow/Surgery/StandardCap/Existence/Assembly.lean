import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.Existence
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Basic.MaximalExistence
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Curvature.Positive
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.RotationInvariance
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Asymptotics.AsymptoticCertificate
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Noncollapsing.NoncollapsingCertificate
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.CylinderAtlas

/-!
# Assembly conditional on the unit lifetime lower bound

Every field uses the same supplied initial metric and actual maximal
flow. The sole remaining hypothesis is the lifetime lower bound; the
proved cylinder upper bound gives equality with one.
Source: Morgan-Tian Theorems 12.5 and 12.29, pp. 295-297, 324-325;
conditional entry assembly derivation in the M34 task records.
-/

set_option autoImplicit false

namespace PoincareMT.M34

/-- All frozen standard-cap existence fields for the same actual maximal
flow, conditional only on its unit lifetime lower bound (Theorem 12.29). -/
theorem repairedStandardCapExistenceData_of_lifetime_ge_one
    (P : M34StandardCapPredecessors) {g0 : StandardInitialMetric}
    (F : MaximalStandardCapFlow g0) (hlifetime : 1 ≤ F.base.lifetime) :
    Nonempty (RepairedStandardCapExistenceData g0) := by
  obtain ⟨E0⟩ := standardCapEstimate_exists g0
  obtain ⟨A⟩ := nonempty_standardCylinderAtlas
  exact ⟨{
    atlas := A
    flow := F
    lifetime_one := le_antisymm
      (partialStandardCapFlow_lifetime_le_one P.curvature E0 F.base) hlifetime
    complete := fun _ ht => partialFlow_complete F.base P.curvature ht
    positive_sectional := partialFlow_positiveSectional P.curvature E0 F.base
    nonnegative_sectional := partialFlow_nonnegativeSectionalCurvature P.curvature E0 F.base
    rotation_invariant := fun _ ht =>
      partialStandardCapFlow_rotation_invariant P.curvature E0 F.base g0.cylindrical_end ht
    initial_estimate := E0
    asymptotic := fun _ ht _ he => standardFlowAsymptoticCertificate_exists P.curvature E0 F A he ht
    noncollapsing := standardFlow_noncollapsingCertificate F P
  }⟩

/-- The final existence theory follows from the unit lifetime lower bound
for actual maximal flows, with all other fields already constructed
(Theorems 12.5 and 12.29). -/
theorem repairedStandardCapExistenceTheory_of_lifetime_ge_one
    (P : M34StandardCapPredecessors)
    (hlifetime : ∀ (g0 : StandardInitialMetric) (F : MaximalStandardCapFlow g0),
      1 ≤ F.base.lifetime) : RepairedStandardCapExistenceTheory where
  initial_metric := standardInitialMetric_exists
  existence := by
    intro g0
    obtain ⟨F, _⟩ := maximalStandardCapFlow_exists P g0
    exact repairedStandardCapExistenceData_of_lifetime_ge_one P F (hlifetime g0 F)

end PoincareMT.M34
