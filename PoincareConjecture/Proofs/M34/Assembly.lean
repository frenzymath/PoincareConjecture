import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.Existence
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.MaximalExistence
import PoincareConjecture.Proofs.M34.Lemma12_6_Curvature.Positive
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.RotationInvariance
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.AsymptoticCertificate
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.NoncollapsingCertificate
import PoincareConjecture.Proofs.M34.Standard.CylinderAtlas

set_option autoImplicit false

namespace PoincareConjecture.M34

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

theorem repairedStandardCapExistenceTheory_of_lifetime_ge_one
    (P : M34StandardCapPredecessors)
    (hlifetime : ∀ (g0 : StandardInitialMetric) (F : MaximalStandardCapFlow g0),
      1 ≤ F.base.lifetime) : RepairedStandardCapExistenceTheory where
  initial_metric := standardInitialMetric_exists
  existence := by
    intro g0
    obtain ⟨F, _⟩ := maximalStandardCapFlow_exists P g0
    exact repairedStandardCapExistenceData_of_lifetime_ge_one P F (hlifetime g0 F)

end PoincareConjecture.M34
