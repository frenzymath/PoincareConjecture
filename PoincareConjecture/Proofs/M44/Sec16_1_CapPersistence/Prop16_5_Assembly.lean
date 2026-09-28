import PoincareConjecture.Statements.M44CapPersistence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_UniformCutoff

set_option autoImplicit false

universe u

namespace PoincareConjecture.M44

theorem exists_repaired_cap_persistence_data
    (P : M44CapPersistencePredecessors.{u})
    (E : RepairedStandardCapExistenceTheory)
    (U : RepairedStandardCapUniquenessTheory)
    (S : RepairedMetricSurgeryTheory.{u}) (g0 : StandardInitialMetric) :
    Nonempty (RepairedCapPersistenceData.{u} g0) := by
  obtain ⟨standard⟩ := E.existence g0
  obtain ⟨unique⟩ := U.estimates g0 standard
  obtain ⟨surgery⟩ := S.surgery g0
  refine ⟨{ standard_cap := standard
            standard_cap_uniqueness := ⟨unique⟩
            metric_surgery := surgery
            proposition_16_5 := ?_ }⟩
  intro p rNext hg hr _hrUpper A eta theta hA heta htheta htheta1
  have hmodel : ∃ model : RepairedStandardCapExistenceData p.setup.standard_initial,
      Nonempty (RepairedStandardCapUniquenessData p.setup.standard_initial model) := by
    rw [hg]
    exact ⟨standard, ⟨unique⟩⟩
  obtain ⟨model, ⟨modelUnique⟩⟩ := hmodel
  exact exists_cap_persistence_cutoff P p.setup model modelUnique
    (surgeryEpochStart (p.i - 1)) rNext A eta theta hr hA heta htheta htheta1

end PoincareConjecture.M44
