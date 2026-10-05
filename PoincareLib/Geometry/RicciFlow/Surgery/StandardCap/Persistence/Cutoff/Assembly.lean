import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceTheory
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cutoff.UniformCutoff

/-!
# The repaired cap-persistence package

The supplied M34, M35 and M36 packages and the proved cutoff-first
operation construct the exact frozen persistence data. Morgan--Tian,
Proposition 16.5, pp. 370-375; M44 derivation 113.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M44

/-- Every initial metric receives the frozen cap-persistence data
from the authorized analytic services and supplied M34, M35 and M36
theories. Source: Proposition 16.5, pp. 370-375; M44 derivation 113. -/
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

end PoincareMT.M44
