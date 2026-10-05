import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceData
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.ExistenceTheory
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.UniquenessTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.OperationTheory
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceInputs

/-!
Adapted from Mapher `PoincareMT/Statements/M44CapPersistence.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M44 repaired surgery-cap persistence statement

Every standard initial metric has a cap-persistence package with the exact
two-way comparison/disappearance alternative from Proposition 16.5. The
parameter prefix is indexed by the package's M36 constants and is required to
use the same standard initial metric.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedCapPersistenceTheory : Prop where
  persistence : RepairedStandardCapExistenceTheory →
    RepairedStandardCapUniquenessTheory →
    RepairedMetricSurgeryTheory.{u} →
    ∀ g₀ : StandardInitialMetric,
      Nonempty (RepairedCapPersistenceData.{u} g₀)

end PoincareMT
