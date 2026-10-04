/- Adapted from Mapher `PoincareMT/Proofs/M03/ConnectionExistence.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.RicciFlow.Local.Connection.Koszul
import PoincareLib.Geometry.RicciFlow.Local.Connection.Construction

/-!
# Existence of Levi-Civita connection data

Morgan-Tian, Theorem 1.2 and formula (1.1), printed pp. 3-4, supply the
coordinate construction. The conclusion is existence of actual compatible
connection data; it makes no uniqueness claim on irregular sections and
defines no chosen connection. The imported proof is kernel-closed; its
semantic review remains part of the M03 helper review.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- Every smooth metric has compatible torsion-free connection data. -/
theorem exists_leviCivitaData {n : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : Nonempty (LeviCivitaData g) := by
  exact RicciFlow.Local.leviCivitaData_nonempty g

end PoincareMT
