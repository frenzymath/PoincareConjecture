import PoincareLib.Geometry.RicciFlow.Extinction.Width.Contradiction.Main
import PoincareLib.Geometry.RicciFlow.Extinction.Global.TerminalEvent
import PoincareLib.Geometry.RicciFlow.Extinction.Global.WidthInputs
import PoincareLib.Geometry.RicciFlow.Extinction.Global.ContinuationInputs
import PoincareLib.Geometry.RicciFlow.Extinction.Global.NegativeProfile
import PoincareLib.Geometry.RicciFlow.Extinction.Global.EmptySlice
import PoincareLib.Geometry.RicciFlow.Extinction.Global.Statement

/-!
# M71 global finite extinction proof entry

The fixed initial width determines a time at which every continuation
package has a negative comparison profile. The resulting empty slice and
the checked first-empty helper give finite extinction with permanence in
the zero-time Poincare branch of Morgan--Tian Theorem 18.1, pp. 431-432.
M67, M68 and M69 remain the explicit predecessor hypotheses of the statement.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- On the same M52 flow, assume actual ancestry/comparison data and target
covers with one fixed initial component, metric, and nonzero class of trivial
pi2, together with the same flow's strict delta/height comparison bounds,
absolute scalar bound, and indexed M58/M61/M65/M66 width services.
Apply M67--M69 with that fixed class over [0,T], choose a time at which
the explicit profile is negative, and use M70 and the first-empty helper to
export finite extinction with permanence. Source: the zero-time specialization
of Morgan--Tian Proposition 18.18 and Theorem 18.1, pp. 431--432. -/
theorem m71GlobalFiniteExtinction
    : M71GlobalFiniteExtinctionStatement.{u} := by
  intro M _ _ _ _ _ _ _ _ _ N G input hM67 hM68 hM69
  have hT := m71ExtinctionTime_mem input
  have hempty := m71EmptySlice input.continuation hM67 hM68 hM69
    (m71ExtinctionTime input.continuation) hT
    (m71ExtinctionTime_nonneg input.continuation)
    (m71Profile_neg_at_extinctionTime input.continuation hM67)
  rw [input.flow_eq] at hT hempty
  obtain ⟨E, _hET, _hfirst⟩ := m71FirstEmptySurgery G.certificate
    (m71ExtinctionTime input.continuation) hT hempty
  exact ⟨E⟩

end PoincareMT
