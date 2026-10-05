import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.CanonicalTimeAssembly
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.TerminalCap.BoundedTipThreshold
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.TerminalCap.SelectedCapAssembly
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.TerminalCap.SelectedCollars

/-!
# The full canonical alternatives on the selected standard cap

Morgan-Tian Theorem 12.32, pp. 326-327, with the repaired initial
closed-cap boundary. The actual bounded-tip collars, retained analytic
controls and noncollapse produce the terminal cap. The initial-slab
and prescribed-window neck theorems then give one cap constant before
every point and time. No geometric or analytic producer is assumed.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.Uniqueness

open OrdinaryRealization

/-- Theorem 12.32, pp. 326-327: every point of the actual selected
flow has one of the three literal frozen alternatives, at the requested
epsilon and with one positive cap constant independent of point and time. -/
theorem standard_cap_canonical
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (epsilon : ℝ)
    (he : 0 < epsilon) (hehalf : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico 0 E.flow.base.lifetime,
      ∀ x : StandardCapSpace,
        StandardCanonicalAlternative E.atlas E.flow t x epsilon C := by
  apply canonical_of_bounded_tip_caps P E epsilon he hehalf
  intro D hD
  apply exists_bounded_tip_cap_threshold_of_selected P E epsilon D
  intro t x ht hR hd L kappa A
  obtain ⟨s, _F, hs, _hF, hcollars⟩ :=
    blowupSequence_bounded_tip_radial_collars P E t x ht hR L A he hehalf hD hd
  exact blowupSequence_caps_of_radial_collars P E t x ht hR L A he hehalf hD hd hs hcollars

end PoincareMT.M35.Uniqueness
