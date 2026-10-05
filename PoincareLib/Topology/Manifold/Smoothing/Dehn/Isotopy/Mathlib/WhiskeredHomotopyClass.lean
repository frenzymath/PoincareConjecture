import PoincareLib.Topology.Manifold.Smoothing.Dehn.Isotopy.Mathlib.HomotopyLoopWhisker
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.WhiskeredLoopSplit

/-!
# Retain the original whisker under an actual marked rim homotopy

Append the literal basepoint trace to the original path. The resulting
based class is exactly the original class, in path-concatenation order.
See Hatcher pp.45--48 and Dehn031, section5.
-/

set_option autoImplicit false

namespace ContinuousMap.Homotopy

/-- The original based loop class is unchanged after appending the
actual homotopy trace to its retained whisker. This equality therefore
retains exclusion from the very same original subgroup.
See Dehn031, section5. -/
theorem whiskeredLoopClass_eq {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (H : f.Homotopy g) {x : X} {b : Y}
    (p : Path b (f x)) (rho : Path x x) :
    p.whiskeredLoopClass (rho.map f.continuous) =
      (p.trans (H.evalAt x)).whiskeredLoopClass (rho.map g.continuous) := by
  simp only [Path.whiskeredLoopClass, Path.trans_symm,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  rw [H.loop_quotient_eq_whisker rho]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]

end ContinuousMap.Homotopy
