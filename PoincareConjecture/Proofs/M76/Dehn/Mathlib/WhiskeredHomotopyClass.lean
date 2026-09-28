import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HomotopyLoopWhisker
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.WhiskeredLoopSplit

set_option autoImplicit false

namespace ContinuousMap.Homotopy

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
