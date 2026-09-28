import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps











set_option autoImplicit false

namespace ContinuousMap.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}




theorem loop_quotient_eq_whisker (H : f.Homotopy g) {x : X} (rho : Path x x) :
    Path.Homotopic.Quotient.mk (rho.map f.continuous) =
      Path.Homotopic.Quotient.mk
        (((H.evalAt x).trans (rho.map g.continuous)).trans (H.evalAt x).symm) := by
  have h := Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H rho)
  have hright := congrArg
    (fun q : Path.Homotopic.Quotient (f x) (g x) =>
      q.trans (Path.Homotopic.Quotient.mk (H.evalAt x).symm)) h
  simpa only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl] using hright

end ContinuousMap.Homotopy
