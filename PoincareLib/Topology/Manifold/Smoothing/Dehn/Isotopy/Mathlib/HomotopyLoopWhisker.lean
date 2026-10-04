import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Actual basepoint transport through the rim homotopy

The homotopy square identifies the initial loop with the final loop
whiskered by the literal basepoint trace. This identity is stated in
path order, avoiding any reversal by the fundamental group's product
convention. See Hatcher, Theorem 3.1, pp. 45--48, and Dehn derivations
022 section 3 and 023 section 4.
-/

set_option autoImplicit false

namespace ContinuousMap.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}

/-- The initial loop class equals the final loop class transported
by the actual basepoint path of the homotopy. Both concatenations
are in geometric path order. See Dehn derivation 023, section 4. -/
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
