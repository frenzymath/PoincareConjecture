import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.BasisRadialProjection
import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.Graphs.FixedEdgeCycleSpace

/-!
# Contractible linear projections of cyclic links

Basis evaluation transfers the fixed-edge contraction to the ambient
linear maps used in Cairns 1940, Section 3, p. 799, and Lemma 5.1,
p. 801. This is the operator-coordinate step of M76 derivation 25;
the geometric kernel comparison is separate.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Linear maps realizing a cyclic link with the two frame columns
fixed. See Cairns pp. 799, 801 and M76 derivation 25. -/
abbrev CycleProjectionSpace (n : ℕ) (b : Module.Basis (Fin (n + 3)) ℝ E) (theta : ℝ) :=
  (cyclicEdgeComplex n).FixedBasisRadialProjection b
    ({0, 1} : Set (Fin (n + 3))) (cycleFrame n theta)

/-- The constrained ambient linear-map space is contractible in its
operator topology. See Cairns Lemma 5.1 and M76 derivation 25. -/
theorem contractible_cycleProjectionSpace (n : ℕ) (b : Module.Basis (Fin (n + 3)) ℝ E)
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    ContractibleSpace (CycleProjectionSpace n b theta) := by
  let := contractible_fixedEdgeCycleSpace n htheta
  exact (AbstractSimplicialComplex.fixedBasisRadialProjectionHomeomorph
    (cyclicEdgeComplex n) b ({0, 1} : Set (Fin (n + 3)))
    (cycleFrame n theta)).contractibleSpace

end PoincareMT.M76.Smoothing
