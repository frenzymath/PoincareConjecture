import PoincareLib.Geometry.RicciFlow.AncientKappa.StructuralData
import PoincareLib.Geometry.RicciFlow.Harnack.Theory
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory

/-!
# M16 structural ancient-kappa statement

The theorem is dimension-general and exposes derived structural data for
every actual ancient kappa-solution.  Its direct predecessor services are
M04 tensor calculus, M06 ancient Harnack, and M13 parabolic rescaling.  No
orientation, compactness, model classification, or limit witness is part of
this contract.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-! The complete M16 output, with predecessor services supplied to the theorem. The
underlying witness is data-valued and exposes the constructed normalization
witness; the public conclusion is its proposition-valued `Nonempty` wrapper so
the numbered declaration remains a genuine theorem. -/
structure AncientKappaStructuralTheory (n : ℕ) : Type (u + 2) where
  structural : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
    ∀ K : AncientKappaSolution n M, AncientKappaStructuralData K

def AncientKappaStructuralConclusion (n : ℕ) : Prop :=
  Nonempty (AncientKappaStructuralTheory.{u} n)

end PoincareMT
