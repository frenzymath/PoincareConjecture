import PoincareConjecture.Definitions.M16StructuralKappa
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Statements.Ch04.Harnack
import PoincareConjecture.Statements.M13Rescaling

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure AncientKappaStructuralTheory (n : ℕ) : Type (u + 2) where
  structural : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
    ∀ K : AncientKappaSolution n M, AncientKappaStructuralData K

def AncientKappaStructuralConclusion (n : ℕ) : Prop :=
  Nonempty (AncientKappaStructuralTheory.{u} n)

end PoincareConjecture
