import PoincareConjecture.Proofs.M76.Mathlib.BasisRadialProjection
import PoincareConjecture.Proofs.M76.Smoothing.FixedEdgeCycleSpace










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



abbrev CycleProjectionSpace (n : ℕ) (b : Module.Basis (Fin (n + 3)) ℝ E) (theta : ℝ) :=
  (cyclicEdgeComplex n).FixedBasisRadialProjection b
    ({0, 1} : Set (Fin (n + 3))) (cycleFrame n theta)



theorem contractible_cycleProjectionSpace (n : ℕ) (b : Module.Basis (Fin (n + 3)) ℝ E)
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    ContractibleSpace (CycleProjectionSpace n b theta) := by
  let := contractible_fixedEdgeCycleSpace n htheta
  exact (AbstractSimplicialComplex.fixedBasisRadialProjectionHomeomorph
    (cyclicEdgeComplex n) b ({0, 1} : Set (Fin (n + 3)))
    (cycleFrame n theta)).contractibleSpace

end PoincareConjecture.M76.Smoothing
