import PoincareConjecture.Statements.Ch04.Pinching
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M05.HorizonProof












set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]










theorem hamiltonIveyPinching
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Set.Ico a b))
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hinit : HamiltonIveyPinchedAt (F.connection a) a) :
    HamiltonIveyPinchingConclusion a b F := by
  exact horizon_hamiltonIveyPinching ha hab F hM04 hinit


theorem hamiltonIveyPinching_from_M04
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Set.Ico a b))
    (hinit : HamiltonIveyPinchedAt (F.connection a) a) :
    HamiltonIveyPinchingConclusion a b F := by
  exact hamiltonIveyPinching ha hab F ricciFlowCurvatureTheory hinit

end PoincareConjecture
