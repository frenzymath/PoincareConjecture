import PoincareConjecture.Proofs.M76.PrimeReduction.InnermostReturningBigon
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLinearChain

set_option autoImplicit false

open Set

namespace Polygon

local notation "V" => (ℝ × ℝ)
local notation "Z" => (Set.preimage (Prod.snd : (ℝ × ℝ) → ℝ) ({0} : Set ℝ))

theorem exists_innermost_returning_bigon_of_actual_paths
    {ι : Type*} [Finite ι] [Nonempty ι]
    (n : ι → ℕ) (P : ∀ i, Polygon V (n i + 3))
    (p : ∀ i, Fin (n i + 2) → V)
    (hP : ∀ i, (P i).HasSimplicialEdges)
    (hi : ∀ i, Function.Injective (P i))
    (hup : ∀ i j, 0 ≤ (P i j).2)
    (hp : ∀ i, Function.Injective (p i))
    (hinter : ∀ i (r s : Fin (n i + 1)),
      segment ℝ ((p i) r.castSucc) ((p i) r.succ) ∩
          segment ℝ ((p i) s.castSucc) ((p i) s.succ) ⊆
        convexHull ℝ
          (({(p i) r.castSucc, (p i) r.succ} : Set V) ∩
            {(p i) s.castSucc, (p i) s.succ}))
    (hboundary : ∀ i,
      (P i).boundary ℝ = pathCarrier (p i) ∪
        segment ℝ ((p i) 0) ((p i) (Fin.last (n i + 1))))
    (haxis : ∀ i,
      pathCarrier (p i) ∩ Z =
        {((p i) 0), (p i) (Fin.last (n i + 1))})
    (hdis : Pairwise fun i j => Disjoint (pathCarrier (p i)) (pathCarrier (p j))) :
    ∃ i, IsFinitePLBallPair V (closure (P i).inside) ((P i).boundary ℝ) ∧
      closure (P i).inside ∩ Z =
        segment ℝ ((p i) 0) ((p i) (Fin.last (n i + 1))) ∧
      closure (P i).inside ∩ (⋃ j, (P j).boundary ℝ) = (P i).boundary ℝ ∧
      Disjoint (P i).inside (⋃ j, (P j).boundary ℝ) := by
  have hA : ∀ i, IsFinitePLBallPair ℝ (pathCarrier (p i))
      {((p i) 0), (p i) (Fin.last (n i + 1))} := by
    intro i
    exact Set.isFinitePLBallPair_linear_chain (p i) (hp i) (hinter i)
  exact exists_innermost_returning_bigon n P hP hi hup
    (fun i => pathCarrier (p i))
    (fun i => (p i) 0) (fun i => (p i) (Fin.last (n i + 1)))
    hA hboundary haxis hdis

end Polygon
