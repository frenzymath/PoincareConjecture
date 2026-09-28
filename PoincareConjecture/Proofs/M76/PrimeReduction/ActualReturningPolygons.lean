import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningPathPolygon
import PoincareConjecture.Proofs.M76.PrimeReduction.ActualReturningArcFamily

set_option autoImplicit false

open Set

namespace Polygon

local notation "V" => (ℝ × ℝ)
local notation "Z" => (Set.preimage (Prod.snd : (ℝ × ℝ) → ℝ) ({0} : Set ℝ))

theorem exists_actual_returning_polygons_and_innermost
    {ι : Type*} [Finite ι] [Nonempty ι]
    (n : ι → ℕ) (p : ∀ i, Fin (n i + 2) → V)
    (hp : ∀ i, Function.Injective (p i))
    (hinter : ∀ i (r s : Fin (n i + 1)),
      segment ℝ ((p i) r.castSucc) ((p i) r.succ) ∩
          segment ℝ ((p i) s.castSucc) ((p i) s.succ) ⊆
        convexHull ℝ (({(p i) r.castSucc, (p i) r.succ} : Set V) ∩
          {(p i) s.castSucc, (p i) s.succ}))
    (haxis : ∀ i, pathCarrier (p i) ∩ Z = {(p i) 0, (p i) (Fin.last (n i + 1))})
    (hup : ∀ i j, 0 ≤ (p i j).2)
    (hdis : Pairwise fun i j => Disjoint (pathCarrier (p i)) (pathCarrier (p j))) :
    ∃ P : ∀ i, Polygon V (n i + 3),
      (∀ i, (P i).HasSimplicialEdges ∧ Function.Injective (P i)) ∧
      (∀ i j, 0 ≤ (P i j).2) ∧
      (∀ i, (P i).boundary ℝ = pathCarrier (p i) ∪
        segment ℝ ((p i) 0) ((p i) (Fin.last (n i + 1)))) ∧
      ∃ i, IsFinitePLBallPair V (closure (P i).inside) ((P i).boundary ℝ) ∧
        closure (P i).inside ∩ Z =
          segment ℝ ((p i) 0) ((p i) (Fin.last (n i + 1))) ∧
        closure (P i).inside ∩ (⋃ j, (P j).boundary ℝ) = (P i).boundary ℝ ∧
        Disjoint (P i).inside (⋃ j, (P j).boundary ℝ) := by
  choose P hP hi hPu hb using fun i =>
    exists_polygon_of_returning_path (p i) (hp i) (hinter i) (haxis i) (hup i)
  refine ⟨P, fun i => ⟨hP i, hi i⟩, hPu, hb, ?_⟩
  exact exists_innermost_returning_bigon_of_actual_paths n P p hP hi hPu hp hinter hb haxis hdis

end Polygon
