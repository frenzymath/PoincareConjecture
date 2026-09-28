import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLDisk

set_option autoImplicit false

open Set Metric

namespace Polygon

theorem isUnitBallPair_closed_inside {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    IsUnitBallPair (ℝ × ℝ) (closure P.inside) (P.boundary ℝ) := by
  obtain ⟨hb, C, hC, hcv, hne, e, _, hboundary⟩ :=
    P.isFinitePLBallPair_closed_inside hP hinj
  exact (isUnitBallPair_of_compact_convex hC hcv hne).of_homeomorph hb e hboundary

theorem exists_closed_inside_homeomorph_closedBall {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    ∃ e : closure P.inside ≃ₜ closedBall (0 : ℝ × ℝ) 1,
      ∀ x : closure P.inside, (x : ℝ × ℝ) ∈ P.boundary ℝ ↔
        (e x : ℝ × ℝ) ∈ sphere (0 : ℝ × ℝ) 1 :=
  (P.isUnitBallPair_closed_inside hP hinj).2

theorem exists_closed_inside_extension {m n : ℕ}
    (P : Polygon (ℝ × ℝ) (m + 3)) (Q : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (eb : P.boundary ℝ ≃ₜ Q.boundary ℝ) :
    ∃ e : closure P.inside ≃ₜ closure Q.inside,
      ∀ (x : P.boundary ℝ) (hx : (x : ℝ × ℝ) ∈ closure P.inside),
        (e ⟨x, hx⟩ : ℝ × ℝ) = eb x := by
  obtain ⟨e, he, _⟩ := (P.isUnitBallPair_closed_inside hP hinjP).exists_extension
    (Q.isUnitBallPair_closed_inside hQ hinjQ) eb
  exact ⟨e, fun x _ => congrArg (fun z : closure Q.inside => (z : ℝ × ℝ)) (he x)⟩

end Polygon
