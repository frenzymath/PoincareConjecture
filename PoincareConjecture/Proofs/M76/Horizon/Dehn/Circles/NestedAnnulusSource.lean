import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.NestedSourceDisk
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceComplement












set_option autoImplicit false

open Set Metric Geometry

namespace Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "R" => sphere (0 : V2) 1



theorem nested_annulus_source_partition {m n : ℕ}
    (P : Polygon V2 (m + 3)) (I : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hI : I.HasSimplicialEdges) (hinjI : Function.Injective I)
    (hPsq : P.boundary ℝ ⊆ ball 0 1)
    (hnest : closure I.inside ⊆ P.inside) :
    (closure I.inside ∪ (closure P.inside \ I.inside)) ∪ (D \ P.inside) = D ∧
      closure I.inside ∩ (closure P.inside \ I.inside) = I.boundary ℝ ∧
      (closure P.inside \ I.inside) ∩ (D \ P.inside) = P.boundary ℝ ∧
      Disjoint (closure I.inside) (D \ P.inside) ∧
      IsClosed (closure P.inside \ I.inside) ∧ IsClosed (D \ P.inside) ∧
      R ⊆ D \ P.inside := by
  obtain ⟨_, hiP, hfP, hPD⟩ := polygon_source_region P
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hP hinjP (convex_ball _ _) hPsq
  obtain ⟨_, hiI, hfI, _⟩ := polygon_source_region I
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hI hinjI convex_univ (subset_univ _)
  have hIo : IsOpen I.inside := hiI ▸ isOpen_interior
  have hPo : IsOpen P.inside := hiP ▸ isOpen_interior
  have hIbd : closure I.inside \ I.inside = I.boundary ℝ := by
    rw [← hfI, frontier, isClosed_closure.closure_eq, hiI]
  have hPbd : closure P.inside \ P.inside = P.boundary ℝ := by
    rw [← hfP, frontier, isClosed_closure.closure_eq, hiP]
  have hIP : closure I.inside ⊆ closure P.inside := hnest.trans subset_closure
  refine ⟨?_, ?_, ?_, ?_, isClosed_closure.sdiff hIo,
    isClosed_closedBall.sdiff hPo, ?_⟩
  · apply Subset.antisymm
    · exact union_subset (union_subset (hIP.trans (hPD.trans ball_subset_closedBall))
        (sdiff_subset.trans (hPD.trans ball_subset_closedBall))) sdiff_subset
    · intro x hx
      by_cases hxP : x ∈ P.inside
      · by_cases hxI : x ∈ I.inside
        · exact Or.inl (Or.inl (subset_closure hxI))
        · exact Or.inl (Or.inr ⟨subset_closure hxP, hxI⟩)
      · exact Or.inr ⟨hx, hxP⟩
  · rw [← hIbd]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hIP hx.1, hx.2⟩⟩
  · rw [← hPbd]
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2.2⟩
    · intro hx
      exact ⟨⟨hx.1, fun hi => hx.2 (hnest (subset_closure hi))⟩,
        hPD.trans ball_subset_closedBall hx.1, hx.2⟩
  · exact Set.disjoint_left.mpr fun _ hx hy => hy.2 (hnest hx)
  · intro x hx
    exact ⟨sphere_subset_closedBall hx, fun hp => (ne_of_lt (hPD (subset_closure hp))) hx⟩




theorem exists_nested_annulus_source_disk {m n k : ℕ}
    (P : Polygon V2 (m + 3)) (I : Polygon V2 (n + 3)) (Q : Polygon V2 (k + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hI : I.HasSimplicialEdges) (hinjI : Function.Injective I)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hPsq : P.boundary ℝ ⊆ ball 0 1) (hIsq : I.boundary ℝ ⊆ ball 0 1)
    (hQsq : Q.boundary ℝ ⊆ ball 0 1)
    (hIP : closure I.inside ⊆ P.inside) (hQI : closure Q.inside ⊆ I.inside)
    (eb : Q.boundary ℝ ≃ₜ I.boundary ℝ) (heb : eb.IsFinitePL) :
    ∃ (H : closure Q.inside ≃ₜ closure I.inside) (j : V2 → V2),
      H.IsFinitePL ∧ FinitePiecewiseAffineOn j (closure Q.inside) ∧
      (∀ x : closure Q.inside, j x = (H x : V2)) ∧
      (∀ x : Q.boundary ℝ, j x = (eb x : V2)) ∧
      j '' closure Q.inside = closure I.inside ∧
      (j '' closure Q.inside ∪ (closure P.inside \ I.inside)) ∪ (D \ P.inside) = D ∧
      j '' closure Q.inside ∩ (closure P.inside \ I.inside) = I.boundary ℝ ∧
      (closure P.inside \ I.inside) ∩ (D \ P.inside) = P.boundary ℝ ∧
      Disjoint (j '' closure Q.inside) (D \ P.inside) ∧
      IsFinitePLBallPair V2 D R := by
  obtain ⟨H, j, hH, hj, hjH, _, himage, hjb, _⟩ :=
    exists_nested_circle_source_disk I Q hI hinjI hQ hinjQ hIsq hQsq hQI eb heb
  obtain ⟨hcover, hinner, houter, hdis, _⟩ :=
    nested_annulus_source_partition P I hP hinjP hI hinjI hPsq hIP
  refine ⟨H, j, hH, hj, hjH, hjb, himage, ?_, ?_, houter, ?_, isFinitePLBallPair_unit_cube⟩
  · simpa only [himage] using hcover
  · simpa only [himage] using hinner
  · simpa only [himage] using hdis

end Dehn
