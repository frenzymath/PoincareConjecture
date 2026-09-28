import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceRegions
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallReplacement
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior










set_option autoImplicit false

open Set Geometry

namespace Dehn

local notation "P2" => (ℝ × ℝ)



theorem polygon_closed_inside_eq_of_ball_pair {n : ℕ}
    (P : Polygon P2 (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) {D : Set P2}
    (hD : IsFinitePLBallPair P2 D (P.boundary ℝ)) : closure P.inside = D := by
  have hi := P.inside_eq_of_open_bounded_frontier hP hinjP isOpen_interior
    (hD.isCompact.isBounded.subset interior_subset)
    (hD.isConnected_interior_of_finrank_eq rfl).nonempty
    (hD.frontier_interior_of_finrank_eq rfl)
  rw [hi]
  exact hD.closure_interior_of_finrank_eq rfl




theorem polygon_annulus_region_of_cap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a b q r : Set E} {T : Set P2} {m n : ℕ}
    (hs : IsFinitePLBallPair P2 (a ∪ b) r) (ha : IsFinitePLBallPair P2 a q)
    (hinter : a ∩ b = q) (hrb : r ⊆ b)
    (P : Polygon P2 (m + 3)) (Q : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hdis : Disjoint (P.boundary ℝ) (Q.boundary ℝ))
    (e : b ≃ₜ T) (he : e.IsFinitePL)
    (hmem : ∀ x : b, (x : E) ∈ q ↔ (e x : P2) ∈ P.boundary ℝ)
    (hcap : closure P.inside ∩ T = P.boundary ℝ)
    {f : E → P2} (hf : ∀ x : b, (e x : P2) = f x)
    (hrim : f '' r = Q.boundary ℝ) :
    closure P.inside ⊆ Q.inside ∧ T = closure Q.inside \ P.inside := by
  obtain ⟨hball, _⟩ := hs.exists_piece_replacement ha
    (P.isFinitePLBallPair_closed_inside hP hinjP) hinter hcap hrb e he hmem hf
  rw [hrim] at hball
  have hclosed : closure Q.inside = closure P.inside ∪ T :=
    polygon_closed_inside_eq_of_ball_pair Q hQ hinjQ hball
  have hboundary : P.boundary ℝ ⊆ Q.inside := by
    intro x hx
    have hcl : x ∈ closure Q.inside := hclosed.symm ▸ Or.inl
      ((P.isFinitePLBallPair_closed_inside hP hinjP).1 hx)
    rw [closure_eq_self_union_frontier, Q.frontier_inside hQ hinjQ] at hcl
    exact hcl.resolve_right (Set.disjoint_left.mp hdis hx)
  refine ⟨Q.closure_inside_subset_inside_of_boundary_subset_inside P
    hQ hinjQ hP hinjP hboundary, ?_⟩
  rw [hclosed]
  ext x
  constructor
  · intro hx
    refine ⟨Or.inr hx, ?_⟩
    intro hxi
    have hxb : x ∈ P.boundary ℝ := hcap ▸ And.intro (subset_closure hxi) hx
    exact hxi.1 hxb
  · rintro ⟨hx | hx, hxi⟩
    · have hxb : x ∈ P.boundary ℝ := by
        rw [closure_eq_self_union_frontier, P.frontier_inside hP hinjP] at hx
        exact hx.resolve_left hxi
      exact (hcap.symm ▸ hxb).2
    · exact hx

end Dehn
