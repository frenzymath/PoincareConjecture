import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.EmbeddedHole
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.IndexedCopies



set_option autoImplicit false
open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "Strip" => PolygonalCrossingResolution.source
local notation "Piece" => NonspanningRetainedPiece

structure NonspanningChainHole {SA SM SC : Set P2} {pA pL pR pC : I01 → P2}
    (s : NonspanningChainGeometry SA SM SC pA pL pR pC) (D : Set P2) where
  carrier : Set P2
  chart : D ≃ₜ carrier
  chart_PL : chart.IsFinitePL
  ball : IsFinitePLBallPair P2 carrier (frontier carrier)
  inside : carrier ⊆ interior T
  piece : Piece
  source_inside : D ⊆ interior (s.retainedSet piece)
  source_other : ∀ i, i ≠ piece → Disjoint (s.retainedSet i) D
  chart_value : ∀ x : D, (chart x : P2) =
    s.retainedCopy piece ⟨x, interior_subset (source_inside x.property)⟩
  retained_mem : ∀ i (x : s.retainedSet i),
    (s.retainedCopy i x : P2) ∈ carrier ↔ (x : P2) ∈ D
  retained_interior : ∀ i (x : s.retainedSet i),
    (s.retainedCopy i x : P2) ∈ interior carrier ↔ (x : P2) ∈ interior D
  strip_avoid : ∀ b (x : Strip), (s.stripCopy b x : P2) ∉ carrier

namespace NonspanningChainGeometry

variable {SA SM SC : Set P2} {pA pL pR pC : I01 → P2}
  (s : NonspanningChainGeometry SA SM SC pA pL pR pC)

theorem nonempty_hole {D : Set P2} (hD : IsFinitePLBallPair P2 D (frontier D))
    (k : Piece) (hinside : D ⊆ interior (s.retainedSet k))
    (hother : ∀ i, i ≠ k → Disjoint (s.retainedSet i) D)
    (hA : ∀ t, pA t ∈ frontier SA) (hL : ∀ t, pL t ∈ frontier SM)
    (hR : ∀ t, pR t ∈ frontier SM) (hC : ∀ t, pC t ∈ frontier SC) :
    Nonempty (NonspanningChainHole s D) := by
  obtain ⟨P, q, hq, hP, hPT, hqv, hmem, hint, _, himage⟩ :=
    exists_inner_disk_image_of_copy (s.retainedCopy k) (s.retainedCopy_embedding k).injective
      (s.retainedCopy_representative k) hD hinside
  have hnot (i : Piece) (hik : i ≠ k) (x : s.retainedSet i) :
      (s.retainedCopy i x : P2) ∉ P := by
    rw [himage]
    rintro ⟨y, _, heq⟩
    exact s.retainedCopy_ne hik x y (Subtype.ext heq.symm)
  refine ⟨⟨P, q, hq, hP, hPT, k, hinside, hother, hqv, ?_, ?_, ?_⟩⟩
  · intro i x
    by_cases hik : i = k
    · subst i
      exact hmem x
    · constructor
      · exact fun hx => (hnot i hik x hx).elim
      · intro hx
        exact (disjoint_left.mp (hother i hik) x.property hx).elim
  · intro i x
    by_cases hik : i = k
    · subst i
      exact hint x
    · constructor
      · exact fun hx => (hnot i hik x (interior_subset hx)).elim
      · intro hx
        exact (disjoint_left.mp (hother i hik) x.property (interior_subset hx)).elim
  · intro b x hx
    obtain ⟨y, hy, heq⟩ := himage.subset hx
    have hfront := s.retained_strip_contact hA hL hR hC k b y x (Subtype.ext heq)
    exact hfront.2 (hinside hy)

end NonspanningChainGeometry
end PoincareConjecture.M76.Dehn
