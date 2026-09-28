import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Hole
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PrescribedIntervalDiskMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.HoleTransport
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedPolygonAnnulus

set_option autoImplicit false
open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.NonspanningChainHole

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "Strip" => PolygonalCrossingResolution.source
local notation "Piece" => NonspanningRetainedPiece
local notation "Index" => (Piece ⊕ Bool)

variable {SA SM SC D : Set P2} {pA pL pR pC : I01 → P2}
  {s : NonspanningChainGeometry SA SM SC pA pL pR pC}
  (H : NonspanningChainHole s D)

def sourceSet (_H : NonspanningChainHole s D) : Index → Set P2
  | .inl i => s.retainedSet i \ interior D
  | .inr _ => Strip

def pieceCopy : (i : Index) → H.sourceSet i → T
  | .inl i, x => s.retainedCopy i ⟨x, x.property.1⟩
  | .inr b, x => s.stripCopy b x

theorem pieceCopy_embedding (i : Index) : Topology.IsEmbedding (H.pieceCopy i) := by
  cases i with
  | inl i =>
    exact (s.retainedCopy_embedding i).comp (Topology.IsEmbedding.inclusion sdiff_subset)
  | inr b => exact s.stripCopy_embedding b

theorem pieceCopy_outside (i : Index) (x : H.sourceSet i) :
    (H.pieceCopy i x : P2) ∈ T \ interior H.carrier := by
  refine ⟨(H.pieceCopy i x).property, ?_⟩
  cases i with
  | inl i => exact fun hx => x.property.2 ((H.retained_interior i _).mp hx)
  | inr b => exact fun hx => H.strip_avoid b x (interior_subset hx)

theorem pieceCopy_cover :
    (⋃ i, range (fun x : H.sourceSet i => (H.pieceCopy i x : P2))) =
      T \ interior H.carrier := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, x, rfl⟩ := mem_iUnion.mp hz
    exact H.pieceCopy_outside i x
  · rintro ⟨hz, hout⟩
    rcases s.indexed_cover ⟨z, hz⟩ with ⟨i, x, hx⟩ | ⟨b, x, hx⟩
    · have hxo : (x : P2) ∉ interior D := by
        intro hxi
        exact hout (by simpa only [hx] using (H.retained_interior i x).mpr hxi)
      exact mem_iUnion.mpr ⟨.inl i, ⟨x, x.property, hxo⟩, congrArg Subtype.val hx⟩
    · exact mem_iUnion.mpr ⟨.inr b, x, congrArg Subtype.val hx⟩

theorem source_complex
    (hS : ∀ i, IsFinitePLBallPair P2 (s.retainedSet i) (frontier (s.retainedSet i)))
    (hD : IsFinitePLBallPair P2 D (frontier D)) (i : Index) :
    ∃ K : SimplicialComplex ℝ P2, K.faces.Finite ∧ K.space = H.sourceSet i := by
  cases i with
  | inl i =>
    by_cases hi : i = H.piece
    · subst i
      obtain ⟨q, hq, _, _⟩ := exists_square_annulus_nested_disks hD (hS H.piece)
        H.source_inside (show (0 : ℝ) < 1 by norm_num) (show (2 : ℝ) * 1 < 8 by norm_num)
      obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hq.symm
      exact ⟨K, hK, hKs⟩
    · have heq : s.retainedSet i \ interior D = s.retainedSet i := by
        apply sdiff_eq_left.mpr
        exact (H.source_other i hi).mono_right interior_subset
      obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hS i
      exact ⟨K, hK, hKs.trans heq.symm⟩
  | inr b =>
    have hr := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hr
    exact ⟨K, hK, hKs⟩

theorem pieceCopy_representative
    (hS : ∀ i, IsFinitePLBallPair P2 (s.retainedSet i) (frontier (s.retainedSet i)))
    (hD : IsFinitePLBallPair P2 D (frontier D)) (i : Index) :
    ∃ c : P2 → P2, FinitePiecewiseAffineOn c (H.sourceSet i) ∧
      ∀ x : H.sourceSet i, (H.pieceCopy i x : P2) = c x := by
  cases i with
  | inl i =>
    obtain ⟨c, hc, hcv⟩ := s.retainedCopy_representative i
    obtain ⟨K, hK, hKs⟩ := H.source_complex hS hD (.inl i)
    refine ⟨c, ?_, fun x => hcv ⟨x, x.property.1⟩⟩
    rw [← hKs]
    exact hc.restrict K hK (hKs.subset.trans sdiff_subset)
  | inr b => exact s.stripCopy_representative b

end PoincareConjecture.M76.Dehn.NonspanningChainHole
