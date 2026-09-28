import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Fibers

set_option autoImplicit false
open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn

inductive NonspanningRetainedPiece
  | first | middle | last
  deriving DecidableEq

instance : Fintype NonspanningRetainedPiece where
  elems := {.first, .middle, .last}
  complete := by intro i; cases i <;> simp

namespace NonspanningChainGeometry

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "Strip" => PolygonalCrossingResolution.source
local notation "Piece" => NonspanningRetainedPiece

variable {SA SM SC : Set P2} {pA pL pR pC : I01 → P2}
  (s : NonspanningChainGeometry SA SM SC pA pL pR pC)

def retainedSet (_s : NonspanningChainGeometry SA SM SC pA pL pR pC) : Piece → Set P2
  | .first => SA
  | .middle => SM
  | .last => SC

def retainedCopy : (i : Piece) → s.retainedSet i → T
  | .first => s.copyA
  | .middle => s.copyM
  | .last => s.copyC

def stripCopy : Bool → Strip → T
  | false => s.copyL
  | true => s.copyR

theorem retainedCopy_embedding (i : Piece) : Topology.IsEmbedding (s.retainedCopy i) := by
  cases i with
  | first => exact s.embeddings.1
  | middle => exact s.embeddings.2.2.1
  | last => exact s.embeddings.2.2.2.2

theorem stripCopy_embedding (i : Bool) : Topology.IsEmbedding (s.stripCopy i) := by
  cases i with
  | false => exact s.embeddings.2.1
  | true => exact s.embeddings.2.2.2.1

theorem retainedCopy_representative (i : Piece) :
    ∃ f : P2 → P2, FinitePiecewiseAffineOn f (s.retainedSet i) ∧
      ∀ x : s.retainedSet i, (s.retainedCopy i x : P2) = f x := by
  cases i with
  | first => exact s.copyA_representative
  | middle => exact s.copyM_representative
  | last => exact s.copyC_representative

theorem stripCopy_representative (i : Bool) :
    ∃ f : P2 → P2, FinitePiecewiseAffineOn f Strip ∧
      ∀ x : Strip, (s.stripCopy i x : P2) = f x := by
  cases i with
  | false => exact s.copyL_representative
  | true => exact s.copyR_representative

theorem retainedCopy_ne {i j : Piece} (hij : i ≠ j)
    (x : s.retainedSet i) (y : s.retainedSet j) :
    s.retainedCopy i x ≠ s.retainedCopy j y := by
  cases i <;> cases j
  · exact (hij rfl).elim
  · exact s.A_ne_middle x y
  · exact s.A_ne_C x y
  · exact (s.A_ne_middle y x).symm
  · exact (hij rfl).elim
  · exact s.middle_ne_C x y
  · exact (s.A_ne_C y x).symm
  · exact (s.middle_ne_C y x).symm
  · exact (hij rfl).elim

theorem retained_strip_contact
    (hA : ∀ t, pA t ∈ frontier SA) (hL : ∀ t, pL t ∈ frontier SM)
    (hR : ∀ t, pR t ∈ frontier SM) (hC : ∀ t, pC t ∈ frontier SC)
    (i : Piece) (b : Bool) (x : s.retainedSet i) (y : Strip)
    (hxy : s.retainedCopy i x = s.stripCopy b y) :
    (x : P2) ∈ frontier (s.retainedSet i) := by
  cases i <;> cases b
  · obtain ⟨t, ht, _⟩ := (s.A_left_eq_iff x y).mp hxy
    exact ht ▸ hA t
  · exact (s.A_ne_right x y hxy).elim
  · obtain ⟨t, _, ht⟩ := (s.left_middle_eq_iff y x).mp hxy.symm
    exact ht ▸ hL t
  · obtain ⟨t, ht, _⟩ := (s.middle_right_eq_iff x y).mp hxy
    exact ht ▸ hR t
  · exact (s.left_ne_C y x hxy.symm).elim
  · obtain ⟨t, _, ht⟩ := (s.right_C_eq_iff y x).mp hxy.symm
    exact ht ▸ hC t

theorem indexed_cover (z : T) :
    (∃ i x, s.retainedCopy i x = z) ∨ ∃ b x, s.stripCopy b x = z := by
  rcases s.cover.symm.subset (mem_univ z) with
    ((((⟨x, hx⟩ | ⟨x, hx⟩) | ⟨x, hx⟩) | ⟨x, hx⟩) | ⟨x, hx⟩)
  · exact Or.inl ⟨.first, x, hx⟩
  · exact Or.inr ⟨false, x, hx⟩
  · exact Or.inl ⟨.middle, x, hx⟩
  · exact Or.inr ⟨true, x, hx⟩
  · exact Or.inl ⟨.last, x, hx⟩

end NonspanningChainGeometry
end PoincareConjecture.M76.Dehn
