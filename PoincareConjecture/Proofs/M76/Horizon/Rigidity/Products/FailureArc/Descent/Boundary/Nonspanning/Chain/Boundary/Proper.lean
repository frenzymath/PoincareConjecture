import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Boundary.Outer



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.NonspanningStripExteriors

open PolygonalCrossingResolution NonspanningChainHole

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "Ann" => squareAnnulus 8 1

variable {c : Bool → P2 → P2} {D T : Set P2} (E : NonspanningStripExteriors c D T)
  (N : NonspanningChainAnnulus E.hole)

theorem preserves_region {X : Type*} {f g : P2 → X} {τ : C3 → X} {R : Set X}
    (hf : MapsTo f (T \ interior D) R) (hτ : MapsTo τ tube R)
    (hkeep : ∀ i (x : E.hole.sourceSet i), g (N.copy i x) =
      pieceMap f (τ ∘ tubeArmOrientation E.s0 E.s1) i x) : MapsTo g Ann R := by
  intro x hx
  obtain ⟨i, y, hy⟩ := mem_iUnion.mp (N.copy_cover.symm.subset (mem_univ ⟨x, hx⟩))
  have heq : (N.copy i y : P2) = x := congrArg Subtype.val hy
  rw [← heq, hkeep]
  cases i with
  | inl k => exact hf ⟨E.retained_subset k y.property.1, y.property.2⟩
  | inr b =>
    apply hτ
    apply (tubeArmOrientation_mem_tube E.s0 E.s1 _).mpr
    exact (mapsTo_tube (show (1 / 4 : ℝ) ≤ 1 by norm_num) b).2 y.property

theorem preserves_properness {X : Type*} {f g : P2 → X} {τ : C3 → X} {Q : Set X}
    (hD : IsFinitePLBallPair P2 D (frontier D))
    (hcQ : ∀ j p, p ∈ source → (c j p ∈ frontier T ↔ p.1 = 0 ∨ p.1 = 1))
    (hdis : Disjoint (c false '' source) (c true '' source))
    (hf : ∀ x ∈ T \ interior D, f x ∈ Q ↔ x ∈ frontier T ∪ frontier D)
    (hτ : ∀ z ∈ tube, τ z ∈ Q ↔ z.2 = 0 ∨ z.2 = 1)
    (hkeep : ∀ i (x : E.hole.sourceSet i), g (N.copy i x) =
      pieceMap f (τ ∘ tubeArmOrientation E.s0 E.s1) i x) :
    ∀ x ∈ Ann, g x ∈ Q ↔ depth 8 x = -1 ∨ depth 8 x = 1 := by
  have hout := E.normalized_copies_outer_iff N hcQ hdis
  intro x hx
  obtain ⟨i, y, hy⟩ := mem_iUnion.mp (N.copy_cover.symm.subset (mem_univ ⟨x, hx⟩))
  have heq : (N.copy i y : P2) = x := congrArg Subtype.val hy
  rw [← heq, hkeep]
  cases i with
  | inl k =>
    change f y ∈ Q ↔ _
    rw [hf y ⟨E.retained_subset k y.property.1, y.property.2⟩,
      hout.1 k y, N.retained_inner hD k y]
    rfl
  | inr b =>
    change (τ ∘ tubeArmOrientation E.s0 E.s1) (alternate (1 / 4) b y) ∈ Q ↔ _
    rw [reoriented_tube_frontier_iff τ hτ E.s0 E.s1 _
      ((mapsTo_tube (show (1 / 4 : ℝ) ≤ 1 by norm_num) b).2 y.property),
      hout.2 b y]
    simp only [alternate, N.strip_not_inner b y, or_false]

theorem preserves_marks {X : Type*} {f g : P2 → X} {τ : C3 → X} (F : Bool → Set X)
    (hD : IsFinitePLBallPair P2 D (frontier D))
    (hcQ : ∀ j p, p ∈ source → (c j p ∈ frontier T ↔ p.1 = 0 ∨ p.1 = 1))
    (hdis : Disjoint (c false '' source) (c true '' source))
    (hf0 : ∀ x ∈ T \ interior D, x ∈ frontier T → f x ∈ F false)
    (hf1 : ∀ x ∈ T \ interior D, x ∈ frontier D → f x ∈ F true)
    (hτ : ∀ z ∈ tube, z.2 = 0 ∨ z.2 = 1 → τ z ∈ F false)
    (hkeep : ∀ i (x : E.hole.sourceSet i), g (N.copy i x) =
      pieceMap f (τ ∘ tubeArmOrientation E.s0 E.s1) i x) :
    (∀ x ∈ Ann, depth 8 x = -1 → g x ∈ F false) ∧
    (∀ x ∈ Ann, depth 8 x = 1 → g x ∈ F true) := by
  have hout := E.normalized_copies_outer_iff N hcQ hdis
  constructor
  · intro x hx hdepth
    obtain ⟨i, y, hy⟩ := mem_iUnion.mp (N.copy_cover.symm.subset (mem_univ ⟨x, hx⟩))
    have heq : (N.copy i y : P2) = x := congrArg Subtype.val hy
    rw [← heq] at hdepth ⊢
    rw [hkeep]
    cases i with
    | inl k =>
      exact hf0 y ⟨E.retained_subset k y.property.1, y.property.2⟩
        ((hout.1 k y).mp hdepth)
    | inr b =>
      apply reoriented_tube_marked_ends τ hτ E.s0 E.s1
      · exact (mapsTo_tube (show (1 / 4 : ℝ) ≤ 1 by norm_num) b).2 y.property
      · exact (hout.2 b y).mp hdepth
  · intro x hx hdepth
    obtain ⟨i, y, hy⟩ := mem_iUnion.mp (N.copy_cover.symm.subset (mem_univ ⟨x, hx⟩))
    have heq : (N.copy i y : P2) = x := congrArg Subtype.val hy
    rw [← heq] at hdepth ⊢
    rw [hkeep]
    cases i with
    | inl k =>
      exact hf1 y ⟨E.retained_subset k y.property.1, y.property.2⟩
        ((N.retained_inner hD k y).mp hdepth)
    | inr b => exact (N.strip_not_inner b y hdepth).elim

end PoincareConjecture.M76.Dehn.NonspanningStripExteriors
