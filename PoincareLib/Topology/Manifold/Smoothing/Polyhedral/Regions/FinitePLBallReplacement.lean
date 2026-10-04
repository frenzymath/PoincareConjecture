import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBoundaryPieceGluing

/-!
# Replacing one ball piece inside a finite PL ball

A prescribed map of the retained complement extends across the
replaced ball. When the outer boundary lies in that complement,
its exact image remains the boundary of the new ball. See
Alexander 1924, pp. 7--8, Hudson 1969, pp. 15--19 and
M76 derivation 227.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

variable {V W X Y : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- Replacing a finite PL ball piece preserves the ambient ball
pair and the prescribed outer boundary image, without a ball
assumption on the retained complement. The union chart retains
both pieces. See Alexander pp. 7--8 and derivation 227. -/
theorem IsFinitePLBallPair.exists_piece_replacement
    {a b q c : Set X} {A B Q : Set Y}
    (hs : IsFinitePLBallPair V (a ∪ b) c)
    (ha : IsFinitePLBallPair W a q) (hA : IsFinitePLBallPair W A Q)
    (hinter : a ∩ b = q) (hInter : A ∩ B = Q) (hcb : c ⊆ b)
    (e : b ≃ₜ B) (he : e.IsFinitePL)
    (hmem : ∀ x : b, (x : X) ∈ q ↔ (e x : Y) ∈ Q)
    {f : X → Y} (hf : ∀ x : b, (e x : Y) = f x) :
    IsFinitePLBallPair V (A ∪ B) (f '' c) ∧
      ∃ H : (a ∪ b : Set X) ≃ₜ (A ∪ B : Set Y), H.IsFinitePL ∧
        (∀ x : b, (H ⟨x, Or.inr x.property⟩ : Y) = f x) ∧
        (∀ x : (a ∪ b : Set X), (x : X) ∈ a ↔ (H x : Y) ∈ A) ∧
        (∀ x : (a ∪ b : Set X), (x : X) ∈ b ↔ (H x : Y) ∈ B) ∧
        ∀ x : (a ∪ b : Set X), (x : X) ∈ c ↔ (H x : Y) ∈ f '' c := by
  obtain ⟨H, hH, hkeep, hHa, hHb⟩ :=
    ha.exists_union_homeomorph_of_boundary_piece hA hinter hInter e he hmem
  have hval (x : b) : (H ⟨x, Or.inr x.property⟩ : Y) = f x :=
    (congrArg (fun y : (A ∪ B : Set Y) => (y : Y)) (hkeep x)).trans (hf x)
  have hboundary (x : (a ∪ b : Set X)) : (x : X) ∈ c ↔ (H x : Y) ∈ f '' c := by
    constructor
    · intro hx
      exact ⟨x, hx, (hval ⟨x, hcb hx⟩).symm⟩
    · rintro ⟨y, hy, hyx⟩
      have hEq : H ⟨y, Or.inr (hcb hy)⟩ = H x :=
        Subtype.ext ((hval ⟨y, hcb hy⟩).trans hyx)
      have hyx' : y = (x : X) := congrArg Subtype.val (H.injective hEq)
      exact hyx' ▸ hy
  have houter : f '' c ⊆ A ∪ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact Or.inr (hf ⟨x, hcb hx⟩ ▸ (e ⟨x, hcb hx⟩).property)
  have hball : IsFinitePLBallPair V (A ∪ B) (f '' c) := by
    apply hs.of_homeomorph houter H.symm hH.symm
    intro y
    simpa only [H.apply_symm_apply] using (hboundary (H.symm y)).symm
  exact ⟨hball, H, hH, hval, hHa, hHb, hboundary⟩

end Set
