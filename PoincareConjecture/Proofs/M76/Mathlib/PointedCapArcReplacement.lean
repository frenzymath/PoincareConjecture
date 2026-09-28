import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallReplacement
import PoincareConjecture.Proofs.M76.Mathlib.PointedRimArcPartition

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsFinitePLBallPair.pointed_arc_replacement
    {b : Set E} {r u : E → ℝ} {a c : ℝ}
    (hu : IsFinitePLBallPair ℝ (b ∩ {x | c ≤ u x}) (b ∩ {x | u x = c}))
    (hr : IsFinitePLBallPair ℝ (b ∩ {x | a ≤ r x}) (b ∩ {x | r x = a}))
    (hhigh : ∀ x ∈ b, a ≤ r x → c < u x)
    {f : E → F}
    (hf : FinitePiecewiseAffineOn f ((b ∩ {x | r x ≤ a}) ∩ {x | c ≤ u x}))
    (hinj : InjOn f ((b ∩ {x | r x ≤ a}) ∩ {x | c ≤ u x}))
    {D : Set F} (hD : IsFinitePLBallPair ℝ D (f '' (b ∩ {x | r x = a})))
    (hinter : D ∩ (f '' ((b ∩ {x | r x ≤ a}) ∩ {x | c ≤ u x})) =
      f '' (b ∩ {x | r x = a})) :
    IsFinitePLBallPair ℝ (D ∪ (f '' ((b ∩ {x | r x ≤ a}) ∩ {x | c ≤ u x})))
      (f '' (b ∩ {x | u x = c})) := by
  obtain ⟨hcover, hsource, houter⟩ := rim_superlevel_truncated_sublevel_partition hhigh
  have hs : IsFinitePLBallPair ℝ
      ((b ∩ {x | a ≤ r x}) ∪ ((b ∩ {x | r x ≤ a}) ∩ {x | c ≤ u x}))
      (b ∩ {x | u x = c}) := hcover.symm ▸ hu
  have hq : b ∩ {x | r x = a} ⊆ (b ∩ {x | r x ≤ a}) ∩ {x | c ≤ u x} :=
    hsource.symm.subset.trans inter_subset_right
  obtain ⟨e, he, heval⟩ := hf.exists_homeomorph_image hinj
  have hmem (x : ((b ∩ {x | r x ≤ a}) ∩ {x | c ≤ u x} : Set E)) :
      (x : E) ∈ b ∩ {x | r x = a} ↔ (e x : F) ∈ f '' (b ∩ {x | r x = a}) := by
    rw [heval]
    constructor
    · exact fun hx => mem_image_of_mem f hx
    · rintro ⟨y, hy, hyx⟩
      exact hinj (hq hy) x.property hyx ▸ hy
  exact (hs.exists_piece_replacement hr hD hsource hinter houter e he hmem heval).1

end Set
