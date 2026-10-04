import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallBoundarySide

/-!
# One-sidedness of a planar cap on a cut surface disk

The cap is at zero height and meets the cut disk only on its rim.
The disk's boundary-side conclusion therefore gives the exact
cap/strict-side-closure incidence needed for its deformation.
See Alexander 1924, pp. 7--8 and M76 derivation 156.
-/

set_option autoImplicit false

open Set

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {d b c R : Set X}

/-- A zero-height cap meeting a finite PL disk only on its
connected punctured rim avoids one strict-height closure except
at the puncture, when all other zeros lie in a closed residual
set meeting the rim only there. See M76 derivation 156. -/
theorem IsFinitePLBallPair.cap_height_side (hd : IsFinitePLBallPair E d b)
    (f : X → ℝ) (hf : ContinuousOn f d) (hbzero : ∀ x ∈ b, f x = 0)
    (hcplane : ∀ x ∈ c, f x = 0) (hcmeet : c ∩ d ⊆ b)
    (q : X) (hbconn : IsPreconnected (b \ {q})) (hR : IsClosed R)
    (hbR : b ∩ R ⊆ {q}) (hzeros : (d ∩ {x | f x = 0}) \ b ⊆ R) :
    c ∩ closure ((d ∪ c) ∩ {x | f x < 0}) ⊆ {q} ∨
      c ∩ closure ((d ∪ c) ∩ {x | 0 < f x}) ⊆ {q} := by
  have hneg : (d ∪ c) ∩ {x | f x < 0} = d ∩ {x | f x < 0} := by
    ext x
    constructor
    · rintro ⟨hxd | hxc, hxneg⟩
      · exact ⟨hxd, hxneg⟩
      · exact (ne_of_lt hxneg (hcplane x hxc)).elim
    · exact fun hx => ⟨Or.inl hx.1, hx.2⟩
  have hpos : (d ∪ c) ∩ {x | 0 < f x} = d ∩ {x | 0 < f x} := by
    ext x
    constructor
    · rintro ⟨hxd | hxc, hxpos⟩
      · exact ⟨hxd, hxpos⟩
      · exact (ne_of_gt hxpos (hcplane x hxc)).elim
    · exact fun hx => ⟨Or.inl hx.1, hx.2⟩
  rw [hneg, hpos]
  rcases hd.boundary_height_side f hf hbzero q hbconn hR hbR hzeros with hn | hp
  · left
    rintro x ⟨hxc, hxcl⟩
    have hxd : x ∈ d := closure_minimal inter_subset_left hd.isCompact.isClosed hxcl
    exact hn ⟨hcmeet ⟨hxc, hxd⟩, hxcl⟩
  · right
    rintro x ⟨hxc, hxcl⟩
    have hxd : x ∈ d := closure_minimal inter_subset_left hd.isCompact.isClosed hxcl
    exact hp ⟨hcmeet ⟨hxc, hxd⟩, hxcl⟩

end Set
