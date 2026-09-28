import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallBoundarySide










set_option autoImplicit false

open Set

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {d b c R : Set X}





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
