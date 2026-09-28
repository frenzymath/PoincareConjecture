import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.ClosedComplement



set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem mem_closedFaceComplement_union_iff
    (K N N₀ N₁ : SimplicialComplex ℝ E)
    (hfaces : N.faces = N₀.faces ∪ N₁.faces)
    (hdis : Disjoint N₀.space N₁.space) {x : E} (hx : x ∈ N₀.space) :
    x ∈ (K.closedFaceComplement N).space ↔
      x ∈ (K.closedFaceComplement N₀).space := by
  rw [K.closedFaceComplement_space N, K.closedFaceComplement_space N₀]
  constructor
  · intro h
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp h
    refine mem_iUnion₂.mpr ⟨t, ⟨ht.1, ?_⟩, hxt⟩
    intro htN
    exact ht.2 (hfaces ▸ Or.inl htN)
  · intro h
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp h
    refine mem_iUnion₂.mpr ⟨t, ⟨ht.1, ?_⟩, hxt⟩
    intro htN
    rw [hfaces] at htN
    rcases htN with htN | htN
    · exact ht.2 htN
    · exact disjoint_left.mp hdis hx (N₁.convexHull_subset_space htN hxt)

theorem space_eq_union_of_faces_eq_union
    (N N₀ N₁ : SimplicialComplex ℝ E)
    (hfaces : N.faces = N₀.faces ∪ N₁.faces) :
    N.space = N₀.space ∪ N₁.space := by
  ext x
  simp only [mem_space_iff, hfaces, mem_union]
  aesop

end Geometry.SimplicialComplex
