import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.FiniteCapComponentCarriers

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem isClopen_finite_cap_selection
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite κ]
    {P A : Set E} (hA : IsClosed A) (hrest : IsClosed (P \ A)) (hAP : A ⊆ P)
    (C B : κ → Set E) (hC : ∀ i, IsFinitePLBallPair V3 (C i) (B i))
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    (hcontact : ∀ i, P ∩ C i = B i) (t : Finset κ)
    (hselected : ∀ i ∈ t, B i ⊆ A)
    (homitted : ∀ i, i ∉ t → Disjoint (B i) A) :
    IsClopen ((Subtype.val : (P ∪ ⋃ i, C i : Set E) → E) ⁻¹'
      (A ∪ ⋃ i : t, C i)) := by
  classical
  let T := A ∪ ⋃ i : t, C i
  let U := (P \ A) ∪ ⋃ i : {i // i ∉ t}, C i
  have hT : IsClosed T := hA.union
    (isClosed_iUnion_of_finite fun i : t => (hC i).isCompact.isClosed)
  have hU : IsClosed U := hrest.union
    (isClosed_iUnion_of_finite fun i : {i // i ∉ t} => (hC i).isCompact.isClosed)
  have hTU : Disjoint T U := by
    apply disjoint_left.mpr
    intro x hxT hxU
    rcases hxT with hxA | hxC
    · rcases hxU with hxP | hxC
      · exact hxP.2 hxA
      · obtain ⟨i,hxi⟩ := mem_iUnion.mp hxC
        exact disjoint_left.mp (homitted i i.property)
          ((hcontact i).subset ⟨hAP hxA,hxi⟩) hxA
    · obtain ⟨i,hxi⟩ := mem_iUnion.mp hxC
      rcases hxU with hxP | hxC
      · exact hxP.2 (hselected i i.property ((hcontact i).subset ⟨hxP.1,hxi⟩))
      · obtain ⟨j,hxj⟩ := mem_iUnion.mp hxC
        exact disjoint_left.mp (hdis (show (i : κ) ≠ j from
          fun hij => j.property (hij ▸ i.property))) hxi hxj
  have hcov : T ∪ U = P ∪ ⋃ i, C i := by
    apply Subset.antisymm
    · rintro x ((hx | hx) | (hx | hx))
      · exact Or.inl (hAP hx)
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact Or.inr (mem_iUnion.mpr ⟨i,hi⟩)
      · exact Or.inl hx.1
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact Or.inr (mem_iUnion.mpr ⟨i,hi⟩)
    · rintro x (hx | hx)
      · by_cases hxA : x ∈ A
        · exact Or.inl (Or.inl hxA)
        · exact Or.inr (Or.inl ⟨hx,hxA⟩)
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        by_cases hit : i ∈ t
        · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨i,hit⟩,hi⟩))
        · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨⟨i,hit⟩,hi⟩))
  refine ⟨hT.preimage continuous_subtype_val,?_⟩
  have heq : (Subtype.val : (P ∪ ⋃ i, C i : Set E) → E) ⁻¹' T =
      ((Subtype.val : (P ∪ ⋃ i, C i : Set E) → E) ⁻¹' U)ᶜ := by
    ext x
    constructor
    · exact fun hx hu => disjoint_left.mp hTU hx hu
    · intro hx
      exact (hcov.symm.subset x.property).resolve_right hx
  rw [heq]
  exact (hU.preimage continuous_subtype_val).isOpen_compl

end PoincareConjecture.M76
