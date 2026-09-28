import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.FiniteModelCollarTransport

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

theorem exists_retained_open_model_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {R U : Set X} {P C : Set Y}
    (H : R ≃ₜ P) (f : X → Y) (hH : ∀ x : R, (H x : Y) = f x)
    (hUR : U ⊆ R) (hU : IsOpen U) (hP : IsClosed P) (hC : IsClosed C)
    (hdis : Disjoint (f '' U) C) :
    ∃ G : U ≃ₜ f '' U,
      (∀ x : U, (G x : Y) = f x) ∧ f '' U ⊆ P ∪ C ∧
      IsOpen ((Subtype.val : (P ∪ C : Set Y) → Y) ⁻¹' (f '' U)) := by
  have hUP : f '' U ⊆ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hH ⟨x, hUR hx⟩ ▸ (H ⟨x, hUR hx⟩).property
  have hmem (x : R) : (x : X) ∈ U ↔ (H x : Y) ∈ f '' U := by
    constructor
    · intro hx
      exact ⟨x, hx, (hH x).symm⟩
    · rintro ⟨y, hy, hyx⟩
      have heq : H ⟨y, hUR hy⟩ = H x := Subtype.ext ((hH _).trans hyx)
      exact (congrArg Subtype.val (H.injective heq)) ▸ hy
  let G := H.restrictSubsets hUR hUP hmem
  have hopen : IsOpen ((Subtype.val : P → Y) ⁻¹' (f '' U)) :=
    isOpen_relative_model_image H f hH hUR (hU.preimage continuous_subtype_val)
  have hclosed : IsClosed (P \ f '' U) := by
    have h := hP.isClosedMap_subtype_val _ hopen.isClosed_compl
    convert h using 1
    ext y
    simp
  have heq : (P ∪ C) \ f '' U = (P \ f '' U) ∪ C := by
    ext y
    constructor
    · rintro ⟨hy | hy, hn⟩
      · exact Or.inl ⟨hy, hn⟩
      · exact Or.inr hy
    · rintro (hy | hy)
      · exact ⟨Or.inl hy.1, hy.2⟩
      · exact ⟨Or.inr hy, fun hx => disjoint_left.mp hdis hx hy⟩
  have hopenUnion := ((heq ▸ hclosed.union hC).preimage
    (continuous_subtype_val : Continuous (Subtype.val : (P ∪ C : Set Y) → Y))).isOpen_compl
  refine ⟨G, fun x => hH ⟨x, hUR x.property⟩, hUP.trans subset_union_left, ?_⟩
  convert hopenUnion using 1
  ext y
  change (y : Y) ∈ f '' U ↔ ¬((y : Y) ∈ P ∪ C ∧ (y : Y) ∉ f '' U)
  simp only [y.property, true_and, not_not]

end PoincareConjecture.M76
