import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.SelectedCapComponent








set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem exists_interior_retained_replacement
    {X Y κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {P A R : Set X} (hAP : A ⊆ P) (hfront : frontier P ⊆ A)
    (Q : κ → Set X) (C : κ → Set Y)
    (hcover : A ∪ ⋃ i, Q i = P) (hQR : ∀ i, Q i ⊆ R)
    (f : X → Y) (G : P ≃ₜ (f '' A ∪ ⋃ i, C i : Set Y))
    (hG : ∀ (x : X) (hx : x ∈ A), (G ⟨x,hAP hx⟩ : Y) = f x)
    (hGQ : ∀ i (x : P), (x : X) ∈ Q i ↔ (G x : Y) ∈ C i) :
    (∀ x : P, (x : X) ∈ R ↔ (G x : Y) ∈ f '' (A ∩ R) ∪ ⋃ i, C i) ∧
    ∃ H : interior P ≃ₜ
      ((f '' A ∪ ⋃ i, C i) \ f '' frontier P : Set Y),
      (∀ x : interior P, (H x : Y) = G ⟨x,interior_subset x.property⟩) ∧
      (∀ x : interior P, (x : X) ∈ A → (H x : Y) = f x) ∧
      ∀ x : interior P, (x : X) ∈ R ↔ (H x : Y) ∈ f '' (A ∩ R) ∪ ⋃ i, C i := by
  have hinner (x : P) : (x : X) ∈ R ↔ (G x : Y) ∈ f '' (A ∩ R) ∪ ⋃ i, C i := by
    constructor
    · intro hxR
      rcases hcover.symm.subset x.property with hxA | hxQ
      · exact Or.inl ⟨x,⟨hxA,hxR⟩,(hG x hxA).symm⟩
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hxQ
        exact Or.inr (mem_iUnion.mpr ⟨i,(hGQ i x).mp hi⟩)
    · rintro (⟨y,hy,hyeq⟩ | hxC)
      · have heq : G ⟨y,hAP hy.1⟩ = G x := Subtype.ext ((hG y hy.1).trans hyeq)
        exact congrArg Subtype.val (G.injective heq) ▸ hy.2
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hxC
        exact hQR i ((hGQ i x).mpr hi)
  have hboundary (x : P) : (x : X) ∈ frontier P ↔ (G x : Y) ∈ f '' frontier P := by
    constructor
    · intro hx
      exact ⟨x,hx,(hG x (hfront hx)).symm⟩
    · rintro ⟨y,hy,hyeq⟩
      have heq : G ⟨y,hAP (hfront hy)⟩ = G x :=
        Subtype.ext ((hG y (hfront hy)).trans hyeq)
      exact congrArg Subtype.val (G.injective heq) ▸ hy
  have hmark (x : P) : (x : X) ∈ interior P ↔
      (G x : Y) ∈ (f '' A ∪ ⋃ i, C i) \ f '' frontier P := by
    rw [mem_sdiff,and_iff_right (G x).property,←hboundary]
    exact mem_interior_iff_notMem_frontier x.property
  let H : interior P ≃ₜ ((f '' A ∪ ⋃ i, C i) \ f '' frontier P : Set Y) :=
    G.restrictSubsets interior_subset sdiff_subset hmark
  exact ⟨hinner,H,fun _ => rfl,fun x hx => hG x hx,
    fun x => hinner ⟨x,interior_subset x.property⟩⟩

end PoincareConjecture.M76
