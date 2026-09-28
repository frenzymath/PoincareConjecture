import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.EmbeddedPrism



set_option autoImplicit false
noncomputable section
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductGluing

local notation "I" => Icc (0 : ℝ) 1

theorem exists_homeomorph_of_attached_products
    {X C D : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace C] [CompactSpace C]
    [TopologicalSpace D] [CompactSpace D]
    {N B : Set X}
    (HN : (C × I) ≃ₜ N) (HB : (D × I) ≃ₜ B)
    (hcollision : ∀ (x : C) (y : D) (s t : I),
      (HN (x,s) : X) = HB (y,t) ↔
        (HN (x,⟨0,by norm_num⟩) : X) = HB (y,⟨0,by norm_num⟩) ∧ s = t) :
    ∃ H : ((range (fun x : C => (HN (x,⟨0,by norm_num⟩) : X)) ∪
        range (fun y : D => (HB (y,⟨0,by norm_num⟩) : X)) : Set X) × I) ≃ₜ
        ((N ∪ B : Set X) : Type),
      (∀ x t, (H (⟨(HN (x,⟨0,by norm_num⟩) : X),
        mem_union_left (range (fun y : D => (HB (y,⟨0,by norm_num⟩) : X)))
          (mem_range_self x)⟩,t) : X) = HN (x,t)) ∧
      ∀ y t, (H (⟨(HB (y,⟨0,by norm_num⟩) : X),
        mem_union_right (range (fun x : C => (HN (x,⟨0,by norm_num⟩) : X)))
          (mem_range_self y)⟩,t) : X) = HB (y,t) := by
  let C' : Bool → Type := fun i => match i with
    | false => C
    | true => D
  letI (i : Bool) : TopologicalSpace (C' i) := by
    cases i <;> dsimp [C'] <;> infer_instance
  letI (i : Bool) : CompactSpace (C' i) := by
    cases i <;> dsimp [C'] <;> infer_instance
  let b : ∀ i, C' i → X := fun i => match i with
    | false => fun x => (HN (x,⟨0,by norm_num⟩) : X)
    | true => fun y => (HB (y,⟨0,by norm_num⟩) : X)
  let f : ∀ i, C' i × I → X := fun i => match i with
    | false => fun z => (HN (z.1,z.2) : X)
    | true => fun z => (HB (z.1,z.2) : X)
  have hf : ∀ i, Continuous (f i) := by
    intro i
    cases i
    · exact continuous_subtype_val.comp HN.continuous
    · exact continuous_subtype_val.comp HB.continuous
  have hzero : ∀ i x, f i (x,⟨0,by norm_num⟩) = b i x := by
    intro i x
    cases i <;> rfl
  have hcollision' : ∀ i j (x : C' i) (y : C' j) (s t : I),
      f i (x,s) = f j (y,t) ↔ b i x = b j y ∧ s = t := by
    intro i j x y s t
    cases i <;> cases j
    · apply collision_iff_of_injective
      intro p q hpq
      exact HN.injective (Subtype.ext hpq)
    · simpa [b, f, C'] using hcollision x y s t
    · simpa only [eq_comm] using hcollision y x t s
    · apply collision_iff_of_injective
      intro p q hpq
      exact HB.injective (Subtype.ext hpq)
  obtain ⟨H₀,hH,hzeroH⟩ :=
    exists_homeomorph_of_parametrized_pieces C' b f hf hzero hcollision'
  have hbase : (⋃ i, range (b i)) =
      range (fun x : C => (HN (x,⟨0,by norm_num⟩) : X)) ∪
        range (fun y : D => (HB (y,⟨0,by norm_num⟩) : X)) := by
    ext z
    simp [b, C']
  have hrangeN : range (fun z : C × I => (HN z : X)) = N := by
    ext z
    constructor
    · rintro ⟨p,rfl⟩
      exact (HN p).property
    · intro hz
      obtain ⟨p,hp⟩ := HN.surjective ⟨z,hz⟩
      exact ⟨p,congrArg Subtype.val hp⟩
  have hrangeB : range (fun z : D × I => (HB z : X)) = B := by
    ext z
    constructor
    · rintro ⟨p,rfl⟩
      exact (HB p).property
    · intro hz
      obtain ⟨p,hp⟩ := HB.surjective ⟨z,hz⟩
      exact ⟨p,congrArg Subtype.val hp⟩
  have htarget : (⋃ i, range (f i)) = N ∪ B := by
    rw [show (⋃ i, range (f i)) =
      range (fun z : C × I => (HN z : X)) ∪
        range (fun z : D × I => (HB z : X)) by
      ext z
      simp [f, C']]
    rw [hrangeN,hrangeB]
  let sourceChange := (Homeomorph.setCongr hbase.symm).prodCongr (Homeomorph.refl I)
  let targetChange := Homeomorph.setCongr htarget
  let H := sourceChange.trans (H₀.trans targetChange)
  refine ⟨H,?_,?_⟩
  · intro x t
    change (H₀ (⟨b false x,mem_iUnion.mpr ⟨false,mem_range_self x⟩⟩,t) : X) = f false (x,t)
    exact hH false x t
  · intro y t
    change (H₀ (⟨b true y,mem_iUnion.mpr ⟨true,mem_range_self y⟩⟩,t) : X) = f true (y,t)
    exact hH true y t

end PoincareConjecture.M76.Dehn.Annuli.ProductGluing
