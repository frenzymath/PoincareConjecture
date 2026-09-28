import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.Vertices



set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem preimage_boundary_component_of_fixed_anchor
    {X : Type*} [TopologicalSpace X] (F : X ≃ₜ X)
    {R C : Set X} {a : X} (hR : F ⁻¹' R = R)
    (ha : a ∈ frontier R) (hC : connectedComponentIn (frontier R) a = C)
    (hfix : F a = a) : F ⁻¹' C = C := by
  have hfront : F ⁻¹' frontier R = frontier R := by rw [F.preimage_frontier, hR]
  have himage : F '' frontier R = frontier R := by
    calc
      F '' frontier R = F '' (F ⁻¹' frontier R) := congrArg (Set.image F) hfront.symm
      _ = frontier R := F.image_preimage _
  have hFC : F '' C = C := by
    rw [← hC, F.image_connectedComponentIn ha, himage, hfix]
  calc
    F ⁻¹' C = F ⁻¹' (F '' C) := congrArg (Set.preimage F) hFC.symm
    _ = C := F.preimage_image _

theorem marked_intersection_image_of_preserving_sets
    {X : Type*} [TopologicalSpace X] (F : X ≃ₜ X)
    {S T C : Set X} {p : X}
    (hT : F ⁻¹' T = T) (hC : F ⁻¹' C = C)
    (hp : (S ∩ T) ∩ C = {p}) :
    ((F '' S) ∩ T) ∩ C = {F p} := by
  have hsets : ((F '' S) ∩ T) ∩ C = F '' ((S ∩ T) ∩ C) := by
    ext y
    constructor
    · rintro ⟨⟨⟨x, hx, rfl⟩, hxT⟩, hxC⟩
      exact ⟨x, ⟨⟨hx, hT.subset hxT⟩, hC.subset hxC⟩, rfl⟩
    · rintro ⟨x, ⟨⟨hx, hxT⟩, hxC⟩, rfl⟩
      exact ⟨⟨mem_image_of_mem F hx, hT.symm.subset hxT⟩, hC.symm.subset hxC⟩
  rw [hsets, hp, image_singleton]

theorem proper_annulus_marks_preserved_of_fixed_anchors
    {E X : Type*} [TopologicalSpace X]
    {A rim lower upper : Set E} {R : Set X} {f : E → X}
    (C : Bool → Set X) (a : Bool → X)
    (ha : ∀ b, a b ∈ frontier R)
    (hC : ∀ b, connectedComponentIn (frontier R) (a b) = C b)
    (hfR : MapsTo f A R)
    (hproper : ∀ x ∈ A, f x ∈ frontier R ↔ x ∈ rim)
    (hlower : ∀ x ∈ A, f x ∈ C false ↔ x ∈ lower)
    (hupper : MapsTo f upper (C true))
    (F : X ≃ₜ X) (hR : F ⁻¹' R = R) (hfix : ∀ b, F (a b) = a b) :
    MapsTo (F ∘ f) A R ∧
      (∀ x ∈ A, (F ∘ f) x ∈ frontier R ↔ x ∈ rim) ∧
      (∀ x ∈ A, (F ∘ f) x ∈ C false ↔ x ∈ lower) ∧
      MapsTo (F ∘ f) upper (C true) := by
  have hmarks (b : Bool) : F ⁻¹' C b = C b :=
    preimage_boundary_component_of_fixed_anchor F hR (ha b) (hC b) (hfix b)
  have hfront : F ⁻¹' frontier R = frontier R := by rw [F.preimage_frontier, hR]
  refine ⟨fun x hx => hR.symm.subset (hfR hx), ?_, ?_,
    fun x hx => (hmarks true).symm.subset (hupper hx)⟩
  · intro x hx
    exact (Set.ext_iff.mp hfront (f x)).trans (hproper x hx)
  · intro x hx
    exact (Set.ext_iff.mp (hmarks false) (f x)).trans (hlower x hx)

theorem boundary_marks_of_proper_rim_agreement
    {E X : Type*} [TopologicalSpace X]
    {A rim : Set E} {R C : Set X} {f k : E → X}
    (H : X ≃ₜ X) (hC : C ⊆ frontier R) (hHC : H ⁻¹' C = C)
    (hfp : ∀ x ∈ A, f x ∈ frontier R ↔ x ∈ rim)
    (hkp : ∀ x ∈ A, k x ∈ frontier R ↔ x ∈ rim)
    (hrim : EqOn k (H ∘ f) (A ∩ rim)) :
    ∀ x ∈ A, k x ∈ C ↔ f x ∈ C := by
  intro x hx
  constructor
  · intro hkC
    have hxr := (hkp x hx).mp (hC hkC)
    rw [hrim ⟨hx, hxr⟩] at hkC
    exact hHC.subset hkC
  · intro hfC
    have hxr := (hfp x hx).mp (hC hfC)
    rw [hrim ⟨hx, hxr⟩]
    exact hHC.symm.subset hfC

theorem marked_intersections_of_proper_rim_agreement
    {E X : Type*} [TopologicalSpace X]
    {A rim : Set E} {R T C : Set X} {f k : E → X}
    (H : X ≃ₜ X)
    (hC : C ⊆ frontier R) (hHC : H ⁻¹' C = C) (hHT : H ⁻¹' T = T)
    (hfp : ∀ x ∈ A, f x ∈ frontier R ↔ x ∈ rim)
    (hkp : ∀ x ∈ A, k x ∈ frontier R ↔ x ∈ rim)
    (hrim : EqOn k (H ∘ f) (A ∩ rim)) :
    ((k '' A) ∩ T) ∩ C = H '' (((f '' A) ∩ T) ∩ C) := by
  ext y
  constructor
  · rintro ⟨⟨⟨x, hx, rfl⟩, hxT⟩, hxC⟩
    have hxr := (hkp x hx).mp (hC hxC)
    have heq := hrim ⟨hx, hxr⟩
    rw [heq] at hxT hxC
    exact ⟨f x, ⟨⟨mem_image_of_mem f hx, hHT.subset hxT⟩,
      hHC.subset hxC⟩, heq.symm⟩
  · rintro ⟨y, ⟨⟨⟨x, hx, rfl⟩, hxT⟩, hxC⟩, rfl⟩
    have hxr := (hfp x hx).mp (hC hxC)
    exact ⟨⟨⟨x, hx, hrim ⟨hx, hxr⟩⟩, hHT.symm.subset hxT⟩, hHC.symm.subset hxC⟩

end PoincareConjecture.M76
