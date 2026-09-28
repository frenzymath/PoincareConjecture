import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.SymmetricPrismTrim



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem prismTrim_inter_global_rectangle
    {E : Type*} [TopologicalSpace E] {A B M : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ))) :
    prismTrim H ∩ M = prismTrim G := by
  have hmem (x : M) : (x : E) ∈ prismTrim H ↔ (x : E) ∈ prismTrim G := by
    let y := G.symm x
    let u : I := ⟨(y : ℝ × ℝ).1,y.property.1⟩
    let t : I := ⟨(y : ℝ × ℝ).2,y.property.2⟩
    have hy : (G ⟨(u,t),u.property,t.property⟩ : E) = x :=
      congrArg Subtype.val (G.apply_symm_apply x)
    have hcoord := prism_inverse_on_global_rectangle H G hMB flip hformula u t
    have hh : (H.symm ⟨x,hMB x.property⟩ : E × ℝ).2 = (fiberFlip flip t : ℝ) := by
      have h := congrArg Prod.snd hcoord
      simpa only [hy] using h
    rw [mem_prismTrim_iff H ⟨x,hMB x.property⟩,mem_prismTrim_iff G x,hh]
    exact fiberFlip_mem_middle_iff flip t
  ext x
  constructor
  · intro hx
    exact (hmem ⟨x,hx.2⟩).mp hx.1
  · intro hx
    have hxM := prismTrim_subset G hx
    exact ⟨(hmem ⟨x,hxM⟩).mpr hx,hxM⟩

theorem prismTrim_intersections_on_shared_rectangles
    {E ρ : Type*} [TopologicalSpace E] {A₀ A₁ B₀ B₁ : Set E}
    (H₀ : (A₀ ×ˢ I : Set (E × ℝ)) ≃ₜ B₀)
    (H₁ : (A₁ ×ˢ I : Set (E × ℝ)) ≃ₜ B₁)
    (M : ρ → Set E) (G : ∀ r, Square ≃ₜ M r)
    (hcontact : B₀ ∩ B₁ = ⋃ r, M r)
    (htrim₀ : ∀ r, prismTrim H₀ ∩ M r = prismTrim (G r))
    (htrim₁ : ∀ r, prismTrim H₁ ∩ M r = prismTrim (G r)) :
    prismTrim H₀ ∩ prismTrim H₁ = ⋃ r, prismTrim (G r) := by
  ext x
  constructor
  · intro hx
    obtain ⟨r,hr⟩ := mem_iUnion.mp (hcontact.subset
      ⟨prismTrim_subset H₀ hx.1,prismTrim_subset H₁ hx.2⟩)
    exact mem_iUnion.mpr ⟨r,(htrim₀ r).subset ⟨hx.1,hr⟩⟩
  · intro hx
    obtain ⟨r,hr⟩ := mem_iUnion.mp hx
    exact ⟨((htrim₀ r).symm.subset hr).1,((htrim₁ r).symm.subset hr).1⟩

end PoincareConjecture.M76.PrismBelt
