import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.Disjoint
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SupportedChartRegion



set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem image_mem_iff_of_eqOn_preserved_open
    {X : Type*} [TopologicalSpace X] (F G : X ≃ₜ X)
    {S U : Set X} (hFG : EqOn F G U) (hGU : G ⁻¹' U = U)
    {y : X} (hy : y ∈ U) : y ∈ F '' S ↔ y ∈ G '' S := by
  have hpre : G.symm y ∈ U := hGU.subset (by simpa only [mem_preimage, G.apply_symm_apply])
  have hF : F (G.symm y) = y := (hFG hpre).trans (G.apply_symm_apply y)
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hxeq : x = G.symm y := F.injective (hxy.trans hF.symm)
    exact ⟨G.symm y, hxeq ▸ hx, G.apply_symm_apply y⟩
  · rintro ⟨x, hx, hxy⟩
    have hxeq : x = G.symm y := G.injective (hxy.trans (G.apply_symm_apply y).symm)
    exact ⟨G.symm y, hxeq ▸ hx, hF⟩

theorem image_contacts_covered_after_local_motions
    {X κ : Type*} [TopologicalSpace X]
    (F : X ≃ₜ X) (G : κ → X ≃ₜ X)
    {S P K : Set X} (U A W : κ → Set X)
    (hK : K ⊆ ⋃ i, A i) (hAU : ∀ i, A i ⊆ U i)
    (hfix : EqOn F id Kᶜ)
    (hGfix : ∀ i, EqOn (G i) id (A i)ᶜ)
    (hFG : ∀ i, EqOn F (G i) (U i))
    (hnew : ∀ i, ((G i '' S) \ S) ⊆ W i)
    (hold : S ∩ P ⊆ ⋃ i, W i) :
    (F '' S) ∩ P ⊆ ⋃ i, W i := by
  intro y hy
  by_cases hyS : y ∈ S
  · exact hold ⟨hyS, hy.2⟩
  have hyK : y ∈ K := by
    by_contra hn
    obtain ⟨x, hx, hxy⟩ := hy.1
    exact hyS ((F.injective (hxy.trans (hfix hn).symm)) ▸ hx)
  obtain ⟨i, hyA⟩ := mem_iUnion.mp (hK hyK)
  have hGU : G i ⁻¹' U i = U i :=
    (G i).injective.preimage_eq_self_of_eqOn_compl
      (fun x hx => hGfix i (fun h => hx (hAU i h)))
  have hyG := (image_mem_iff_of_eqOn_preserved_open F (G i) (hFG i) hGU (hAU i hyA)).mp hy.1
  exact mem_iUnion.mpr ⟨i, hnew i ⟨hyG, hyS⟩⟩

theorem image_vertices_avoided_after_local_motions
    {X κ : Type*} [TopologicalSpace X]
    (F : X ≃ₜ X) (G : κ → X ≃ₜ X)
    {S P V : Set X} (U A W : κ → Set X)
    (hAU : ∀ i, A i ⊆ U i) (hWU : ∀ i, W i ⊆ U i)
    (hGfix : ∀ i, EqOn (G i) id (A i)ᶜ)
    (hFG : ∀ i, EqOn F (G i) (U i))
    (hcover : (F '' S) ∩ P ⊆ ⋃ i, W i)
    (havoid : ∀ i, Disjoint (G i '' S) (V ∩ W i)) :
    Disjoint (F '' S) (V ∩ P) := by
  apply disjoint_left.mpr
  rintro y hy ⟨hyV, hyP⟩
  obtain ⟨i, hyW⟩ := mem_iUnion.mp (hcover ⟨hy, hyP⟩)
  have hGU : G i ⁻¹' U i = U i :=
    (G i).injective.preimage_eq_self_of_eqOn_compl
      (fun x hx => hGfix i (fun h => hx (hAU i h)))
  have hyG := (image_mem_iff_of_eqOn_preserved_open F (G i) (hFG i) hGU (hWU i hyW)).mp hy
  exact disjoint_left.mp (havoid i) hyG ⟨hyV, hyW⟩

end PoincareConjecture.M76
