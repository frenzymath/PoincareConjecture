


import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactness.Compact









set_option autoImplicit false

open Set

namespace Poincare.Topology


theorem finite_connectedComponents_of_finite_preconnected_cover
    {X I : Type*} [TopologicalSpace X] [Finite I] (U : I → Set X)
    (hconnected : ∀ i, IsPreconnected (U i)) (hcover : ⋃ i, U i = univ) :
    Finite (ConnectedComponents X) := by
  have hi (i : I) : (ConnectedComponents.mk '' U i).Subsingleton := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ConnectedComponents.coe_eq_coe'.mpr
      ((hconnected i).subset_connectedComponent hy hx)
  have hfinite := finite_iUnion (fun i => (hi i).finite)
  rw [← image_iUnion, hcover, image_univ, ConnectedComponents.range_coe] at hfinite
  exact finite_univ_iff.mp hfinite


theorem finite_connectedComponents_of_finite_preconnected_cover_set
    {X I : Type*} [TopologicalSpace X] [Finite I] {S : Set X} (U : I → Set X)
    (hconnected : ∀ i, IsPreconnected (U i)) (hcover : ⋃ i, U i = S) :
    Finite (ConnectedComponents S) := by
  apply finite_connectedComponents_of_finite_preconnected_cover
    (fun i => (Subtype.val : S → X) ⁻¹' U i)
  · intro i
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [image_preimage_eq_inter_range, Subtype.range_val,
      inter_eq_left.mpr (hcover ▸ subset_iUnion U i)]
    exact hconnected i
  · ext x
    simp only [mem_iUnion, mem_preimage, mem_univ, iff_true]
    exact mem_iUnion.mp (hcover.symm ▸ x.property)

private def mapComponents {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) : ConnectedComponents X → ConnectedComponents Y :=
  fun q => q.lift (fun x => ConnectedComponents.mk (f x)) (fun x y hxy => by
    apply ConnectedComponents.coe_eq_coe'.mpr
    exact hf.mapsTo_connectedComponent y (connectedComponent_eq_iff_mem.mp hxy))


theorem finite_connectedComponents_of_continuous_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Finite (ConnectedComponents X)] {f : X → Y}
    (hf : Continuous f) (hsurj : Function.Surjective f) :
    Finite (ConnectedComponents Y) := by
  apply Finite.of_surjective (mapComponents f hf)
  intro q
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe q
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨ConnectedComponents.mk x, rfl⟩


theorem finite_connectedComponents_image_of_continuousOn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set X} [Finite (ConnectedComponents S)] {f : X → Y}
    (hf : ContinuousOn f S) : Finite (ConnectedComponents (f '' S)) := by
  let g : S → (f '' S) := fun x => ⟨f x, mem_image_of_mem f x.property⟩
  apply finite_connectedComponents_of_continuous_surjective
    (f := g) (hf.domRestrict.subtype_mk _)
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩



theorem finite_connectedComponents_compl_of_locally_finite
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (hfront : ∀ x ∈ Kᶜ, (frontier (connectedComponentIn Kᶜ x) ∩ K).Nonempty)
    (hloc : ∀ x ∈ K, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ Finite (ConnectedComponents ((U \ K) : Set X))) :
    Finite (ConnectedComponents (Kᶜ : Set X)) := by
  classical
  choose U hopen hmem hfinite using fun x : K => hloc x x.property
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hopen (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  let D (p : s) : Set X := U p.val \ K
  let inclusion (p : s) : D p → (Kᶜ : Set X) := fun z => ⟨z.val, z.property.2⟩
  have hcont (p : s) : Continuous (inclusion p) := continuous_subtype_val.subtype_mk _
  let F : (Σ p : s, ConnectedComponents (D p)) → ConnectedComponents (Kᶜ : Set X) :=
    fun q => mapComponents (inclusion q.1) (hcont q.1) q.2
  have (p : s) : Finite (ConnectedComponents (D p)) := hfinite p.val
  apply Finite.of_surjective F
  intro q
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
  obtain ⟨y, hyfront, hyK⟩ := hfront x x.property
  obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hs hyK)
  obtain ⟨z, hzU, hzcomp⟩ :=
    mem_closure_iff.mp (frontier_subset_closure hyfront) _ (hopen p) hyp
  have hzK : z ∈ Kᶜ := connectedComponentIn_subset Kᶜ x hzcomp
  refine ⟨⟨⟨p, hp⟩, ConnectedComponents.mk ⟨z, hzU, hzK⟩⟩, ?_⟩
  change ConnectedComponents.mk (⟨z, hzK⟩ : (Kᶜ : Set X)) = ConnectedComponents.mk x
  apply ConnectedComponents.coe_eq_coe'.mpr
  rw [connectedComponentIn_eq_image x.property] at hzcomp
  obtain ⟨a, ha, rfl⟩ := hzcomp
  exact ha

end Poincare.Topology
