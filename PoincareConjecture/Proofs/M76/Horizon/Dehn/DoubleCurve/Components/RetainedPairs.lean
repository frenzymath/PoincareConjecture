import PoincareConjecture.Proofs.M76.Horizon.Dehn.Topology.Mathlib.FiniteClosedComponentPartition

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn

theorem retained_double_locus_eq_paired_components
    {E X I : Type*} {S G K : Set E} {f : E → X}
    (U : I → Set E) (mate : I → I) (partner : G → G)
    (hG : G = {x | x ∈ S ∧ ∃ y ∈ S, f x = f y ∧ x ≠ y})
    (hcover : ⋃ i, U i = G)
    (hpartner : ∀ x : G, f x = f (partner x))
    (hne : ∀ x : G, (x : E) ≠ partner x)
    (hunique : ∀ (x : G) (y : E), y ∈ S → f x = f y → (x : E) ≠ y →
      y = (partner x : E))
    (hmate : ∀ (i : I) (x : G), (x : E) ∈ U i → (partner x : E) ∈ U (mate i))
    (hKS : K ⊆ S) (hwhole : ∀ i, U i ⊆ K ∨ Disjoint (U i) K) :
    {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y} =
      (Subtype.val : K → E) ⁻¹'
        (⋃ i : {i : I // U i ⊆ K ∧ U (mate i) ⊆ K}, U i.val) := by
  have hsub (i : I) : U i ⊆ G := by
    rw [← hcover]
    exact subset_iUnion U i
  have hretain (i : I) {x : E} (hx : x ∈ U i) (hxK : x ∈ K) : U i ⊆ K := by
    rcases hwhole i with h | h
    · exact h
    · exact False.elim (disjoint_left.mp h hx hxK)
  ext x
  constructor
  · rintro ⟨y, hxy, hne'⟩
    have hxG : (x : E) ∈ G := hG.symm ▸ ⟨hKS x.property, y, hKS y.property, hxy, hne'⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover.symm ▸ hxG)
    have hpy : (partner ⟨x, hxG⟩ : E) = y := (hunique ⟨x, hxG⟩ y
      (hKS y.property) hxy hne').symm
    have hym : (y : E) ∈ U (mate i) := hpy ▸ hmate i ⟨x, hxG⟩ hxi
    exact mem_iUnion.mpr ⟨⟨i, hretain i hxi x.property, hretain (mate i) hym y.property⟩, hxi⟩
  · intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    let xG : G := ⟨x, hsub i.val hxi⟩
    have hpK : (partner xG : E) ∈ K := i.property.2 (hmate i.val xG hxi)
    exact ⟨⟨partner xG, hpK⟩, hpartner xG, hne xG⟩

theorem image_retained_double_locus_eq_paired_components
    {E X I : Type*} {S G K : Set E} {f : E → X}
    (U : I → Set E) (mate : I → I) (partner : G → G)
    (hG : G = {x | x ∈ S ∧ ∃ y ∈ S, f x = f y ∧ x ≠ y})
    (hcover : ⋃ i, U i = G)
    (hpartner : ∀ x : G, f x = f (partner x))
    (hne : ∀ x : G, (x : E) ≠ partner x)
    (hunique : ∀ (x : G) (y : E), y ∈ S → f x = f y → (x : E) ≠ y →
      y = (partner x : E))
    (hmate : ∀ (i : I) (x : G), (x : E) ∈ U i → (partner x : E) ∈ U (mate i))
    (hKS : K ⊆ S) (hwhole : ∀ i, U i ⊆ K ∨ Disjoint (U i) K) :
    (Subtype.val : K → E) '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y} =
      ⋃ i : {i : I // U i ⊆ K ∧ U (mate i) ⊆ K}, U i.val := by
  rw [retained_double_locus_eq_paired_components U mate partner hG hcover
    hpartner hne hunique hmate hKS hwhole]
  apply image_preimage_eq_iff.mpr
  simpa only [Subtype.range_coe_subtype, ofPred_mem_eq] using
    (iUnion_subset fun i : {i : I // U i ⊆ K ∧ U (mate i) ⊆ K} ↦ i.property.1)

end PoincareConjecture.M76.Dehn
