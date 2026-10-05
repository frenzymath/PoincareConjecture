import PoincareLib.Topology.Manifold.Surgery.Event.Two.TwoChartComparison

/-!
# Extending a region comparison across its actual central collar

An exact equivalence of two open regions matches their actual punctured
collars. Add only the two central images. The original maps extend through
the collars to an equivalence of the enlarged open regions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable {A B : GeneralizedSliceCarrier.{u}}

section OneCollar

variable
  (c : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    RoundCylinderSpace A.carrier ∞)
  {U : Set A.carrier} {a : ℝ} (ha : 0 < a)
  (hc : c.source = Set.univ ×ˢ Set.Ioo (-a) a)
  (hpunct : ∀ z ∈ Set.univ ×ˢ Set.Ioo (-a) a, z.2 ≠ 0 → c z ∈ U)

include ha hc hpunct

/-- Adding the actual zero section fills exactly the missing part of the collar target. -/
theorem collarRegion_union_target :
    U ∪ comparisonCentralSphere c = U ∪ c.target := by
  apply Set.Subset.antisymm
  · exact Set.union_subset_union_right U (comparisonCentral_subset_target c ha hc)
  · rintro x (hx | hx)
    · exact Or.inl hx
    · let z := c.symm x
      have hz : z ∈ Set.univ ×ˢ Set.Ioo (-a) a := hc ▸ c.map_target hx
      have hzx : c z = x := c.toPartialEquiv.right_inv hx
      by_cases hz0 : z.2 = 0
      · exact Or.inr ⟨z, ⟨Set.mem_univ _, hz0⟩, hzx⟩
      · exact Or.inl (hzx ▸ hpunct z hz hz0)

/-- The region enlarged by its actual central sphere is open. -/
theorem collarRegion_isOpen (hU : IsOpen U) :
    IsOpen (U ∪ comparisonCentralSphere c) := by
  rw [collarRegion_union_target c ha hc hpunct]
  exact hU.union c.open_target

end OneCollar

variable
  (cA : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    RoundCylinderSpace A.carrier ∞)
  (cB : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    RoundCylinderSpace B.carrier ∞)
  {U : Set A.carrier} {V : Set B.carrier}
  (E : SurgeryRegionEquivalence A B U V)

/-- At the central image use the literal collar comparison; elsewhere keep the original map. -/
noncomputable def collarRegionComparisonMap (x : A.carrier) : B.carrier := by
  classical
  exact if x ∈ comparisonCentralSphere cA then cB (cA.symm x) else E.map x

/-- Every point outside the actual central sphere keeps its supplied map. -/
theorem collarRegionComparisonMap_off {x : A.carrier}
    (hx : x ∉ comparisonCentralSphere cA) :
    collarRegionComparisonMap cA cB E x = E.map x := by
  classical
  simp only [collarRegionComparisonMap, if_neg hx]

variable {a : ℝ} (ha : 0 < a)
  (hcA : cA.source = Set.univ ×ˢ Set.Ioo (-a) a)
  (hcB : cB.source = Set.univ ×ˢ Set.Ioo (-a) a)
  (hUA : Disjoint U (comparisonCentralSphere cA))
  (hVB : Disjoint V (comparisonCentralSphere cB))
  (hpunctA : ∀ z ∈ Set.univ ×ˢ Set.Ioo (-a) a, z.2 ≠ 0 → cA z ∈ U)
  (hpunctB : ∀ z ∈ Set.univ ×ˢ Set.Ioo (-a) a, z.2 ≠ 0 → cB z ∈ V)
  (hmatch : ∀ z ∈ Set.univ ×ˢ Set.Ioo (-a) a, z.2 ≠ 0 → E.map (cA z) = cB z)

include ha hcA hmatch in
/-- Punctured matching extends to the entire actual collar, including its zero section. -/
theorem collarRegionComparisonMap_collar {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-a) a) :
    collarRegionComparisonMap cA cB E (cA z) = cB z := by
  classical
  have hsource : z ∈ cA.source := hcA.symm ▸ hz
  by_cases hz0 : z.2 = 0
  · have hcentral := (comparisonCentral_mem_iff cA ha hcA hsource).mpr hz0
    simp only [collarRegionComparisonMap, if_pos hcentral]
    have hleft : cA.symm (cA z) = z := cA.toPartialEquiv.left_inv hsource
    rw [hleft]
  · rw [collarRegionComparisonMap_off cA cB E
      (fun h => hz0 ((comparisonCentral_mem_iff cA ha hcA hsource).mp h))]
    exact hmatch z hz hz0

include ha hcA hmatch in
/-- Throughout the open collar target the extension is the actual chart composition. -/
theorem collarRegionComparisonMap_target {x : A.carrier} (hx : x ∈ cA.target) :
    collarRegionComparisonMap cA cB E x = cB (cA.symm x) := by
  have hz : cA.symm x ∈ Set.univ ×ˢ Set.Ioo (-a) a := hcA ▸ cA.map_target hx
  have h := collarRegionComparisonMap_collar cA cB E ha hcA hmatch hz
  have hright : cA (cA.symm x) = x := cA.toPartialEquiv.right_inv hx
  rwa [hright] at h

include hpunctA hmatch in
/-- Exact inverse identities on the original region force matching in the reverse direction. -/
theorem collarRegionComparison_inverse_matching
    (z : RoundCylinderSpace) (hz : z ∈ Set.univ ×ˢ Set.Ioo (-a) a)
    (hz0 : z.2 ≠ 0) : (reverseRegions E).map (cB z) = cA z := by
  change E.inverse (cB z) = cA z
  rw [← hmatch z hz hz0]
  exact E.left_inverse (hpunctA z hz hz0)

include ha hcA hcB hUA hmatch in
/-- The extension maps the original region and its central image into the corresponding union. -/
theorem collarRegionComparisonMap_mapsTo :
    Set.MapsTo (collarRegionComparisonMap cA cB E)
      (U ∪ comparisonCentralSphere cA) (V ∪ comparisonCentralSphere cB) := by
  rintro x (hx | hx)
  · rw [collarRegionComparisonMap_off cA cB E
      (Set.disjoint_left.mp hUA hx)]
    exact Or.inl (E.map_image.subset (Set.mem_image_of_mem _ hx))
  · obtain ⟨z, hz, rfl⟩ := hx
    have hsource : z ∈ Set.univ ×ˢ Set.Ioo (-a) a :=
      hcA ▸ comparisonCentral_source cA ha hcA hz
    rw [collarRegionComparisonMap_collar cA cB E ha hcA hmatch hsource]
    exact Or.inr ⟨z, hz, rfl⟩

include ha hcA hcB hUA hVB hpunctA hmatch in
/-- The two extensions are inverse on the exact enlarged original region. -/
theorem collarRegionComparisonMap_left_inverse :
    Set.LeftInvOn (collarRegionComparisonMap cB cA (reverseRegions E))
      (collarRegionComparisonMap cA cB E) (U ∪ comparisonCentralSphere cA) := by
  rintro x (hx | hx)
  · have hy : E.map x ∈ V := E.map_image.subset (Set.mem_image_of_mem _ hx)
    rw [collarRegionComparisonMap_off cA cB E (Set.disjoint_left.mp hUA hx),
      collarRegionComparisonMap_off cB cA (reverseRegions E) (Set.disjoint_left.mp hVB hy)]
    exact E.left_inverse hx
  · obtain ⟨z, hz, rfl⟩ := hx
    have hsource : z ∈ Set.univ ×ˢ Set.Ioo (-a) a :=
      hcA ▸ comparisonCentral_source cA ha hcA hz
    rw [collarRegionComparisonMap_collar cA cB E ha hcA hmatch hsource,
      collarRegionComparisonMap_collar cB cA (reverseRegions E) ha hcB
        (collarRegionComparison_inverse_matching cA cB E hpunctA hmatch) hsource]

include ha hcA hcB hUA hmatch in
/-- Smoothness is local on the supplied open region and the actual open collar target. -/
theorem collarRegionComparisonMap_smooth (hU : IsOpen U) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (collarRegionComparisonMap cA cB E)
      (U ∪ comparisonCentralSphere cA) := by
  have hlocal : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (fun x => cB (cA.symm x)) cA.target := by
    apply cB.contMDiffOn_toFun.comp cA.contMDiffOn_invFun
    intro x hx
    rw [hcB, ← hcA]
    exact cA.map_target hx
  rintro x (hx | hx)
  · apply ContMDiffAt.contMDiffWithinAt
    apply (E.map_smooth.contMDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact collarRegionComparisonMap_off cA cB E (Set.disjoint_left.mp hUA hy)
  · have htarget : x ∈ cA.target := comparisonCentral_subset_target cA ha hcA hx
    apply ContMDiffAt.contMDiffWithinAt
    apply (hlocal.contMDiffAt (cA.open_target.mem_nhds htarget)).congr_of_eventuallyEq
    filter_upwards [cA.open_target.mem_nhds htarget] with y hy
    exact collarRegionComparisonMap_target cA cB E ha hcA hmatch hy

/-- Matching actual punctured collars extends an exact open-region equivalence through
the central images. This is the local handle-region comparison in Proposition 15.3,
pp. 357-358; no statement about the rest of either carrier is assumed. -/
noncomputable def collarRegionComparison (hU : IsOpen U) (hV : IsOpen V) :
    SurgeryRegionEquivalence A B (U ∪ comparisonCentralSphere cA)
      (V ∪ comparisonCentralSphere cB) := by
  let f := collarRegionComparisonMap cA cB E
  let g := collarRegionComparisonMap cB cA (reverseRegions E)
  have hmatch' := collarRegionComparison_inverse_matching cA cB E hpunctA hmatch
  have hf := collarRegionComparisonMap_mapsTo cA cB E ha hcA hcB hUA hmatch
  have hg := collarRegionComparisonMap_mapsTo cB cA (reverseRegions E)
    ha hcB hcA hVB hmatch'
  have hleft := collarRegionComparisonMap_left_inverse cA cB E
    ha hcA hcB hUA hVB hpunctA hmatch
  have hright := collarRegionComparisonMap_left_inverse cB cA (reverseRegions E)
    ha hcB hcA hVB hUA hpunctB hmatch'
  exact {
    map := f
    inverse := g
    map_image := Set.Subset.antisymm (Set.image_subset_iff.mpr hf)
      (fun y hy => ⟨g y, hg hy, hright hy⟩)
    inverse_image := Set.Subset.antisymm (Set.image_subset_iff.mpr hg)
      (fun x hx => ⟨f x, hf hx, hleft hx⟩)
    left_inverse := hleft
    right_inverse := hright
    map_smooth := collarRegionComparisonMap_smooth cA cB E ha hcA hcB hUA hmatch hU
    inverse_smooth := collarRegionComparisonMap_smooth cB cA (reverseRegions E)
      ha hcB hcA hVB hmatch' hV }

end PoincareMT.M38
