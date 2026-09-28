import PoincareConjecture.Proofs.M38.OpenRegionEquivalences

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A B : GeneralizedSliceCarrier.{u}}

def comparisonCentralSphere
    (c : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace A.carrier ∞) : Set A.carrier :=
  c '' (Set.univ ×ˢ ({0} : Set ℝ))

section OneCollar

variable
  (c : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    RoundCylinderSpace A.carrier ∞)
  {a : ℝ} (ha : 0 < a) (hc : c.source = Set.univ ×ˢ Set.Ioo (-a) a)

include ha hc

theorem comparisonCentral_source :
    Set.univ ×ˢ ({0} : Set ℝ) ⊆ c.source := by
  rintro z ⟨hz, hs⟩
  have hs0 : z.2 = 0 := hs
  rw [hc]
  exact ⟨hz, by simpa only [hs0] using neg_neg_of_pos ha,
    by simpa only [hs0] using ha⟩

theorem comparisonCentral_subset_target : comparisonCentralSphere c ⊆ c.target := by
  rintro _ ⟨z, hz, rfl⟩
  exact c.map_source (comparisonCentral_source c ha hc hz)

theorem comparisonCentral_isClosed : IsClosed (comparisonCentralSphere c) := by
  apply IsCompact.isClosed
  exact (isCompact_univ.prod isCompact_singleton).image_of_continuousOn
    (c.contMDiffOn_toFun.continuousOn.mono (comparisonCentral_source c ha hc))

theorem comparisonCentral_mem_iff {z : RoundCylinderSpace} (hz : z ∈ c.source) :
    c z ∈ comparisonCentralSphere c ↔ z.2 = 0 := by
  constructor
  · rintro ⟨w, hw, hmap⟩
    have heq : w = z := c.toPartialEquiv.injOn
      (comparisonCentral_source c ha hc hw) hz hmap
    have hw0 : w.2 = 0 := hw.2
    simpa only [heq] using hw0
  · intro hz0
    exact ⟨z, ⟨Set.mem_univ _, hz0⟩, rfl⟩

end OneCollar

variable
  (cA : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    RoundCylinderSpace A.carrier ∞)
  (cB : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    RoundCylinderSpace B.carrier ∞)
  (E : SurgeryRegionEquivalence A B
    (comparisonCentralSphere cA)ᶜ (comparisonCentralSphere cB)ᶜ)

noncomputable def twoChartComparisonMap (x : A.carrier) : B.carrier := by
  classical
  exact if x ∈ comparisonCentralSphere cA then cB (cA.symm x) else E.map x

theorem twoChartComparisonMap_complement {x : A.carrier}
    (hx : x ∉ comparisonCentralSphere cA) :
    twoChartComparisonMap cA cB E x = E.map x := by
  classical
  simp only [twoChartComparisonMap, if_neg hx]

theorem twoChartComparisonMap_central {x : A.carrier}
    (hx : x ∈ comparisonCentralSphere cA) :
    twoChartComparisonMap cA cB E x = cB (cA.symm x) := by
  classical
  simp only [twoChartComparisonMap, if_pos hx]

variable {a : ℝ} (ha : 0 < a)
  (hcA : cA.source = Set.univ ×ˢ Set.Ioo (-a) a)
  (hcB : cB.source = Set.univ ×ˢ Set.Ioo (-a) a)
  (hmatch : ∀ z ∈ Set.univ ×ˢ Set.Ioo (-a) a, z.2 ≠ 0 →
    E.map (cA z) = cB z)

include ha hcA hmatch in

theorem twoChartComparisonMap_collar {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-a) a) :
    twoChartComparisonMap cA cB E (cA z) = cB z := by
  have hsource : z ∈ cA.source := hcA.symm ▸ hz
  by_cases hz0 : z.2 = 0
  · rw [twoChartComparisonMap_central cA cB E
      ((comparisonCentral_mem_iff cA ha hcA hsource).mpr hz0)]
    have hleft : cA.symm (cA z) = z := cA.toPartialEquiv.left_inv hsource
    rw [hleft]
  · rw [twoChartComparisonMap_complement cA cB E
      (fun h => hz0 ((comparisonCentral_mem_iff cA ha hcA hsource).mp h))]
    exact hmatch z hz hz0

include ha hcA hmatch in

theorem twoChartComparisonMap_target {x : A.carrier} (hx : x ∈ cA.target) :
    twoChartComparisonMap cA cB E x = cB (cA.symm x) := by
  have hz : cA.symm x ∈ Set.univ ×ˢ Set.Ioo (-a) a :=
    hcA ▸ cA.map_target hx
  have hright : cA (cA.symm x) = x := cA.toPartialEquiv.right_inv hx
  have h := twoChartComparisonMap_collar cA cB E ha hcA hmatch hz
  rwa [hright] at h

include ha hcA hmatch in

theorem twoChartComparison_inverse_matching
    (z : RoundCylinderSpace) (hz : z ∈ Set.univ ×ˢ Set.Ioo (-a) a)
    (hz0 : z.2 ≠ 0) : (reverseRegions E).map (cB z) = cA z := by
  have hsource : cA z ∈ (comparisonCentralSphere cA)ᶜ :=
    fun h => hz0 ((comparisonCentral_mem_iff cA ha hcA (hcA.symm ▸ hz)).mp h)
  change E.inverse (cB z) = cA z
  rw [← hmatch z hz hz0]
  exact E.left_inverse hsource

include ha hcA hcB hmatch in

theorem twoChartComparisonMap_left_inverse :
    Function.LeftInverse (twoChartComparisonMap cB cA (reverseRegions E))
      (twoChartComparisonMap cA cB E) := by
  intro x
  by_cases hx : x ∈ comparisonCentralSphere cA
  · obtain ⟨z, hz, rfl⟩ := hx
    have hsource : z ∈ Set.univ ×ˢ Set.Ioo (-a) a :=
      hcA ▸ comparisonCentral_source cA ha hcA hz
    rw [twoChartComparisonMap_collar cA cB E ha hcA hmatch hsource,
      twoChartComparisonMap_collar cB cA (reverseRegions E) ha hcB
        (twoChartComparison_inverse_matching cA cB E ha hcA hmatch) hsource]
  · have hy : E.map x ∈ (comparisonCentralSphere cB)ᶜ :=
      E.map_image.subset (Set.mem_image_of_mem _ hx)
    rw [twoChartComparisonMap_complement cA cB E hx,
      twoChartComparisonMap_complement cB cA (reverseRegions E) hy]
    exact E.left_inverse hx

include ha hcA hcB hmatch in

theorem twoChartComparisonMap_smooth :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (twoChartComparisonMap cA cB E) := by
  have hlocal : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (fun x => cB (cA.symm x)) cA.target := by
    apply cB.contMDiffOn_toFun.comp cA.contMDiffOn_invFun
    intro x hx
    rw [hcB, ← hcA]
    exact cA.map_target hx
  intro x
  by_cases hx : x ∈ comparisonCentralSphere cA
  · have htarget : x ∈ cA.target := comparisonCentral_subset_target cA ha hcA hx
    apply (hlocal.contMDiffAt (cA.open_target.mem_nhds htarget)).congr_of_eventuallyEq
    filter_upwards [cA.open_target.mem_nhds htarget] with y hy
    exact twoChartComparisonMap_target cA cB E ha hcA hmatch hy
  · have hopen : IsOpen ((comparisonCentralSphere cA)ᶜ : Set A.carrier) :=
      (comparisonCentral_isClosed cA ha hcA).isOpen_compl
    apply (E.map_smooth.contMDiffAt (hopen.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact twoChartComparisonMap_complement cA cB E hy

noncomputable def twoChartComparisonDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞ where
  toFun := twoChartComparisonMap cA cB E
  invFun := twoChartComparisonMap cB cA (reverseRegions E)
  left_inv := twoChartComparisonMap_left_inverse cA cB E ha hcA hcB hmatch
  right_inv := twoChartComparisonMap_left_inverse cB cA (reverseRegions E)
    ha hcB hcA (twoChartComparison_inverse_matching cA cB E ha hcA hmatch)
  contMDiff_toFun := twoChartComparisonMap_smooth cA cB E ha hcA hcB hmatch
  contMDiff_invFun := twoChartComparisonMap_smooth cB cA (reverseRegions E)
    ha hcB hcA (twoChartComparison_inverse_matching cA cB E ha hcA hmatch)

theorem twoChartComparisonDiffeomorph_complement {x : A.carrier}
    (hx : x ∉ comparisonCentralSphere cA) :
    twoChartComparisonDiffeomorph cA cB E ha hcA hcB hmatch x = E.map x :=
  twoChartComparisonMap_complement cA cB E hx

theorem twoChartComparisonDiffeomorph_collar {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-a) a) :
    twoChartComparisonDiffeomorph cA cB E ha hcA hcB hmatch (cA z) = cB z :=
  twoChartComparisonMap_collar cA cB E ha hcA hmatch hz

end PoincareConjecture.M38
