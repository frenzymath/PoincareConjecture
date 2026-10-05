import PoincareLib.Topology.Manifold.Surgery.Event.Open.OpenRegionEquivalences

/-!
# Extending an exact complement comparison through its actual collars

Two actual collars have the same positive-width source. A smooth region
equivalence of their central-sphere complements agrees with the collar
coordinates away from parameter zero. The literal collar comparison then
extends that equivalence, with its actual inverse, to a global diffeomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable {A B : GeneralizedSliceCarrier.{u}}

/-- The central set is exactly the image of the actual collar's zero section. -/
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

/-- Positive width puts the whole zero section in the supplied source. -/
theorem comparisonCentral_source :
    Set.univ ×ˢ ({0} : Set ℝ) ⊆ c.source := by
  rintro z ⟨hz, hs⟩
  have hs0 : z.2 = 0 := hs
  rw [hc]
  exact ⟨hz, by simpa only [hs0] using neg_neg_of_pos ha,
    by simpa only [hs0] using ha⟩

/-- The actual central sphere lies in the original open collar target. -/
theorem comparisonCentral_subset_target : comparisonCentralSphere c ⊆ c.target := by
  rintro _ ⟨z, hz, rfl⟩
  exact c.map_source (comparisonCentral_source c ha hc hz)

/-- Compactness of the zero section makes its actual image closed in the carrier. -/
theorem comparisonCentral_isClosed : IsClosed (comparisonCentralSphere c) := by
  apply IsCompact.isClosed
  exact (isCompact_univ.prod isCompact_singleton).image_of_continuousOn
    (c.contMDiffOn_toFun.continuousOn.mono (comparisonCentral_source c ha hc))

/-- Within the true collar source, central membership is exactly zero signed parameter. -/
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

/-- The exact complement map is extended only at the central image, using the actual collars. -/
noncomputable def twoChartComparisonMap (x : A.carrier) : B.carrier := by
  classical
  exact if x ∈ comparisonCentralSphere cA then cB (cA.symm x) else E.map x

/-- Every point off the central sphere keeps the originally supplied complement map. -/
theorem twoChartComparisonMap_complement {x : A.carrier}
    (hx : x ∉ comparisonCentralSphere cA) :
    twoChartComparisonMap cA cB E x = E.map x := by
  classical
  simp only [twoChartComparisonMap, if_neg hx]

/-- Every central point uses the actual inverse collar coordinate and the other original collar. -/
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
/-- Punctured matching and the actual inverse law give the full collar equation, including zero. -/
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
/-- The extended map equals the literal collar composition throughout the original open target. -/
theorem twoChartComparisonMap_target {x : A.carrier} (hx : x ∈ cA.target) :
    twoChartComparisonMap cA cB E x = cB (cA.symm x) := by
  have hz : cA.symm x ∈ Set.univ ×ˢ Set.Ioo (-a) a :=
    hcA ▸ cA.map_target hx
  have hright : cA (cA.symm x) = x := cA.toPartialEquiv.right_inv hx
  have h := twoChartComparisonMap_collar cA cB E ha hcA hmatch hz
  rwa [hright] at h

include ha hcA hmatch in
/-- The inverse complement map has the forced matching equation on the same punctured collar. -/
theorem twoChartComparison_inverse_matching
    (z : RoundCylinderSpace) (hz : z ∈ Set.univ ×ˢ Set.Ioo (-a) a)
    (hz0 : z.2 ≠ 0) : (reverseRegions E).map (cB z) = cA z := by
  have hsource : cA z ∈ (comparisonCentralSphere cA)ᶜ :=
    fun h => hz0 ((comparisonCentral_mem_iff cA ha hcA (hcA.symm ▸ hz)).mp h)
  change E.inverse (cB z) = cA z
  rw [← hmatch z hz hz0]
  exact E.left_inverse hsource

include ha hcA hcB hmatch in
/-- The two extended maps are literal mutual inverses on the whole carrier. -/
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
/-- Smoothness uses the original complement map off the sphere and the actual collar composition near it. -/
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

/-- Matching the actual punctured collars extends their exact complement equivalence
to a global smooth diffeomorphism. This is the central-fiber comparison needed by
the nonseparating reconstruction of Morgan--Tian Proposition 15.3, pp. 357-358. -/
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

/-- The global diffeomorphism retains the literal complement map on its exact original domain. -/
theorem twoChartComparisonDiffeomorph_complement {x : A.carrier}
    (hx : x ∉ comparisonCentralSphere cA) :
    twoChartComparisonDiffeomorph cA cB E ha hcA hcB hmatch x = E.map x :=
  twoChartComparisonMap_complement cA cB E hx

/-- The global diffeomorphism sends every supplied collar coordinate to that same coordinate. -/
theorem twoChartComparisonDiffeomorph_collar {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-a) a) :
    twoChartComparisonDiffeomorph cA cB E ha hcA hcB hmatch (cA z) = cB z :=
  twoChartComparisonMap_collar cA cB E ha hcA hmatch hz

end PoincareMT.M38
