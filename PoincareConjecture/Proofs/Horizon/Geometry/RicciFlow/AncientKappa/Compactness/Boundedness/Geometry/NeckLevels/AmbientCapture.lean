import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.Capture










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace

namespace Poincare.Geometry.Manifold.RegularLevel

variable {M : Type*} [TopologicalSpace M]



theorem image_connectedComponent_openLevelIncl
    (f : M → ℝ) (U : Opens M) (c : ℝ) (z : openLevelSet f U c) :
    openLevelIncl f U c '' connectedComponent z =
      connectedComponentIn {x | x ∈ U ∧ f x = c} (openLevelIncl f U c z) := by
  let i := openLevelIncl f U c
  let A : Set M := {x | x ∈ U ∧ f x = c}
  have hi := isEmbedding_openLevelIncl f U c
  have hrange : range i = A := by
    exact range_openLevelIncl f U c
  have hz : i z ∈ A := hrange ▸ mem_range_self z
  apply Subset.antisymm
  · have hp : IsPreconnected (i '' connectedComponent z) :=
      isPreconnected_connectedComponent.image i hi.continuous.continuousOn
    exact hp.subset_connectedComponentIn (mem_image_of_mem i mem_connectedComponent)
        (by rintro _ ⟨x, _, rfl⟩; exact ⟨x.1.2, x.2⟩)
  · have hccrange : connectedComponentIn A (i z) ⊆ range i := by
      rw [hrange]
      exact connectedComponentIn_subset A (i z)
    have himage : i '' (i ⁻¹' connectedComponentIn A (i z)) =
        connectedComponentIn A (i z) := image_preimage_eq_of_subset hccrange
    have hpre : IsPreconnected (i ⁻¹' connectedComponentIn A (i z)) := by
      apply hi.isInducing.isPreconnected_image.mp
      rw [himage]
      exact isPreconnected_connectedComponentIn
    have hsubset := hpre.subset_connectedComponent (mem_connectedComponentIn hz)
    rw [← himage]
    exact image_mono hsubset



theorem range_comp_openLevelIncl_eq_connectedComponentIn
    {Y : Type*} (f : M → ℝ) (U : Opens M) (c : ℝ)
    (F : Y → openLevelSet f U c) (q : Y)
    (hcomponent : range F = connectedComponent (F q)) :
    range (openLevelIncl f U c ∘ F) =
      connectedComponentIn {x | x ∈ U ∧ f x = c} (openLevelIncl f U c (F q)) := by
  rw [range_comp, hcomponent, image_connectedComponent_openLevelIncl]

end Poincare.Geometry.Manifold.RegularLevel
