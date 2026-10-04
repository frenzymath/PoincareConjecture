import PoincareLib.Topology.Manifold.ConnectedSum.Surgery.Topology

/-!
# Exact smooth region identifications

These constructions compose the actual region maps and transport a finite
disjoint union to a diffeomorphic target. They contain no cutting or
classification theorem.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M38

/-- Composition retains the exact intermediate region for both smooth maps. -/
def composeRegions {A B C : GeneralizedSliceCarrier.{u}}
    {U : Set A.carrier} {V : Set B.carrier} {W : Set C.carrier}
    (e : SurgeryRegionEquivalence A B U V)
    (f : SurgeryRegionEquivalence B C V W) : SurgeryRegionEquivalence A C U W where
  map := f.map ∘ e.map
  inverse := e.inverse ∘ f.inverse
  map_image := by rw [Set.image_comp, e.map_image, f.map_image]
  inverse_image := by rw [Set.image_comp, f.inverse_image, e.inverse_image]
  left_inverse := by
    intro x hx
    have he : e.map x ∈ V := e.map_image.subset (Set.mem_image_of_mem _ hx)
    change e.inverse (f.inverse (f.map (e.map x))) = x
    rw [f.left_inverse he, e.left_inverse hx]
  right_inverse := by
    intro x hx
    have hf : f.inverse x ∈ V := f.inverse_image.subset (Set.mem_image_of_mem _ hx)
    change f.map (e.map (e.inverse (f.inverse x))) = x
    rw [e.right_inverse hf, f.right_inverse hx]
  map_smooth := f.map_smooth.comp e.map_smooth (by
    intro x hx
    exact e.map_image.subset (Set.mem_image_of_mem _ hx))
  inverse_smooth := e.inverse_smooth.comp f.inverse_smooth (by
    intro x hx
    exact f.inverse_image.subset (Set.mem_image_of_mem _ hx))

/-- A global diffeomorphism identifies any region with its exact image. -/
noncomputable def diffeomorphRegions {A B : GeneralizedSliceCarrier.{u}}
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    (U : Set A.carrier) : SurgeryRegionEquivalence A B U (e '' U) where
  map := e
  inverse := e.symm
  map_image := rfl
  inverse_image := e.symm_image_image U
  left_inverse := fun _ _ => e.symm_apply_apply _
  right_inverse := fun _ _ => e.apply_symm_apply _
  map_smooth := e.contMDiff.contMDiffOn
  inverse_smooth := e.symm.contMDiff.contMDiffOn

/-- Transport a smooth disjoint union by images under the supplied actual
diffeomorphism, preserving every piece and its identification. -/
noncomputable def transportUnion {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {A B : GeneralizedSliceCarrier.{u}}
    (D : SmoothDisjointUnionData pieces A)
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞) :
    SmoothDisjointUnionData pieces B where
  region := fun i => e '' D.region i
  region_open := fun i => e.toHomeomorph.isOpenMap _ (D.region_open i)
  region_closed := fun i => e.toHomeomorph.isClosedMap _ (D.region_closed i)
  identify := fun i => composeRegions (D.identify i) (diffeomorphRegions e (D.region i))
  pairwise_disjoint := fun i j hij =>
    (Set.disjoint_image_iff e.injective).mpr (D.pairwise_disjoint i j hij)
  cover := by
    rw [← Set.image_iUnion, D.cover]
    exact Set.image_univ_of_surjective e.surjective

end PoincareMT.M38
