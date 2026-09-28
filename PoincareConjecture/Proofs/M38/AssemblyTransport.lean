import PoincareConjecture.Proofs.M38.RegionEquivalences

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

noncomputable def transportConnectedSum {A B C D : GeneralizedSliceCarrier.{u}}
    (S : SmoothConnectedSumData A B C)
    (e : Diffeomorph (𝓡 3) (𝓡 3) C.carrier D.carrier ∞) :
    SmoothConnectedSumData A B D where
  first_ball := S.first_ball
  second_ball := S.second_ball
  first_region := e '' S.first_region
  second_region := e '' S.second_region
  first_open := e.toHomeomorph.isOpenMap _ S.first_open
  second_open := e.toHomeomorph.isOpenMap _ S.second_open
  first_identify := composeRegions S.first_identify (diffeomorphRegions e S.first_region)
  second_identify := composeRegions S.second_identify (diffeomorphRegions e S.second_region)
  regions_disjoint := (Set.disjoint_image_iff e.injective).mpr S.regions_disjoint
  sphere_gluing := S.sphere_gluing
  collar := e ∘ S.collar
  collar_inverse := S.collar_inverse ∘ e.symm
  collar_smooth := e.contMDiff.comp_contMDiffOn S.collar_smooth
  collar_inverse_smooth := S.collar_inverse_smooth.comp e.symm.contMDiff.contMDiffOn (by
    rintro q ⟨z, hz, rfl⟩
    change e.symm (e (S.collar z)) ∈ S.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
    rw [e.symm_apply_apply]
    exact Set.mem_image_of_mem S.collar hz)
  collar_left_inverse := by
    intro z hz
    change S.collar_inverse (e.symm (e (S.collar z))) = z
    rw [e.symm_apply_apply]
    exact S.collar_left_inverse hz
  collar_right_inverse := by
    rintro q ⟨z, hz, rfl⟩
    change e (S.collar (S.collar_inverse (e.symm (e (S.collar z))))) = e (S.collar z)
    rw [e.symm_apply_apply, S.collar_right_inverse (Set.mem_image_of_mem _ hz)]
  collar_open := by
    rw [Set.image_comp]
    exact e.toHomeomorph.isOpenMap _ S.collar_open
  negative_gluing := fun z s hs => congrArg e (S.negative_gluing z s hs)
  positive_gluing := fun z s hs => congrArg e (S.positive_gluing z s hs)
  central_disjoint := by
    rw [Set.image_comp, ← Set.image_union]
    exact (Set.disjoint_image_iff e.injective).mpr S.central_disjoint
  cover := by
    rw [Set.image_comp, ← Set.image_union, ← Set.image_union, S.cover]
    exact Set.image_univ_of_surjective e.surjective

theorem transportConnectedSumStep {A B C : GeneralizedSliceCarrier.{u}}
    (h : SmoothConnectedSumStep A B)
    (e : Diffeomorph (𝓡 3) (𝓡 3) B.carrier C.carrier ∞) :
    SmoothConnectedSumStep A C := by
  obtain ⟨D, E, hU, ⟨S⟩⟩ := h
  exact ⟨D, E, hU, ⟨transportConnectedSum S e⟩⟩

theorem exists_transportAssembly {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {A B : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces A)
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞) :
    Nonempty (SmoothFiniteConnectedSumAssembly pieces B) := by
  obtain ⟨I, U, h⟩ := S
  rcases h.cases_tail with he | ⟨C, hprefix, hlast⟩
  · subst A
    exact ⟨⟨B, transportUnion U e, Relation.ReflTransGen.refl⟩⟩
  · exact ⟨⟨I, U, hprefix.tail (transportConnectedSumStep hlast e)⟩⟩

noncomputable def transportConclusion {A A' B : GeneralizedSliceCarrier.{u}}
    (C : SurgeryTopologyConclusion A B)
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A'.carrier ∞) :
    SurgeryTopologyConclusion A' B where
  piece_count := C.piece_count
  piece := C.piece
  piece_compact := C.piece_compact
  piece_connected := C.piece_connected
  kind := C.kind
  survivor_region := C.survivor_region
  survivor := C.survivor
  survivor_component := C.survivor_component
  survivor_cover := C.survivor_cover
  survivor_disjoint := C.survivor_disjoint
  bundles := C.bundles
  spaceforms := C.spaceforms
  reconstruction := Classical.choice (exists_transportAssembly C.reconstruction e)

end PoincareConjecture.M38
