import PoincareConjecture.Definitions.Ch15.SurgeryTopology

















set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

private theorem m72TransportImage {X : Type*}
    {A B : GeneralizedSliceCarrier.{u}}
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    (f : X → A.carrier) (U : Set X) :
    (d ∘ f) '' U = d.symm ⁻¹' (f '' U) := by
  rw [Set.image_comp, d.image_eq_preimage_symm]


noncomputable def SurgeryRegionEquivalence.transportTarget
    {A B C : GeneralizedSliceCarrier.{u}}
    {U : Set A.carrier} {V : Set B.carrier}
    (E : SurgeryRegionEquivalence A B U V)
    (d : Diffeomorph (𝓡 3) (𝓡 3) B.carrier C.carrier ∞) :
    SurgeryRegionEquivalence A C U (d.symm ⁻¹' V) where
  map := d ∘ E.map
  inverse := E.inverse ∘ d.symm
  map_image := by
    rw [Set.image_comp, E.map_image, d.image_eq_preimage_symm]
  inverse_image := by
    rw [Set.image_comp, ← d.image_eq_preimage_symm,
      d.symm_image_image, E.inverse_image]
  left_inverse := by
    intro x hx
    simpa only [Function.comp_apply, Diffeomorph.symm_apply_apply] using
      E.left_inverse hx
  right_inverse := by
    intro x hx
    change d (E.map (E.inverse (d.symm x))) = x
    rw [E.right_inverse hx, d.apply_symm_apply]
  map_smooth := d.contMDiff.comp_contMDiffOn E.map_smooth
  inverse_smooth := E.inverse_smooth.comp d.symm.contMDiff.contMDiffOn
    (fun _ hx => hx)


noncomputable def SmoothDisjointUnionData.transportTarget
    {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {A B : GeneralizedSliceCarrier.{u}}
    (S : SmoothDisjointUnionData pieces A)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞) :
    SmoothDisjointUnionData pieces B where
  region := fun i => d.symm ⁻¹' S.region i
  region_open := fun i => (S.region_open i).preimage d.symm.continuous
  region_closed := fun i => (S.region_closed i).preimage d.symm.continuous
  identify := fun i => (S.identify i).transportTarget d
  pairwise_disjoint := fun i j hij => (S.pairwise_disjoint i j hij).preimage d.symm
  cover := by
    rw [← Set.preimage_iUnion, S.cover, Set.preimage_univ]


noncomputable def SmoothConnectedSumData.transportTarget
    {A B C D : GeneralizedSliceCarrier.{u}}
    (S : SmoothConnectedSumData A B C)
    (d : Diffeomorph (𝓡 3) (𝓡 3) C.carrier D.carrier ∞) :
    SmoothConnectedSumData A B D where
  first_ball := S.first_ball
  second_ball := S.second_ball
  first_region := d.symm ⁻¹' S.first_region
  second_region := d.symm ⁻¹' S.second_region
  first_open := S.first_open.preimage d.symm.continuous
  second_open := S.second_open.preimage d.symm.continuous
  first_identify := S.first_identify.transportTarget d
  second_identify := S.second_identify.transportTarget d
  regions_disjoint := S.regions_disjoint.preimage d.symm
  sphere_gluing := S.sphere_gluing
  collar := d ∘ S.collar
  collar_inverse := S.collar_inverse ∘ d.symm
  collar_smooth := d.contMDiff.comp_contMDiffOn S.collar_smooth
  collar_inverse_smooth := by
    rw [m72TransportImage]
    exact S.collar_inverse_smooth.comp d.symm.contMDiff.contMDiffOn
      (fun _ hx => hx)
  collar_left_inverse := by
    intro x hx
    simpa only [Function.comp_apply, Diffeomorph.symm_apply_apply] using
      S.collar_left_inverse hx
  collar_right_inverse := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, Diffeomorph.symm_apply_apply]
    rw [S.collar_right_inverse (Set.mem_image_of_mem S.collar hx)]
  collar_open := by
    rw [m72TransportImage]
    exact S.collar_open.preimage d.symm.continuous
  negative_gluing := by
    intro z s hs
    exact congrArg d (S.negative_gluing z s hs)
  positive_gluing := by
    intro z s hs
    exact congrArg d (S.positive_gluing z s hs)
  central_disjoint := by
    rw [m72TransportImage, ← Set.preimage_union]
    exact S.central_disjoint.preimage d.symm
  cover := by
    rw [m72TransportImage, ← Set.preimage_union, ← Set.preimage_union,
      S.cover, Set.preimage_univ]


theorem SmoothConnectedSumStep.transportTarget
    {A B C : GeneralizedSliceCarrier.{u}}
    (h : SmoothConnectedSumStep A B)
    (d : Diffeomorph (𝓡 3) (𝓡 3) B.carrier C.carrier ∞) :
    SmoothConnectedSumStep A C := by
  rcases h with ⟨P, Q, hUnion, ⟨S⟩⟩
  exact ⟨P, Q, hUnion, ⟨S.transportTarget d⟩⟩



theorem SmoothFiniteConnectedSumAssembly.nonempty_transportTarget
    {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {A B : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces A)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞) :
    Nonempty (SmoothFiniteConnectedSumAssembly pieces B) := by
  rcases S with ⟨initial, disjointUnion, operations⟩
  rcases operations.cases_tail with h | ⟨C, hPrefix, hLast⟩
  · subst A
    exact ⟨{
      initial := B
      disjoint_union := disjointUnion.transportTarget d
      operations := Relation.ReflTransGen.refl }⟩
  · exact ⟨{
      initial := initial
      disjoint_union := disjointUnion
      operations := hPrefix.tail (hLast.transportTarget d) }⟩


noncomputable def SmoothFiniteConnectedSumAssembly.transportTarget
    {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {A B : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces A)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞) :
    SmoothFiniteConnectedSumAssembly pieces B :=
  Classical.choice (S.nonempty_transportTarget d)



noncomputable def SurgeryTopologyConclusion.transportPre
    {A A' B : GeneralizedSliceCarrier.{u}}
    (S : SurgeryTopologyConclusion A B)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A'.carrier ∞) :
    SurgeryTopologyConclusion A' B where
  piece_count := S.piece_count
  piece := S.piece
  piece_compact := S.piece_compact
  piece_connected := S.piece_connected
  kind := S.kind
  survivor_region := S.survivor_region
  survivor := S.survivor
  survivor_component := S.survivor_component
  survivor_cover := S.survivor_cover
  survivor_disjoint := S.survivor_disjoint
  bundles := S.bundles
  spaceforms := S.spaceforms
  reconstruction := S.reconstruction.transportTarget d

@[simp] theorem SurgeryTopologyConclusion.transportPre_piece_count
    {A A' B : GeneralizedSliceCarrier.{u}}
    (S : SurgeryTopologyConclusion A B)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A'.carrier ∞) :
    (S.transportPre d).piece_count = S.piece_count := rfl

@[simp] theorem SurgeryTopologyConclusion.transportPre_piece
    {A A' B : GeneralizedSliceCarrier.{u}}
    (S : SurgeryTopologyConclusion A B)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A'.carrier ∞) :
    (S.transportPre d).piece = S.piece := rfl

@[simp] theorem SurgeryTopologyConclusion.transportPre_kind
    {A A' B : GeneralizedSliceCarrier.{u}}
    (S : SurgeryTopologyConclusion A B)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A'.carrier ∞) :
    (S.transportPre d).kind = S.kind := rfl

@[simp] theorem SurgeryTopologyConclusion.transportPre_survivor_region
    {A A' B : GeneralizedSliceCarrier.{u}}
    (S : SurgeryTopologyConclusion A B)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A'.carrier ∞) :
    (S.transportPre d).survivor_region = S.survivor_region := rfl

@[simp] theorem SurgeryTopologyConclusion.transportPre_survivor
    {A A' B : GeneralizedSliceCarrier.{u}}
    (S : SurgeryTopologyConclusion A B)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A'.carrier ∞) :
    (S.transportPre d).survivor = S.survivor := rfl

end PoincareConjecture
