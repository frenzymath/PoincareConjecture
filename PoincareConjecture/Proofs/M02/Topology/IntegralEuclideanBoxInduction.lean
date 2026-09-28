import PoincareConjecture.Proofs.M02.Topology.IntegralEuclideanBoxCap
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportCapCanonicalUnion
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportCapTwoCanonicalUnion
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportCapThreeCanonicalUnion
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportEmpty
import PoincareConjecture.Proofs.M02.IntegralOpenCapData



set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

namespace PoincareConjecture.Proofs.M02.Topology

open PoincareConjecture.Proofs.M02

private theorem support_homology_restriction_isIso_of_eq
    {X : Type} [TopologicalSpace X] {K L : Set X} {n : Nat}
    (hKL : K ⊆ L) (hEq : K = L) :
    IsIso (integralSupportHomologyRestriction hKL n) := by
  subst L
  have hh : hKL = (Set.Subset.refl K) := Subsingleton.elim _ _
  rw [hh]
  change IsIso (homologyMap (integralSupportRestriction (Set.Subset.refl K)) n)
  have hrest : integralSupportRestriction (Set.Subset.refl K) = 𝟙 _ := by
    apply (cancel_epi (integralRelativeProjection Kᶜ)).mp
    rw [integralSupportRestriction_projection]
    rfl
  rw [hrest, homologyMap_id]
  infer_instance

private theorem openOrientation_id
    {X : Type} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    [LocallyCompactSpace X]
    (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3) (x : X) :
    integralOpenOrientation (ContinuousMap.id X)
      _root_.Topology.IsOpenEmbedding.id omegaX x = omegaX x := by
  have hf : Function.Injective (ContinuousMap.id X) := by
    intro a b h
    exact h
  have hIK : (ContinuousMap.id X) '' ({x} : Set X) ⊆ ({x} : Set X) := by
    rintro y ⟨z, hz, rfl⟩
    exact hz
  have hchain : integralSupportEmbeddingChains (ContinuousMap.id X) hf
      ({x} : Set X) = integralSupportRestriction hIK := by
    apply (cancel_epi (integralRelativeProjection ({x} : Set X)ᶜ)).mp
    rw [integralSupportEmbeddingChains_projection,
      integralSupportRestriction_projection]
    change integralChainsFunctor.map (𝟙 (TopCat.of X)) ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  let : IsIso (homologyMap (integralSupportEmbeddingChains
      (ContinuousMap.id X) hf ({x} : Set X)) 3) :=
    integralSupportEmbeddingChains_homology_isIso (ContinuousMap.id X)
      _root_.Topology.IsOpenEmbedding.id ⟨{x}, isCompact_singleton⟩ 3
  change inv (homologyMap (integralSupportEmbeddingChains
    (ContinuousMap.id X) hf ({x} : Set X)) 3)
    (integralSupportHomologyRestriction hIK 3 (omegaX x)) = omegaX x
  have hm := congrArg (fun m => homologyMap m 3) hchain
  change inv (homologyMap (integralSupportEmbeddingChains
    (ContinuousMap.id X) hf ({x} : Set X)) 3)
    (homologyMap (integralSupportRestriction hIK) 3 (omegaX x)) = omegaX x
  rw [← hm]
  exact IsIso.hom_inv_id_apply
    (homologyMap (integralSupportEmbeddingChains
      (ContinuousMap.id X) hf ({x} : Set X)) 3) (omegaX x)

private theorem openOrientation_homeomorph_inverse
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [RegularSpace X] [RegularSpace Y]
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (e : X ≃ₜ Y)
    (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3) (x : X) :
    integralOpenOrientation e e.isOpenEmbedding
      (integralOpenOrientation (e.symm : C(Y, X)) e.symm.isOpenEmbedding omegaX)
      x = omegaX x := by
  have hc := integralOpenOrientation_comp
    (e : C(X, Y)) (e.symm : C(Y, X)) e.isOpenEmbedding e.symm.isOpenEmbedding
    omegaX x
  have hcomp : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
    ext y
    simp
  have hc' : integralOpenOrientation (ContinuousMap.id X)
      _root_.Topology.IsOpenEmbedding.id omegaX x =
      integralOpenOrientation e e.isOpenEmbedding
        (integralOpenOrientation (e.symm : C(Y, X)) e.symm.isOpenEmbedding omegaX) x := by
    simpa only [hcomp] using hc
  rw [openOrientation_id] at hc'
  exact hc'.symm

private theorem openOrientation_generator_of_generator
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [RegularSpace X] [RegularSpace Y]
    [LocallyCompactSpace X]
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hgenY : ∀ y : Y, ∃ g : Int ≃ₗ[Int]
      integralSupportHomology ({y} : Set Y) 3, g 1 = omegaY y)
    (x : X) :
    ∃ g : Int ≃ₗ[Int] integralSupportHomology ({x} : Set X) 3,
      g 1 = integralOpenOrientation f hf omegaY x := by
  let hval : f '' ({x} : Set X) ⊆ ({f x} : Set Y) := by
    rintro y ⟨z, hz, rfl⟩
    rw [mem_singleton_iff] at hz ⊢
    subst z
    rfl
  let himage : f '' ({x} : Set X) = ({f x} : Set Y) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_singleton_iff] at hz ⊢
      subst z
      rfl
    · intro hy
      rw [mem_singleton_iff] at hy
      subst y
      exact ⟨x, mem_singleton _, rfl⟩
  let r := integralSupportHomologyRestriction hval 3
  let : IsIso r := support_homology_restriction_isIso_of_eq hval himage
  let m := homologyMap (integralSupportEmbeddingChains f hf.injective
    ({x} : Set X)) 3
  let : IsIso m := integralSupportEmbeddingChains_homology_isIso f hf
    ⟨{x}, isCompact_singleton⟩ 3
  obtain ⟨g, hg⟩ := hgenY (f x)
  refine ⟨g.trans (asIso r).toLinearEquiv |>.trans (asIso m).symm.toLinearEquiv, ?_⟩
  apply (ModuleCat.mono_iff_injective m).mp inferInstance
  dsimp
  rw [IsIso.inv_hom_id_apply]
  rw [integralOpenOrientation_point, hg]

private abbrev E := EuclideanSpace Real (Fin 3)

def integralEuclideanOpenCapProperty (U : Set E) (hU : IsOpen U) : Prop :=
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  Epi (integralCompactSupportCapOne
    (integralOpenSupportDetectedData U integralEuclideanSupportDetected hU)
    (integralOpenOmegaData hU
      (Classical.choose exists_integralEuclideanOrientationData))
    (integralOpenLocalOrientationData hU
      (Classical.choose exists_integralEuclideanOrientationData)
      (Classical.choose_spec exists_integralEuclideanOrientationData).2)) ∧
  IsIso (integralCompactSupportCapTwo
    (integralOpenSupportDetectedData U integralEuclideanSupportDetected hU)
    (integralOpenOmegaData hU
      (Classical.choose exists_integralEuclideanOrientationData))
    (integralOpenLocalOrientationData hU
      (Classical.choose exists_integralEuclideanOrientationData)
      (Classical.choose_spec exists_integralEuclideanOrientationData).2)) ∧
  IsIso (integralCompactSupportCapThree
    (integralOpenSupportDetectedData U integralEuclideanSupportDetected hU)
    (integralOpenOmegaData hU
      (Classical.choose exists_integralEuclideanOrientationData))
    (integralOpenLocalOrientationData hU
      (Classical.choose exists_integralEuclideanOrientationData)
      (Classical.choose_spec exists_integralEuclideanOrientationData).2))
  ∧ ∀ q : Nat, 4 ≤ q →
      IsZero (integralCompactSupportCohomology U q)

theorem integralEuclideanOpenCapProperty_empty :
    integralEuclideanOpenCapProperty (∅ : Set E) isOpen_empty := by
  let : LocallyCompactSpace (∅ : Set E) := isOpen_empty.locallyCompactSpace
  dsimp [integralEuclideanOpenCapProperty]
  have hcoh1 := integralCompactSupportCohomology_empty_isZero 1
  have hcoh2 := integralCompactSupportCohomology_empty_isZero 2
  have hcoh3 := integralCompactSupportCohomology_empty_isZero 3
  have hhom0 := integralHomology_empty_isZero (X := E) 0
  have hhom1 := integralHomology_empty_isZero (X := E) 1
  have hhom2 := integralHomology_empty_isZero (X := E) 2
  constructor
  · exact hhom2.epi (integralCompactSupportCapOne _ _ _)
  constructor
  · exact hcoh2.isIso hhom1 (integralCompactSupportCapTwo _ _ _)
  · constructor
    · exact hcoh3.isIso hhom0 (integralCompactSupportCapThree _ _ _)
    · intro q hq
      exact integralCompactSupportCohomology_empty_isZero q

theorem integralEuclideanOpenCapProperty_union
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
    (hUprop : integralEuclideanOpenCapProperty U hU)
    (hVprop : integralEuclideanOpenCapProperty V hV)
    (hIprop : integralEuclideanOpenCapProperty (U ∩ V) (hU.inter hV)) :
    integralEuclideanOpenCapProperty (U ∪ V) (hU.union hV) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : LocallyCompactSpace V := hV.locallyCompactSpace
  let : LocallyCompactSpace (↥(U ∩ V)) := (hU.inter hV).locallyCompactSpace
  let : LocallyCompactSpace (↥(U ∪ V)) := (hU.union hV).locallyCompactSpace
  dsimp [integralEuclideanOpenCapProperty] at hUprop hVprop hIprop
  have hU' : Epi (integralCompactSupportCapOne
      (integralOpenSupportDetectedData U integralEuclideanSupportDetected hU)
      (integralOpenOmegaData hU
        (Classical.choose exists_integralEuclideanOrientationData))
      (integralOpenLocalOrientationData hU
        (Classical.choose exists_integralEuclideanOrientationData)
        (Classical.choose_spec exists_integralEuclideanOrientationData).2)) := by
    exact hUprop.1
  have hU2 : IsIso (integralCompactSupportCapTwo
      (integralOpenSupportDetectedData U integralEuclideanSupportDetected hU)
      (integralOpenOmegaData hU
        (Classical.choose exists_integralEuclideanOrientationData))
      (integralOpenLocalOrientationData hU
        (Classical.choose exists_integralEuclideanOrientationData)
        (Classical.choose_spec exists_integralEuclideanOrientationData).2)) := by
    exact hUprop.2.1
  have hU3 : IsIso (integralCompactSupportCapThree
      (integralOpenSupportDetectedData U integralEuclideanSupportDetected hU)
      (integralOpenOmegaData hU
        (Classical.choose exists_integralEuclideanOrientationData))
      (integralOpenLocalOrientationData hU
        (Classical.choose exists_integralEuclideanOrientationData)
        (Classical.choose_spec exists_integralEuclideanOrientationData).2)) := by
    exact hUprop.2.2.1
  have hV' : Epi (integralCompactSupportCapOne
      (integralOpenSupportDetectedData V integralEuclideanSupportDetected hV)
      (integralOpenOmegaData hV
        (Classical.choose exists_integralEuclideanOrientationData))
      (integralOpenLocalOrientationData hV
        (Classical.choose exists_integralEuclideanOrientationData)
        (Classical.choose_spec exists_integralEuclideanOrientationData).2)) := by
    exact hVprop.1
  have hV2 : IsIso (integralCompactSupportCapTwo
      (integralOpenSupportDetectedData V integralEuclideanSupportDetected hV)
      (integralOpenOmegaData hV
        (Classical.choose exists_integralEuclideanOrientationData))
      (integralOpenLocalOrientationData hV
        (Classical.choose exists_integralEuclideanOrientationData)
        (Classical.choose_spec exists_integralEuclideanOrientationData).2)) := by
    exact hVprop.2.1
  have hV3 : IsIso (integralCompactSupportCapThree
      (integralOpenSupportDetectedData V integralEuclideanSupportDetected hV)
      (integralOpenOmegaData hV
        (Classical.choose exists_integralEuclideanOrientationData))
      (integralOpenLocalOrientationData hV
        (Classical.choose exists_integralEuclideanOrientationData)
        (Classical.choose_spec exists_integralEuclideanOrientationData).2)) := by
    exact hVprop.2.2.1
  have hI2 : IsIso (integralCompactSupportCapTwo
      (integralOpenSupportDetectedData (U ∩ V) integralEuclideanSupportDetected
        (hU.inter hV))
      (integralOpenOmegaData (hU.inter hV)
        (Classical.choose exists_integralEuclideanOrientationData))
      (integralOpenLocalOrientationData (hU.inter hV)
        (Classical.choose exists_integralEuclideanOrientationData)
        (Classical.choose_spec exists_integralEuclideanOrientationData).2)) := by
    exact hIprop.2.1
  have hI3 : IsIso (integralCompactSupportCapThree
      (integralOpenSupportDetectedData (U ∩ V) integralEuclideanSupportDetected
        (hU.inter hV))
      (integralOpenOmegaData (hU.inter hV)
        (Classical.choose exists_integralEuclideanOrientationData))
      (integralOpenLocalOrientationData (hU.inter hV)
        (Classical.choose exists_integralEuclideanOrientationData)
        (Classical.choose_spec exists_integralEuclideanOrientationData).2)) := by
    exact hIprop.2.2.1
  have hU4 : ∀ q : Nat, 4 ≤ q →
      IsZero (integralCompactSupportCohomology U q) := by
    exact hUprop.2.2.2
  have hV4 : ∀ q : Nat, 4 ≤ q →
      IsZero (integralCompactSupportCohomology V q) := by
    exact hVprop.2.2.2
  have hI4 : ∀ q : Nat, 4 ≤ q →
      IsZero (integralCompactSupportCohomology (↥(U ∩ V)) q) := by
    exact hIprop.2.2.2
  have h1 := integralCompactSupportCapOne_union_epi_canonical U V hU hV
    integralEuclideanSupportDetected
    (Classical.choose exists_integralEuclideanOrientationData)
    (Classical.choose_spec exists_integralEuclideanOrientationData).2
    hU' hV' hU2 hV2 hI2
  have h2 := integralCompactSupportCapTwo_union_isIso_canonical U V hU hV
    integralEuclideanSupportDetected
    (Classical.choose exists_integralEuclideanOrientationData)
    (Classical.choose_spec exists_integralEuclideanOrientationData).2
    hU2 hV2 hI2 hU3 hV3 hI3
  dsimp [integralEuclideanOpenCapProperty]
  refine ⟨h1, h2, ?_, ?_⟩
  · exact integralCompactSupportCapThree_union_isIso_canonical U V hU hV
      integralEuclideanSupportDetected
      (Classical.choose exists_integralEuclideanOrientationData)
      (Classical.choose_spec exists_integralEuclideanOrientationData).2
      hU3 hV3 hI3 (hI4 4 le_rfl)
  · intro q hq
    have hpair : IsZero
        (integralCompactSupportCohomology U q ⊞
          integralCompactSupportCohomology V q) :=
      (biprod_isZero_iff _ _).mpr ⟨hU4 q hq, hV4 q hq⟩
    have hnext : IsZero
        (integralCompactSupportCohomology (↥(U ∩ V)) (q + 1)) :=
      hI4 (q + 1) (by omega)
    exact (integralCompactSupportOpenMayerVietoris_exact_union U V hU hV q).isZero_of_both_isZero
      hpair hnext


set_option maxHeartbeats 800000 in

theorem integralEuclideanOpenCapProperty_box
    (a b : Fin 3 → ℝ) (hn : (euclideanThreeOpenBox a b).Nonempty) :
    integralEuclideanOpenCapProperty (euclideanThreeOpenBox a b)
      (euclideanThreeOpenBox_isOpen a b) := by
  let U := euclideanThreeOpenBox a b
  let hU := euclideanThreeOpenBox_isOpen a b
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let e : U ≃ₜ integralEuclideanSpace := euclideanThreeOpenBoxHomeomorph a b hn
  let ec : C(U, integralEuclideanSpace) := e
  let hDX := integralOpenSupportDetectedData U integralEuclideanSupportDetected hU
  let omegaX := integralOpenOmegaData hU
    (Classical.choose exists_integralEuclideanOrientationData)
  let hlocalX := integralOpenLocalOrientationData hU
    (Classical.choose exists_integralEuclideanOrientationData)
    (Classical.choose_spec exists_integralEuclideanOrientationData).2
  let omegaE := integralOpenOrientation (e.symm : C(integralEuclideanSpace, U))
    e.symm.isOpenEmbedding omegaX
  let hlocalE := integralOpenOrientation_locallyRepresented
    (e.symm : C(integralEuclideanSpace, U)) e.symm.isOpenEmbedding omegaX hlocalX
  have hgenX : ∀ x : U, ∃ g : Int ≃ₗ[Int]
      integralSupportHomology ({x} : Set U) 3, g 1 = omegaX x := by
    intro x
    simpa [omegaX, integralOpenOmegaData] using
      (openOrientation_generator_of_generator
        (integralOpenSubtypeVal U)
        (integralOpenSubtypeVal_isOpenEmbedding U hU)
        (Classical.choose exists_integralEuclideanOrientationData)
        (Classical.choose_spec exists_integralEuclideanOrientationData).1 x)
  have hgenE : ∃ g : Int ≃ₗ[Int]
      integralSupportHomology ({0} : Set integralEuclideanSpace) 3, g 1 = omegaE 0 := by
    obtain ⟨g, hg⟩ := openOrientation_generator_of_generator
      (e.symm : C(integralEuclideanSpace, U)) e.symm.isOpenEmbedding omegaX hgenX 0
    exact ⟨g, by simpa [omegaE] using hg⟩
  have hpoint : ∀ x : U,
      homologyMap (integralSupportEmbeddingChains ec e.injective ({x} : Set U)) 3
          (omegaX x) =
        integralSupportHomologyRestriction
          (show ec '' ({x} : Set U) ⊆ ({ec x} : Set integralEuclideanSpace) from by
            rintro y ⟨z, hz, rfl⟩
            rw [mem_singleton_iff] at hz ⊢
            subst z
            rfl) 3 (omegaE (ec x)) := by
    intro x
    have hp := integralOpenOrientation_point ec e.isOpenEmbedding omegaE x
    have hr := openOrientation_homeomorph_inverse e omegaX x
    change homologyMap (integralSupportEmbeddingChains ec e.injective
      ({x} : Set U)) 3
        (integralOpenOrientation ec e.isOpenEmbedding omegaE x) = _ at hp
    rw [hr] at hp
    exact hp
  have horient : ∀ K : Compacts U,
      homologyMap (integralSupportEmbeddingChains ec e.injective (K : Set U)) 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX) =
      integralCompactSupportOrientation integralEuclideanSupportDetected omegaE
        (K.map ec ec.continuous) hlocalE := by
    intro K
    exact integralCompactSupportOrientation_openEmbedding hDX
      integralEuclideanSupportDetected omegaX omegaE hlocalX hlocalE ec
      e.isOpenEmbedding hpoint K
  change Epi (integralCompactSupportCapOne hDX omegaX hlocalX) ∧
    IsIso (integralCompactSupportCapTwo hDX omegaX hlocalX) ∧
    IsIso (integralCompactSupportCapThree hDX omegaX hlocalX) ∧
    ∀ q : Nat, 4 ≤ q → IsZero (integralCompactSupportCohomology U q)
  constructor
  · exact box_cap_naturality_one_target e hDX omegaX hlocalX
      integralEuclideanSupportDetected omegaE hlocalE
      (integralEuclideanCompactSupportCapOne_epi integralEuclideanSupportDetected
        omegaE hlocalE) horient
  constructor
  · exact box_cap_naturality_two_target e hDX omegaX hlocalX
      integralEuclideanSupportDetected omegaE hlocalE
      (integralEuclideanCompactSupportCapTwo_isIso integralEuclideanSupportDetected
        omegaE hlocalE) horient
  · constructor
    · exact box_cap_naturality_three_target e hDX omegaX hlocalX
        integralEuclideanSupportDetected omegaE hlocalE
        (integralEuclideanCompactSupportCapThree_isIso
          integralEuclideanSupportDetected omegaE hlocalE hgenE) horient
    · intro q hq
      let : IsIso (integralCompactSupportCohomologyOpenMap ec
          e.isOpenEmbedding q) :=
        integralCompactSupportCohomologyOpenMap_homeomorph_isIso e q
      exact (integralEuclideanCompactSupportCohomology_ne_three_isZero q
        (by omega)).of_iso
        (asIso (integralCompactSupportCohomologyOpenMap ec e.isOpenEmbedding q))

end PoincareConjecture.Proofs.M02.Topology
