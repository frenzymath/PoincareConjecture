import PoincareConjecture.Proofs.M02.Topology.IntegralOpenCapProperty
import PoincareConjecture.Proofs.M02.Topology.IntegralEuclideanBoxCap
import PoincareConjecture.Proofs.M02.Topology.IntegralEuclideanCompactCohomology
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenOrientation
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenOrientationCompatibility



set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Limits TopologicalSpace Set

namespace PoincareConjecture.Proofs.M02.Topology

open PoincareConjecture.Proofs.M02

private theorem supportRestriction_isIso_of_eq
    {X : Type} [TopologicalSpace X] {K L : Set X} {n : Nat}
    (hKL : K ⊆ L) (hEq : K = L) :
    IsIso (integralSupportHomologyRestriction hKL n) := by
  subst L
  have hh : hKL = Set.Subset.refl K := Subsingleton.elim _ _
  rw [hh]
  change IsIso (homologyMap (integralSupportRestriction (Set.Subset.refl K)) n)
  have hrest : integralSupportRestriction (Set.Subset.refl K) = 𝟙 _ := by
    apply (cancel_epi (integralRelativeProjection Kᶜ)).mp
    rw [integralSupportRestriction_projection]
    rfl
  rw [hrest, homologyMap_id]
  infer_instance

private theorem openOrientation_id_apply
    {X : Type} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    [LocallyCompactSpace X]
    (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3) (x : X) :
    integralOpenOrientation (ContinuousMap.id X)
      _root_.Topology.IsOpenEmbedding.id omegaX x = omegaX x := by
  have hf : Function.Injective (ContinuousMap.id X) := fun _ _ h => h
  have hIK : (ContinuousMap.id X) '' ({x} : Set X) ⊆ ({x} : Set X) := by
    rintro y ⟨z, hz, rfl⟩
    exact hz
  have hchain : integralSupportEmbeddingChains (ContinuousMap.id X) hf
      ({x} : Set X) = integralSupportRestriction hIK := by
    apply (cancel_epi (integralRelativeProjection ({x} : Set X)ᶜ)).mp
    rw [integralSupportEmbeddingChains_projection, integralSupportRestriction_projection]
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

private theorem openOrientation_homeomorph_inverse_apply
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
  rw [openOrientation_id_apply] at hc'
  exact hc'.symm

private theorem openOrientation_generator
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
  let : IsIso r := supportRestriction_isIso_of_eq hval himage
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

set_option maxHeartbeats 3000000 in

theorem integralOpenCapProperty_of_homeomorph_euclidean
    {X : Type} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    [LocallyCompactSpace X]
    (hDX : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
    (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
    (hlocalX : ∀ x : X, ∃ B : Set X, IsOpen B ∧ x ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ y : X, ∀ hy : y ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaX y)
    (hgenX : ∀ x : X, ∃ g : Int ≃ₗ[Int]
      integralSupportHomology ({x} : Set X) 3, g 1 = omegaX x)
    (U : Set X) (hU : IsOpen U) (e : U ≃ₜ E) :
    integralOpenCapProperty hDX omegaX hlocalX U hU := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let ec : C(U, E) := e
  let hDU := integralOpenSupportDetectedData U hDX hU
  let omegaU := integralOpenOmegaData hU omegaX
  let hlocalU := integralOpenLocalOrientationData hU omegaX hlocalX
  let omegaE := integralOpenOrientation (e.symm : C(E, U))
    e.symm.isOpenEmbedding omegaU
  let hlocalE := integralOpenOrientation_locallyRepresented
    (e.symm : C(E, U)) e.symm.isOpenEmbedding omegaU hlocalU
  have hgenU : ∀ x : U, ∃ g : Int ≃ₗ[Int]
      integralSupportHomology ({x} : Set U) 3, g 1 = omegaU x := by
    intro x
    simpa [omegaU, integralOpenOmegaData] using
      (openOrientation_generator (integralOpenSubtypeVal U)
        (integralOpenSubtypeVal_isOpenEmbedding U hU) omegaX hgenX x)
  have hgenE : ∃ g : Int ≃ₗ[Int]
      integralSupportHomology ({0} : Set E) 3, g 1 = omegaE 0 := by
    obtain ⟨g, hg⟩ := openOrientation_generator
      (e.symm : C(E, U)) e.symm.isOpenEmbedding omegaU hgenU 0
    exact ⟨g, by simpa [omegaE] using hg⟩
  have hpoint : ∀ x : U,
      homologyMap (integralSupportEmbeddingChains ec e.injective ({x} : Set U)) 3
          (omegaU x) =
        integralSupportHomologyRestriction
          (show ec '' ({x} : Set U) ⊆ ({ec x} : Set E) from by
            rintro y ⟨z, hz, rfl⟩
            rw [mem_singleton_iff] at hz ⊢
            subst z
            rfl) 3 (omegaE (ec x)) := by
    intro x
    have hp := integralOpenOrientation_point ec e.isOpenEmbedding omegaE x
    have hr := openOrientation_homeomorph_inverse_apply e omegaU x
    change homologyMap (integralSupportEmbeddingChains ec e.injective
      ({x} : Set U)) 3
        (integralOpenOrientation ec e.isOpenEmbedding omegaE x) = _ at hp
    rw [hr] at hp
    exact hp
  have horient : ∀ K : Compacts U,
      homologyMap (integralSupportEmbeddingChains ec e.injective (K : Set U)) 3
        (integralCompactSupportOrientation hDU omegaU K hlocalU) =
      integralCompactSupportOrientation integralEuclideanSupportDetected omegaE
        (K.map ec ec.continuous) hlocalE := by
    intro K
    exact integralCompactSupportOrientation_openEmbedding hDU
      integralEuclideanSupportDetected omegaU omegaE hlocalU hlocalE ec
      e.isOpenEmbedding hpoint K
  change Epi (integralCompactSupportCapOne hDU omegaU hlocalU) ∧
    IsIso (integralCompactSupportCapTwo hDU omegaU hlocalU) ∧
    IsIso (integralCompactSupportCapThree hDU omegaU hlocalU) ∧
    ∀ q : Nat, 4 ≤ q → IsZero (integralCompactSupportCohomology U q)
  constructor
  · exact box_cap_naturality_one_target e hDU omegaU hlocalU
      integralEuclideanSupportDetected omegaE hlocalE
      (integralEuclideanCompactSupportCapOne_epi integralEuclideanSupportDetected
        omegaE hlocalE) horient
  constructor
  · exact box_cap_naturality_two_target e hDU omegaU hlocalU
      integralEuclideanSupportDetected omegaE hlocalE
      (integralEuclideanCompactSupportCapTwo_isIso integralEuclideanSupportDetected
        omegaE hlocalE) horient
  constructor
  · exact box_cap_naturality_three_target e hDU omegaU hlocalU
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
