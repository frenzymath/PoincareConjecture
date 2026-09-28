import PoincareConjecture.Proofs.M02.Topology.EuclideanBoxCover
import PoincareConjecture.Proofs.M02.Topology.IntegralEuclideanOrientation
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportHomeomorph
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportCapNaturality
import PoincareConjecture.Proofs.M02.Topology.IntegralEuclideanCapDuality
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenHomeomorphData
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenOrientation
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactOrientationEmbedding

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set TopologicalSpace

universe u

namespace PoincareConjecture.Proofs.M02.Topology

abbrev integralEuclideanBox (a b : Fin 3 → ℝ) :=
  euclideanThreeOpenBox a b

theorem box_cap_naturality_one
    {X : Type} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    (e : X ≃ₜ integralEuclideanSpace)
    (hDX : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
    (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
    (hlocalX : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ c : integralSupportHomology U 3, ∀ y : X, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaX y)
    (horient : ∀ K : Compacts X,
      homologyMap (integralSupportEmbeddingChains (e : C(X, integralEuclideanSpace))
        e.injective (K : Set X)) 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX) =
      integralCompactSupportOrientation integralEuclideanSupportDetected
        (Classical.choose exists_integralEuclideanOrientationData)
        (K.map (e : C(X, integralEuclideanSpace)) e.continuous)
        (Classical.choose_spec exists_integralEuclideanOrientationData).2) :
    Epi (integralCompactSupportCapOne hDX omegaX hlocalX) := by
  let cX := integralCompactSupportCapOne hDX omegaX hlocalX
  let cE := integralCompactSupportCapOne integralEuclideanSupportDetected
    (Classical.choose exists_integralEuclideanOrientationData)
    (Classical.choose_spec exists_integralEuclideanOrientationData).2
  let : IsIso (homologyMap (integralChainsFunctor.map (TopCat.ofHom (e : C(X,
    integralEuclideanSpace)))) 2) :=
    integralHomeomorphHomologyMap_isIso e 2
  let : IsIso (integralCompactSupportCohomologyOpenMap
      (e : C(X, integralEuclideanSpace)) e.isOpenEmbedding 1) :=
    integralCompactSupportCohomologyOpenMap_homeomorph_isIso e 1
  let : Epi cE := integralEuclideanCompactSupportCapOne_epi
    integralEuclideanSupportDetected (Classical.choose exists_integralEuclideanOrientationData)
      (Classical.choose_spec exists_integralEuclideanOrientationData).2
  let : Epi (integralCompactSupportCohomologyOpenMap
      (e : C(X, integralEuclideanSpace)) e.isOpenEmbedding 1 ≫ cE) := by
    infer_instance
  have hnat := integralCompactSupportCapOne_openEmbedding_naturality hDX
    integralEuclideanSupportDetected omegaX (Classical.choose
      exists_integralEuclideanOrientationData)
    hlocalX (Classical.choose_spec exists_integralEuclideanOrientationData).2
    (e : C(X, integralEuclideanSpace)) e.isOpenEmbedding horient
  let : Epi (cX ≫ homologyMap (integralChainsFunctor.map (TopCat.ofHom (e : C(X,
    integralEuclideanSpace)))) 2) := by
    rw [hnat]
    infer_instance
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro z
  have hcompsurj : Function.Surjective
      (cX ≫ homologyMap (integralChainsFunctor.map
        (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 2) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨x, hx⟩ := hcompsurj
    ((homologyMap (integralChainsFunctor.map (TopCat.ofHom (e : C(X,
      integralEuclideanSpace)))) 2) z)
  refine ⟨x, ?_⟩
  apply (ModuleCat.mono_iff_injective
    (homologyMap (integralChainsFunctor.map (TopCat.ofHom (e : C(X,
      integralEuclideanSpace)))) 2)).mp inferInstance
  exact hx

theorem box_cap_naturality_two
    {X : Type} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    (e : X ≃ₜ integralEuclideanSpace)
    (hDX : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
    (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
    (hlocalX : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ c : integralSupportHomology U 3, ∀ y : X, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaX y)
    (horient : ∀ K : Compacts X,
      homologyMap (integralSupportEmbeddingChains (e : C(X, integralEuclideanSpace))
        e.injective (K : Set X)) 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX) =
      integralCompactSupportOrientation integralEuclideanSupportDetected
        (Classical.choose exists_integralEuclideanOrientationData)
        (K.map (e : C(X, integralEuclideanSpace)) e.continuous)
        (Classical.choose_spec exists_integralEuclideanOrientationData).2) :
    IsIso (integralCompactSupportCapTwo hDX omegaX hlocalX) := by
  let cX := integralCompactSupportCapTwo hDX omegaX hlocalX
  let cE := integralCompactSupportCapTwo integralEuclideanSupportDetected
    (Classical.choose exists_integralEuclideanOrientationData)
    (Classical.choose_spec exists_integralEuclideanOrientationData).2
  let : IsIso (homologyMap
      (integralChainsFunctor.map (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 1) :=
    integralHomeomorphHomologyMap_isIso e 1
  let : IsIso (integralCompactSupportCohomologyOpenMap
      (e : C(X, integralEuclideanSpace)) e.isOpenEmbedding 2) :=
    integralCompactSupportCohomologyOpenMap_homeomorph_isIso e 2
  let : IsIso cE := integralEuclideanCompactSupportCapTwo_isIso
    integralEuclideanSupportDetected (Classical.choose exists_integralEuclideanOrientationData)
      (Classical.choose_spec exists_integralEuclideanOrientationData).2
  have hnat := integralCompactSupportCapTwo_openEmbedding_naturality hDX
    integralEuclideanSupportDetected omegaX (Classical.choose
      exists_integralEuclideanOrientationData)
    hlocalX (Classical.choose_spec exists_integralEuclideanOrientationData).2
    (e : C(X, integralEuclideanSpace)) e.isOpenEmbedding horient
  have hcomp : IsIso (cX ≫ homologyMap
      (integralChainsFunctor.map (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 1) := by
    rw [hnat]
    infer_instance
  let := hcomp
  exact IsIso.of_isIso_comp_right cX
    (homologyMap (integralChainsFunctor.map
      (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 1)

theorem box_cap_naturality_three
    {X : Type} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    (e : X ≃ₜ integralEuclideanSpace)
    (hDX : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
    (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
    (hlocalX : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ c : integralSupportHomology U 3, ∀ y : X, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaX y)
    (horient : ∀ K : Compacts X,
      homologyMap (integralSupportEmbeddingChains (e : C(X, integralEuclideanSpace))
        e.injective (K : Set X)) 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX) =
      integralCompactSupportOrientation integralEuclideanSupportDetected
        (Classical.choose exists_integralEuclideanOrientationData)
        (K.map (e : C(X, integralEuclideanSpace)) e.continuous)
        (Classical.choose_spec exists_integralEuclideanOrientationData).2) :
    IsIso (integralCompactSupportCapThree hDX omegaX hlocalX) := by
  let cX := integralCompactSupportCapThree hDX omegaX hlocalX
  let cE := integralCompactSupportCapThree integralEuclideanSupportDetected
    (Classical.choose exists_integralEuclideanOrientationData)
    (Classical.choose_spec exists_integralEuclideanOrientationData).2
  let : IsIso (homologyMap
      (integralChainsFunctor.map (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 0) :=
    integralHomeomorphHomologyMap_isIso e 0
  let : IsIso (integralCompactSupportCohomologyOpenMap
      (e : C(X, integralEuclideanSpace)) e.isOpenEmbedding 3) :=
    integralCompactSupportCohomologyOpenMap_homeomorph_isIso e 3
  let : IsIso cE := integralEuclideanCompactSupportCapThree_isIso
    integralEuclideanSupportDetected (Classical.choose exists_integralEuclideanOrientationData)
      (Classical.choose_spec exists_integralEuclideanOrientationData).2
      ((Classical.choose_spec exists_integralEuclideanOrientationData).1 0)
  have hnat := integralCompactSupportCapThree_openEmbedding_naturality hDX
    integralEuclideanSupportDetected omegaX (Classical.choose
      exists_integralEuclideanOrientationData)
    hlocalX (Classical.choose_spec exists_integralEuclideanOrientationData).2
    (e : C(X, integralEuclideanSpace)) e.isOpenEmbedding horient
  have hcomp : IsIso (cX ≫ homologyMap
      (integralChainsFunctor.map (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 0) := by
    rw [hnat]
    infer_instance
  let := hcomp
  exact IsIso.of_isIso_comp_right cX
    (homologyMap (integralChainsFunctor.map
      (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 0)

theorem box_cap_naturality_one_target
    {X : Type} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    (e : X ≃ₜ integralEuclideanSpace)
    (hDX : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
    (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
    (hlocalX : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ c : integralSupportHomology U 3, ∀ y : X, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaX y)
    (hDE : ∀ L : Set integralEuclideanSpace, IsCompact L → IntegralSupportDetected L 3)
    (omegaE : ∀ y : integralEuclideanSpace,
      integralSupportHomology ({y} : Set integralEuclideanSpace) 3)
    (hlocalE : ∀ y : integralEuclideanSpace, ∃ U : Set integralEuclideanSpace,
      IsOpen U ∧ y ∈ U ∧ ∃ c : integralSupportHomology U 3, ∀ z, ∀ hz : z ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaE z)
    (hcapE : Epi (integralCompactSupportCapOne hDE omegaE hlocalE))
    (horient : ∀ K : Compacts X,
      homologyMap (integralSupportEmbeddingChains (e : C(X, integralEuclideanSpace))
        e.injective (K : Set X)) 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX) =
      integralCompactSupportOrientation hDE omegaE
        (K.map (e : C(X, integralEuclideanSpace)) e.continuous) hlocalE) :
    Epi (integralCompactSupportCapOne hDX omegaX hlocalX) := by
  let cX := integralCompactSupportCapOne hDX omegaX hlocalX
  let cE := integralCompactSupportCapOne hDE omegaE hlocalE
  let : IsIso (homologyMap
      (integralChainsFunctor.map (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 2) :=
    integralHomeomorphHomologyMap_isIso e 2
  let : IsIso (integralCompactSupportCohomologyOpenMap
      (e : C(X, integralEuclideanSpace)) e.isOpenEmbedding 1) :=
    integralCompactSupportCohomologyOpenMap_homeomorph_isIso e 1
  let : Epi cE := hcapE
  let : Epi (integralCompactSupportCohomologyOpenMap
      (e : C(X, integralEuclideanSpace)) e.isOpenEmbedding 1 ≫ cE) := by
    infer_instance
  have hnat := integralCompactSupportCapOne_openEmbedding_naturality hDX hDE
    omegaX omegaE hlocalX hlocalE (e : C(X, integralEuclideanSpace))
    e.isOpenEmbedding horient
  let : Epi (cX ≫ homologyMap
      (integralChainsFunctor.map (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 2) := by
    rw [hnat]
    infer_instance
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro z
  have hcompsurj : Function.Surjective
      (cX ≫ homologyMap
        (integralChainsFunctor.map (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 2) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨x, hx⟩ := hcompsurj
    ((homologyMap (integralChainsFunctor.map
      (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 2) z)
  refine ⟨x, ?_⟩
  apply (ModuleCat.mono_iff_injective
    (homologyMap (integralChainsFunctor.map
      (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 2)).mp inferInstance
  exact hx

theorem box_cap_naturality_two_target
    {X : Type} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    (e : X ≃ₜ integralEuclideanSpace)
    (hDX : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
    (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
    (hlocalX : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ c : integralSupportHomology U 3, ∀ y : X, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaX y)
    (hDE : ∀ L : Set integralEuclideanSpace, IsCompact L → IntegralSupportDetected L 3)
    (omegaE : ∀ y : integralEuclideanSpace,
      integralSupportHomology ({y} : Set integralEuclideanSpace) 3)
    (hlocalE : ∀ y : integralEuclideanSpace, ∃ U : Set integralEuclideanSpace,
      IsOpen U ∧ y ∈ U ∧ ∃ c : integralSupportHomology U 3, ∀ z, ∀ hz : z ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaE z)
    (hcapE : IsIso (integralCompactSupportCapTwo hDE omegaE hlocalE))
    (horient : ∀ K : Compacts X,
      homologyMap (integralSupportEmbeddingChains (e : C(X, integralEuclideanSpace))
        e.injective (K : Set X)) 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX) =
      integralCompactSupportOrientation hDE omegaE
        (K.map (e : C(X, integralEuclideanSpace)) e.continuous) hlocalE) :
    IsIso (integralCompactSupportCapTwo hDX omegaX hlocalX) := by
  let cX := integralCompactSupportCapTwo hDX omegaX hlocalX
  let cE := integralCompactSupportCapTwo hDE omegaE hlocalE
  let : IsIso (homologyMap
      (integralChainsFunctor.map (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 1) :=
    integralHomeomorphHomologyMap_isIso e 1
  let : IsIso (integralCompactSupportCohomologyOpenMap
      (e : C(X, integralEuclideanSpace)) e.isOpenEmbedding 2) :=
    integralCompactSupportCohomologyOpenMap_homeomorph_isIso e 2
  let : IsIso cE := hcapE
  have hnat := integralCompactSupportCapTwo_openEmbedding_naturality hDX hDE
    omegaX omegaE hlocalX hlocalE (e : C(X, integralEuclideanSpace))
    e.isOpenEmbedding horient
  have hcomp : IsIso (cX ≫ homologyMap
      (integralChainsFunctor.map (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 1) := by
    rw [hnat]
    infer_instance
  let := hcomp
  exact IsIso.of_isIso_comp_right cX
    (homologyMap (integralChainsFunctor.map
      (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 1)

theorem box_cap_naturality_three_target
    {X : Type} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    (e : X ≃ₜ integralEuclideanSpace)
    (hDX : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
    (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
    (hlocalX : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ c : integralSupportHomology U 3, ∀ y : X, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaX y)
    (hDE : ∀ L : Set integralEuclideanSpace, IsCompact L → IntegralSupportDetected L 3)
    (omegaE : ∀ y : integralEuclideanSpace,
      integralSupportHomology ({y} : Set integralEuclideanSpace) 3)
    (hlocalE : ∀ y : integralEuclideanSpace, ∃ U : Set integralEuclideanSpace,
      IsOpen U ∧ y ∈ U ∧ ∃ c : integralSupportHomology U 3, ∀ z, ∀ hz : z ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaE z)
    (hcapE : IsIso (integralCompactSupportCapThree hDE omegaE hlocalE))
    (horient : ∀ K : Compacts X,
      homologyMap (integralSupportEmbeddingChains (e : C(X, integralEuclideanSpace))
        e.injective (K : Set X)) 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX) =
      integralCompactSupportOrientation hDE omegaE
        (K.map (e : C(X, integralEuclideanSpace)) e.continuous) hlocalE) :
    IsIso (integralCompactSupportCapThree hDX omegaX hlocalX) := by
  let cX := integralCompactSupportCapThree hDX omegaX hlocalX
  let cE := integralCompactSupportCapThree hDE omegaE hlocalE
  let : IsIso (homologyMap
      (integralChainsFunctor.map (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 0) :=
    integralHomeomorphHomologyMap_isIso e 0
  let : IsIso (integralCompactSupportCohomologyOpenMap
      (e : C(X, integralEuclideanSpace)) e.isOpenEmbedding 3) :=
    integralCompactSupportCohomologyOpenMap_homeomorph_isIso e 3
  let : IsIso cE := hcapE
  have hnat := integralCompactSupportCapThree_openEmbedding_naturality hDX hDE
    omegaX omegaE hlocalX hlocalE (e : C(X, integralEuclideanSpace))
    e.isOpenEmbedding horient
  have hcomp : IsIso (cX ≫ homologyMap
      (integralChainsFunctor.map (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 0) := by
    rw [hnat]
    infer_instance
  let := hcomp
  exact IsIso.of_isIso_comp_right cX
    (homologyMap (integralChainsFunctor.map
      (TopCat.ofHom (e : C(X, integralEuclideanSpace)))) 0)

theorem integralEuclideanBoxSupportDetected
    (a b : Fin 3 → ℝ) (hn : (integralEuclideanBox a b).Nonempty) :
    ∀ L : Set (integralEuclideanBox a b), IsCompact L → IntegralSupportDetected L 3 :=
  integralSupportDetected_of_openEmbedding integralEuclideanSupportDetected
    (euclideanThreeOpenBoxHomeomorph a b hn :
      C(integralEuclideanBox a b, integralEuclideanSpace))
    (euclideanThreeOpenBoxHomeomorph a b hn).isOpenEmbedding

noncomputable def integralEuclideanBoxOmega
    (a b : Fin 3 → ℝ) (hn : (integralEuclideanBox a b).Nonempty) :
    ∀ x : integralEuclideanBox a b,
      integralSupportHomology ({x} : Set (integralEuclideanBox a b)) 3 :=
  by
    letI : LocallyCompactSpace (integralEuclideanBox a b) :=
      (euclideanThreeOpenBox_isOpen a b).locallyCompactSpace
    let e : integralEuclideanBox a b ≃ₜ integralEuclideanSpace :=
      euclideanThreeOpenBoxHomeomorph a b hn
    let ec : C(integralEuclideanBox a b, integralEuclideanSpace) := e
    exact integralOpenOrientation ec e.isOpenEmbedding
      (Classical.choose exists_integralEuclideanOrientationData)

theorem integralEuclideanBoxLocal
    (a b : Fin 3 → ℝ) (hn : (integralEuclideanBox a b).Nonempty) :
    ∀ x : integralEuclideanBox a b, ∃ U : Set (integralEuclideanBox a b), IsOpen U ∧ x ∈ U ∧
      ∃ c : integralSupportHomology U 3, ∀ y : integralEuclideanBox a b, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c =
          integralEuclideanBoxOmega a b hn y :=
  by
    let : LocallyCompactSpace (integralEuclideanBox a b) :=
      (euclideanThreeOpenBox_isOpen a b).locallyCompactSpace
    let e : integralEuclideanBox a b ≃ₜ integralEuclideanSpace :=
      euclideanThreeOpenBoxHomeomorph a b hn
    let ec : C(integralEuclideanBox a b, integralEuclideanSpace) := e
    let h := integralOpenOrientation_locallyRepresented ec e.isOpenEmbedding
      (Classical.choose exists_integralEuclideanOrientationData)
      (Classical.choose_spec exists_integralEuclideanOrientationData).2
    simpa only [integralEuclideanBoxOmega] using h

theorem integralEuclideanBoxCapOne_epi
    (a b : Fin 3 → ℝ) (hn : (integralEuclideanBox a b).Nonempty) :
    Epi (integralCompactSupportCapOne
      (integralEuclideanBoxSupportDetected a b hn)
      (integralEuclideanBoxOmega a b hn)
      (integralEuclideanBoxLocal a b hn)) := by
  let : LocallyCompactSpace (integralEuclideanBox a b) :=
    (euclideanThreeOpenBox_isOpen a b).locallyCompactSpace
  let e : integralEuclideanBox a b ≃ₜ integralEuclideanSpace :=
    euclideanThreeOpenBoxHomeomorph a b hn
  let ec : C(integralEuclideanBox a b, integralEuclideanSpace) := e
  let hDX := integralSupportDetected_of_openEmbedding integralEuclideanSupportDetected
    ec e.isOpenEmbedding
  let omegaX := integralOpenOrientation ec e.isOpenEmbedding
    (Classical.choose exists_integralEuclideanOrientationData)
  let hlocalX := integralOpenOrientation_locallyRepresented ec e.isOpenEmbedding
    (Classical.choose exists_integralEuclideanOrientationData)
    (Classical.choose_spec exists_integralEuclideanOrientationData).2
  apply box_cap_naturality_one e hDX omegaX hlocalX
  intro K
  apply integralCompactSupportOrientation_openEmbedding hDX integralEuclideanSupportDetected
    omegaX (Classical.choose exists_integralEuclideanOrientationData) hlocalX
    (Classical.choose_spec exists_integralEuclideanOrientationData).2 ec e.isOpenEmbedding
  intro x
  exact integralOpenOrientation_point ec e.isOpenEmbedding
    (Classical.choose exists_integralEuclideanOrientationData) x

theorem integralEuclideanBoxCapTwo_isIso
    (a b : Fin 3 → ℝ) (hn : (integralEuclideanBox a b).Nonempty) :
    IsIso (integralCompactSupportCapTwo
      (integralEuclideanBoxSupportDetected a b hn)
      (integralEuclideanBoxOmega a b hn)
      (integralEuclideanBoxLocal a b hn)) := by
  let : LocallyCompactSpace (integralEuclideanBox a b) :=
    (euclideanThreeOpenBox_isOpen a b).locallyCompactSpace
  let e : integralEuclideanBox a b ≃ₜ integralEuclideanSpace :=
    euclideanThreeOpenBoxHomeomorph a b hn
  let ec : C(integralEuclideanBox a b, integralEuclideanSpace) := e
  let hDX := integralSupportDetected_of_openEmbedding integralEuclideanSupportDetected
    ec e.isOpenEmbedding
  let omegaX := integralOpenOrientation ec e.isOpenEmbedding
    (Classical.choose exists_integralEuclideanOrientationData)
  let hlocalX := integralOpenOrientation_locallyRepresented ec e.isOpenEmbedding
    (Classical.choose exists_integralEuclideanOrientationData)
    (Classical.choose_spec exists_integralEuclideanOrientationData).2
  apply box_cap_naturality_two e hDX omegaX hlocalX
  intro K
  apply integralCompactSupportOrientation_openEmbedding hDX integralEuclideanSupportDetected
    omegaX (Classical.choose exists_integralEuclideanOrientationData) hlocalX
    (Classical.choose_spec exists_integralEuclideanOrientationData).2 ec e.isOpenEmbedding
  intro x
  exact integralOpenOrientation_point ec e.isOpenEmbedding
    (Classical.choose exists_integralEuclideanOrientationData) x

theorem integralEuclideanBoxCapThree_isIso
    (a b : Fin 3 → ℝ) (hn : (integralEuclideanBox a b).Nonempty) :
    IsIso (integralCompactSupportCapThree
      (integralEuclideanBoxSupportDetected a b hn)
      (integralEuclideanBoxOmega a b hn)
      (integralEuclideanBoxLocal a b hn)) := by
  let : LocallyCompactSpace (integralEuclideanBox a b) :=
    (euclideanThreeOpenBox_isOpen a b).locallyCompactSpace
  let e : integralEuclideanBox a b ≃ₜ integralEuclideanSpace :=
    euclideanThreeOpenBoxHomeomorph a b hn
  let ec : C(integralEuclideanBox a b, integralEuclideanSpace) := e
  let hDX := integralSupportDetected_of_openEmbedding integralEuclideanSupportDetected
    ec e.isOpenEmbedding
  let omegaX := integralOpenOrientation ec e.isOpenEmbedding
    (Classical.choose exists_integralEuclideanOrientationData)
  let hlocalX := integralOpenOrientation_locallyRepresented ec e.isOpenEmbedding
    (Classical.choose exists_integralEuclideanOrientationData)
    (Classical.choose_spec exists_integralEuclideanOrientationData).2
  apply box_cap_naturality_three e hDX omegaX hlocalX
  intro K
  apply integralCompactSupportOrientation_openEmbedding hDX integralEuclideanSupportDetected
    omegaX (Classical.choose exists_integralEuclideanOrientationData) hlocalX
    (Classical.choose_spec exists_integralEuclideanOrientationData).2 ec e.isOpenEmbedding
  intro x
  exact integralOpenOrientation_point ec e.isOpenEmbedding
    (Classical.choose exists_integralEuclideanOrientationData) x

end PoincareConjecture.Proofs.M02.Topology
