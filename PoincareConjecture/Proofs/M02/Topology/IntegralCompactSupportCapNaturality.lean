import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportCap
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactCohomologyOpenMap
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportCapMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y] [RegularSpace X] [RegularSpace Y]

variable (hDX : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
  (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
  (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
  (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
  (hlocalX : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ b : integralSupportHomology U 3,
      ∀ y : X, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = omegaX y)
  (hlocalY : ∀ y : Y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
    ∃ b : integralSupportHomology U 3,
      ∀ z : Y, ∀ hz : z ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 b = omegaY z)

theorem integralCompactSupportCapOne_openEmbedding_naturality
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (horient : ∀ K : Compacts X,
      homologyMap (integralSupportEmbeddingChains f hf.injective (K : Set X)) 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX) =
      integralCompactSupportOrientation hDY omegaY (K.map f f.continuous) hlocalY) :
    integralCompactSupportCapOne hDX omegaX hlocalX ≫
        homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 2 =
      integralCompactSupportCohomologyOpenMap f hf 1 ≫
        integralCompactSupportCapOne hDY omegaY hlocalY := by
  apply integralCompactSupportCohomology_hom_ext 1
  intro K
  apply (cancel_epi (integralSupportOpenEmbeddingCohomologyIso f hf K 1).hom).mp
  simp only [integralCompactSupportCohomologyOpenMap_pullback_class_assoc,
    integralCompactSupportCapOne_class_assoc]
  rw [integralCompactSupportCapOne_class hDY omegaY hlocalY (K.map f f.continuous)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  simp only [ModuleCat.comp_apply]
  change homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 2
      (integralSupportCapHomologyOne (K : Set X)ᶜ
        (integralCompactSupportOrientation hDX omegaX K hlocalX)
        (homologyMap (integralDualMap
          (integralSupportEmbeddingChains f hf.injective (K : Set X))) 1 phi)) =
    integralSupportCapHomologyOne ((K.map f f.continuous : Compacts Y) : Set Y)ᶜ
      (integralCompactSupportOrientation hDY omegaY (K.map f f.continuous) hlocalY) phi
  have hmap : MapsTo f (K : Set X)ᶜ (f '' (K : Set X))ᶜ := by
    intro x hx
    rintro ⟨y, hy, hxy⟩
    exact hx (hf.injective hxy ▸ hy)
  have hn := integralSupportCapHomologyOne_map f hmap
    (integralCompactSupportOrientation hDX omegaX K hlocalX) phi
  have hrel : integralRelativeMap f hmap =
      integralSupportEmbeddingChains f hf.injective (K : Set X) := rfl
  rw [hrel, horient K] at hn
  exact hn

theorem integralCompactSupportCapTwo_openEmbedding_naturality
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (horient : ∀ K : Compacts X,
      homologyMap (integralSupportEmbeddingChains f hf.injective (K : Set X)) 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX) =
      integralCompactSupportOrientation hDY omegaY (K.map f f.continuous) hlocalY) :
    integralCompactSupportCapTwo hDX omegaX hlocalX ≫
        homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 1 =
      integralCompactSupportCohomologyOpenMap f hf 2 ≫
        integralCompactSupportCapTwo hDY omegaY hlocalY := by
  apply integralCompactSupportCohomology_hom_ext 2
  intro K
  apply (cancel_epi (integralSupportOpenEmbeddingCohomologyIso f hf K 2).hom).mp
  simp only [integralCompactSupportCohomologyOpenMap_pullback_class_assoc,
    integralCompactSupportCapTwo_class_assoc]
  rw [integralCompactSupportCapTwo_class hDY omegaY hlocalY (K.map f f.continuous)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  simp only [ModuleCat.comp_apply]
  change homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 1
      (integralSupportCapHomologyTwo (K : Set X)ᶜ
        (integralCompactSupportOrientation hDX omegaX K hlocalX)
        (homologyMap (integralDualMap
          (integralSupportEmbeddingChains f hf.injective (K : Set X))) 2 phi)) =
    integralSupportCapHomologyTwo ((K.map f f.continuous : Compacts Y) : Set Y)ᶜ
      (integralCompactSupportOrientation hDY omegaY (K.map f f.continuous) hlocalY) phi
  have hmap : MapsTo f (K : Set X)ᶜ (f '' (K : Set X))ᶜ := by
    intro x hx
    rintro ⟨y, hy, hxy⟩
    exact hx (hf.injective hxy ▸ hy)
  have hn := integralSupportCapHomologyTwo_map f hmap
    (integralCompactSupportOrientation hDX omegaX K hlocalX) phi
  have hrel : integralRelativeMap f hmap =
      integralSupportEmbeddingChains f hf.injective (K : Set X) := rfl
  rw [hrel, horient K] at hn
  exact hn

theorem integralCompactSupportCapThree_openEmbedding_naturality
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (horient : ∀ K : Compacts X,
      homologyMap (integralSupportEmbeddingChains f hf.injective (K : Set X)) 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX) =
      integralCompactSupportOrientation hDY omegaY (K.map f f.continuous) hlocalY) :
    integralCompactSupportCapThree hDX omegaX hlocalX ≫
        homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0 =
      integralCompactSupportCohomologyOpenMap f hf 3 ≫
        integralCompactSupportCapThree hDY omegaY hlocalY := by
  apply integralCompactSupportCohomology_hom_ext 3
  intro K
  apply (cancel_epi (integralSupportOpenEmbeddingCohomologyIso f hf K 3).hom).mp
  simp only [integralCompactSupportCohomologyOpenMap_pullback_class_assoc,
    integralCompactSupportCapThree_class_assoc]
  rw [integralCompactSupportCapThree_class hDY omegaY hlocalY (K.map f f.continuous)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  simp only [ModuleCat.comp_apply]
  change homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0
      (integralSupportCapHomologyThree (K : Set X)ᶜ
        (integralCompactSupportOrientation hDX omegaX K hlocalX)
        (homologyMap (integralDualMap
          (integralSupportEmbeddingChains f hf.injective (K : Set X))) 3 phi)) =
    integralSupportCapHomologyThree ((K.map f f.continuous : Compacts Y) : Set Y)ᶜ
      (integralCompactSupportOrientation hDY omegaY (K.map f f.continuous) hlocalY) phi
  have hmap : MapsTo f (K : Set X)ᶜ (f '' (K : Set X))ᶜ := by
    intro x hx
    rintro ⟨y, hy, hxy⟩
    exact hx (hf.injective hxy ▸ hy)
  have hn := integralSupportCapHomologyThree_map f hmap
    (integralCompactSupportOrientation hDX omegaX K hlocalX) phi
  have hrel : integralRelativeMap f hmap =
      integralSupportEmbeddingChains f hf.injective (K : Set X) := rfl
  rw [hrel, horient K] at hn
  exact hn

end PoincareConjecture.Proofs.M02.Topology
