import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Orientation.IntegralCompactOrientation
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralSupportEmbeddingHomologyIso
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex TopologicalSpace Set

universe u

namespace Poincare.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y] [RegularSpace X] [RegularSpace Y]

theorem integralCompactSupportOrientation_openEmbedding
    (hDX : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
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
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (hpoint : ∀ x : X,
      homologyMap (integralSupportEmbeddingChains f hf.injective ({x} : Set X)) 3
        (omegaX x) =
      integralSupportHomologyRestriction
        (show f '' ({x} : Set X) ⊆ ({f x} : Set Y) from by
          rintro y ⟨z, rfl, rfl⟩
          rfl) 3 (omegaY (f x)))
    (K : Compacts X) :
    homologyMap (integralSupportEmbeddingChains f hf.injective (K : Set X)) 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX) =
      integralCompactSupportOrientation hDY omegaY (K.map f f.continuous) hlocalY := by
  apply sub_eq_zero.mp
  apply hDY ((K.map f f.continuous : Compacts Y) : Set Y)
    (K.isCompact.image f.continuous)
  intro y hy
  change y ∈ f '' (K : Set X) at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [map_sub]
  have hsingleton : ({x} : Set X) ⊆ (K : Set X) := singleton_subset_iff.mpr hx
  have hnat := integralSupportEmbeddingChains_naturality f hf.injective hsingleton
  have hnatH := congrArg (fun g => homologyMap g 3) hnat
  rw [homologyMap_comp, homologyMap_comp] at hnatH
  have hleft := congrArg (fun g => g (integralCompactSupportOrientation hDX omegaX K hlocalX)) hnatH
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hleft
  change integralSupportHomologyRestriction (image_mono hsingleton) 3
      (homologyMap (integralSupportEmbeddingChains f hf.injective (K : Set X)) 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX)) =
    homologyMap (integralSupportEmbeddingChains f hf.injective ({x} : Set X)) 3
      (integralSupportHomologyRestriction hsingleton 3
        (integralCompactSupportOrientation hDX omegaX K hlocalX)) at hleft
  rw [integralCompactSupportOrientation_spec hDX omegaX K hlocalX x hx,
    hpoint x] at hleft
  have himage : f '' ({x} : Set X) ⊆ ({f x} : Set Y) := by
    rintro z ⟨w, rfl, rfl⟩
    rfl
  have hreverse : ({f x} : Set Y) ⊆ f '' ({x} : Set X) := by
    intro z hz
    rw [mem_singleton_iff] at hz
    exact ⟨x, mem_singleton x, hz.symm⟩
  have hleft' := congrArg
    (fun a => integralSupportHomologyRestriction hreverse 3 a) hleft
  rw [integralSupportHomologyRestriction_apply_comp,
    integralSupportHomologyRestriction_apply_comp] at hleft'
  have hdirect : (singleton_subset_iff.mpr ⟨x, hx, rfl⟩ :
      ({f x} : Set Y) ⊆ f '' (K : Set X)) = hreverse.trans (image_mono hsingleton) :=
    Subsingleton.elim _ _
  have hrefl : Set.Subset.refl ({f x} : Set Y) = hreverse.trans himage :=
    Subsingleton.elim _ _
  rw [← hdirect, ← hrefl] at hleft'
  have hrestrictionRefl :
      integralSupportHomologyRestriction (Set.Subset.refl ({f x} : Set Y)) 3 =
        𝟙 (integralSupportHomology ({f x} : Set Y) 3) := by
    change homologyMap (integralSupportRestriction (Set.Subset.refl ({f x} : Set Y))) 3 = _
    have hs : integralSupportRestriction (Set.Subset.refl ({f x} : Set Y)) =
        𝟙 (integralSupportChains ({f x} : Set Y)) := by
      apply (cancel_epi (integralRelativeProjection ({f x} : Set Y)ᶜ)).mp
      rw [integralSupportRestriction_projection, Category.comp_id]
    rw [hs, homologyMap_id]
  rw [hrestrictionRefl, ModuleCat.id_apply] at hleft'
  have hfirst :
      integralSupportHomologyRestriction
          (singleton_subset_iff.mpr (show f x ∈ ((K.map f f.continuous : Compacts Y) : Set Y) from
            ⟨x, hx, rfl⟩)) 3
          (homologyMap (integralSupportEmbeddingChains f hf.injective (K : Set X)) 3
            (integralCompactSupportOrientation hDX omegaX K hlocalX)) = omegaY (f x) := by
    exact hleft'
  rw [hfirst]
  have hfxK : f x ∈ ((K.map f f.continuous : Compacts Y) : Set Y) := ⟨x, hx, rfl⟩
  change omegaY (f x) -
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hfxK) 3
        (integralCompactSupportOrientation hDY omegaY (K.map f f.continuous) hlocalY) = 0
  have hspec := integralCompactSupportOrientation_spec hDY omegaY
    (K.map f f.continuous) hlocalY (f x) hfxK
  have hspec' :
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hfxK) 3
          (integralCompactSupportOrientation hDY omegaY (K.map f f.continuous) hlocalY) =
        omegaY (f x) := by
    convert hspec using 1
  rw [hspec', sub_self]

end Poincare.Topology
