import PoincareConjecture.Proofs.M02.Topology.IntegralOpenOrientation
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupport
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportEmbeddingHomologyIso

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set TopologicalSpace

universe u

namespace PoincareConjecture.Proofs.M02.Topology

theorem integralSupportDetected_of_openEmbedding
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Set X) (hK : IsCompact K) :
    IntegralSupportDetected K 3 := by
  intro a ha
  let KC : Compacts X := ⟨K, hK⟩
  let m := homologyMap (integralSupportEmbeddingChains f hf.injective K) 3
  let : IsIso m := integralSupportEmbeddingChains_homology_isIso f hf KC 3
  apply (ModuleCat.mono_iff_injective m).mp inferInstance
  rw [map_zero]
  apply hDY (f '' K) (hK.image f.continuous)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hsingleton : ({x} : Set X) ⊆ K := singleton_subset_iff.mpr hx
  have hnat := integralSupportEmbeddingChains_naturality f hf.injective hsingleton
  have hnatH := congrArg (fun g => homologyMap g 3) hnat
  rw [homologyMap_comp, homologyMap_comp] at hnatH
  have he := congrArg (fun g => g a) hnatH
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at he
  change integralSupportHomologyRestriction (image_mono hsingleton) 3 (m a) =
      homologyMap (integralSupportEmbeddingChains f hf.injective ({x} : Set X)) 3
        (integralSupportHomologyRestriction hsingleton 3 a) at he
  rw [ha x hx, map_zero] at he
  have hreverse : ({f x} : Set Y) ⊆ f '' ({x} : Set X) := by
    intro z hz
    rw [mem_singleton_iff] at hz
    exact ⟨x, mem_singleton x, hz.symm⟩
  have he' := congrArg (fun b => integralSupportHomologyRestriction hreverse 3 b) he
  rw [map_zero, integralSupportHomologyRestriction_apply_comp] at he'
  exact he'

end PoincareConjecture.Proofs.M02.Topology
