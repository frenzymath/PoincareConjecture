import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralSupportEmbeddingHomologyIso
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralCompactGluing
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex TopologicalSpace Set

universe u

namespace Poincare.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y] [LocallyCompactSpace X]

private def singletonCompact (x : X) : Compacts X :=
  ⟨{x}, isCompact_singleton⟩

private theorem singleton_embedding_isIso
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace X]
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f) (x : X) :
    IsIso (homologyMap
      (integralSupportEmbeddingChains f hf.injective ({x} : Set X)) 3) := by
  have h := integralSupportEmbeddingChains_homology_isIso f hf (singletonCompact x) 3
  exact h

def integralOpenOrientation
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (x : X) : integralSupportHomology ({x} : Set X) 3 := by
  letI := singleton_embedding_isIso f hf x
  exact inv (homologyMap
    (integralSupportEmbeddingChains f hf.injective ({x} : Set X)) 3)
    (integralSupportHomologyRestriction
      (show f '' ({x} : Set X) ⊆ ({f x} : Set Y) from by
        rintro y ⟨z, rfl, rfl⟩
        rfl) 3 (omegaY (f x)))

theorem integralOpenOrientation_point
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (x : X) :
    homologyMap (integralSupportEmbeddingChains f hf.injective ({x} : Set X)) 3
        (integralOpenOrientation f hf omegaY x) =
      integralSupportHomologyRestriction
        (show f '' ({x} : Set X) ⊆ ({f x} : Set Y) from by
          rintro y ⟨z, rfl, rfl⟩
          rfl) 3 (omegaY (f x)) := by
  let := singleton_embedding_isIso f hf x
  change homologyMap (integralSupportEmbeddingChains f hf.injective ({x} : Set X)) 3
      (inv (homologyMap
        (integralSupportEmbeddingChains f hf.injective ({x} : Set X)) 3)
        (integralSupportHomologyRestriction _ 3 (omegaY (f x)))) = _
  exact IsIso.inv_hom_id_apply
    (homologyMap (integralSupportEmbeddingChains f hf.injective ({x} : Set X)) 3) _

theorem integralOpenOrientation_locallyRepresented
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : integralSupportHomology B 3,
        ∀ z : Y, ∀ hz : z ∈ B,
          integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaY z) :
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ b : integralSupportHomology U 3,
        ∀ y : X, ∀ hy : y ∈ U,
          integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b =
            integralOpenOrientation f hf omegaY y := by
  intro x
  obtain ⟨B, hB, hfxB, c, hc⟩ := hlocalY (f x)
  have hpre : IsOpen (f ⁻¹' B) := hB.preimage f.continuous
  obtain ⟨K, hK, hxK, hKpre⟩ := exists_compact_between isCompact_singleton hpre
    (singleton_subset_iff.mpr hfxB)
  let KC : Compacts X := ⟨K, hK⟩
  have himageB : f '' K ⊆ B := by
    rintro z ⟨y, hy, rfl⟩
    exact hKpre hy
  have hiK := integralSupportEmbeddingChains_homology_isIso f hf KC 3
  let : IsIso (homologyMap
      (integralSupportEmbeddingChains f hf.injective K) 3) := hiK
  let a : integralSupportHomology K 3 :=
    inv (homologyMap (integralSupportEmbeddingChains f hf.injective K) 3)
      (integralSupportHomologyRestriction himageB 3 c)
  let U := interior K
  have hUK : U ⊆ K := interior_subset
  refine ⟨U, isOpen_interior, hxK (mem_singleton x),
    integralSupportHomologyRestriction hUK 3 a, ?_⟩
  intro y hy
  have hiY := singleton_embedding_isIso f hf y
  let : IsIso (homologyMap
      (integralSupportEmbeddingChains f hf.injective ({y} : Set X)) 3) := hiY
  apply (ModuleCat.mono_iff_injective
    (homologyMap (integralSupportEmbeddingChains f hf.injective ({y} : Set X)) 3)).mp
    inferInstance
  rw [integralOpenOrientation_point]
  have hyK : y ∈ K := hUK hy
  have hsingleU : ({y} : Set X) ⊆ U := singleton_subset_iff.mpr hy
  have hsingleK : ({y} : Set X) ⊆ K := singleton_subset_iff.mpr hyK
  have hnat := integralSupportEmbeddingChains_naturality f hf.injective hsingleK
  have hnatH := congrArg (fun g => homologyMap g 3) hnat
  rw [homologyMap_comp, homologyMap_comp] at hnatH
  have haMap : homologyMap (integralSupportEmbeddingChains f hf.injective K) 3 a =
      integralSupportHomologyRestriction himageB 3 c := by
    change homologyMap (integralSupportEmbeddingChains f hf.injective K) 3
      (inv (homologyMap (integralSupportEmbeddingChains f hf.injective K) 3)
        (integralSupportHomologyRestriction himageB 3 c)) = _
    exact IsIso.inv_hom_id_apply
      (homologyMap (integralSupportEmbeddingChains f hf.injective K) 3) _
  have he := congrArg (fun g => g a) hnatH
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, haMap] at he
  change homologyMap (integralSupportEmbeddingChains f hf.injective ({y} : Set X)) 3
      (integralSupportHomologyRestriction hsingleU 3
        (integralSupportHomologyRestriction hUK 3 a)) = _
  rw [integralSupportHomologyRestriction_apply_comp]
  have hproof : hsingleU.trans hUK = hsingleK := Subsingleton.elim _ _
  rw [hproof]
  change homologyMap (integralSupportEmbeddingChains f hf.injective ({y} : Set X)) 3
      (homologyMap (integralSupportRestriction hsingleK) 3 a) = _
  rw [← he]
  change integralSupportHomologyRestriction (image_mono hsingleK) 3
      (integralSupportHomologyRestriction himageB 3 c) = _
  rw [integralSupportHomologyRestriction_apply_comp]
  have hfyB : f y ∈ B := himageB ⟨y, hyK, rfl⟩
  have hcomp : (image_mono hsingleK).trans himageB =
      (show f '' ({y} : Set X) ⊆ B from fun z hz => himageB (image_mono hsingleK hz)) :=
    Subsingleton.elim _ _
  rw [hcomp]
  have himageSingleton : f '' ({y} : Set X) ⊆ ({f y} : Set Y) := by
    rintro z ⟨w, hw, rfl⟩
    rw [mem_singleton_iff] at hw
    subst w
    rfl
  have htoB : f '' ({y} : Set X) ⊆ B := fun z hz => himageB (image_mono hsingleK hz)
  have hcomposition := integralSupportHomologyRestriction_apply_comp
    himageSingleton (singleton_subset_iff.mpr hfyB) 3 c
  rw [hc (f y) hfyB] at hcomposition
  rw [← hcomposition]

end Poincare.Topology
