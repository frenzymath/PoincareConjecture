import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportOpenConnecting
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenOrientation
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenHomeomorphData
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactOrientationEmbedding
import PoincareConjecture.Proofs.M02.IntegralOpenCapData

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set TopologicalSpace

universe u

namespace PoincareConjecture.Proofs.M02.Topology

open PoincareConjecture.Proofs.M02

theorem integralOpenOrientation_comp
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [T2Space X] [T2Space Y] [T2Space Z] [LocallyCompactSpace X]
    [LocallyCompactSpace Y]
    (f : C(X, Y)) (g : C(Y, Z))
    (hf : _root_.Topology.IsOpenEmbedding f)
    (hg : _root_.Topology.IsOpenEmbedding g)
    (omegaZ : ∀ z : Z, integralSupportHomology ({z} : Set Z) 3)
    (x : X) :
    integralOpenOrientation (g.comp f) (hg.comp hf) omegaZ x =
      integralOpenOrientation f hf
        (integralOpenOrientation g hg omegaZ) x := by
  let hK : f '' ({x} : Set X) ⊆ ({f x} : Set Y) := by
    rintro y ⟨z, hz, rfl⟩
    rw [mem_singleton_iff] at hz
    subst z
    rfl
  let hG : g '' (f '' ({x} : Set X)) ⊆ ({g (f x)} : Set Z) := by
    intro z hz
    rcases hz with ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    rw [mem_singleton_iff] at hw
    subst w
    rfl
  let h1 : g '' ({f x} : Set Y) ⊆ ({g (f x)} : Set Z) := by
    rintro z ⟨w, hw, rfl⟩
    rw [mem_singleton_iff] at hw
    subst w
    rfl
  let h2 : g '' (f '' ({x} : Set X)) ⊆ g '' ({f x} : Set Y) :=
    image_mono hK
  let hc : g '' (f '' ({x} : Set X)) ⊆ (g.comp f) '' ({x} : Set X) := by
    rintro z ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  let hC1 : (g.comp f) '' ({x} : Set X) ⊆ ({g (f x)} : Set Z) := by
    rintro z ⟨w, hw, rfl⟩
    rw [mem_singleton_iff] at hw
    subst w
    rfl
  let mf := homologyMap (integralSupportEmbeddingChains f hf.injective ({x} : Set X)) 3
  let mg := homologyMap (integralSupportEmbeddingChains g hg.injective
    (f '' ({x} : Set X))) 3
  let : IsIso mf := integralSupportEmbeddingChains_homology_isIso f hf
    ⟨{x}, isCompact_singleton⟩ 3
  let : IsIso mg := integralSupportEmbeddingChains_homology_isIso g hg
    ⟨f '' ({x} : Set X), isCompact_singleton.image f.continuous⟩ 3
  have hnat := integralSupportEmbeddingChains_naturality g hg.injective hK
  have hnatH := congrArg (fun k => homologyMap k 3) hnat
  rw [homologyMap_comp, homologyMap_comp] at hnatH
  have hpointg := integralOpenOrientation_point g hg omegaZ (f x)
  have hmgPoint := congrArg (fun k => k
      (integralOpenOrientation g hg omegaZ (f x))) hnatH
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hpointg] at hmgPoint
  have hmgPoint' := hmgPoint.symm
  change mg (integralSupportHomologyRestriction hK 3
      (integralOpenOrientation g hg omegaZ (f x))) =
    integralSupportHomologyRestriction h2 3
      (integralSupportHomologyRestriction h1 3 (omegaZ (g (f x)))) at hmgPoint'
  have hr12 := integralSupportHomologyRestriction_apply_comp h2 h1 3
    (omegaZ (g (f x)))
  rw [hr12] at hmgPoint'
  have hr12G : integralSupportHomologyRestriction (h2.trans h1) 3
      (omegaZ (g (f x))) = integralSupportHomologyRestriction hG 3
      (omegaZ (g (f x))) := by
    congr 1
  rw [hr12G] at hmgPoint'
  have hcomp := congrArg (fun k => homologyMap k 3)
    (integralSupportEmbeddingChains_comp f g hf.injective hg.injective
      ({x} : Set X) hc)
  rw [homologyMap_comp, homologyMap_comp] at hcomp
  have hleft := congrArg (fun k => k
      (integralOpenOrientation (g.comp f) (hg.comp hf) omegaZ x)) hcomp
  simp only [ModuleCat.comp_apply] at hleft
  have hpointc := integralOpenOrientation_point (g.comp f) (hg.comp hf) omegaZ x
  rw [hpointc] at hleft
  have hleft' :
      mg (mf (integralOpenOrientation (g.comp f) (hg.comp hf) omegaZ x)) =
      integralSupportHomologyRestriction hG 3 (omegaZ (g (f x))) := by
    have hrc1 := integralSupportHomologyRestriction_apply_comp hc hC1 3
      (omegaZ (g (f x)))
    have hrcG : integralSupportHomologyRestriction (hc.trans hC1) 3
        (omegaZ (g (f x))) = integralSupportHomologyRestriction hG 3
        (omegaZ (g (f x))) := by
      congr 1
    exact hleft.trans (by
      change integralSupportHomologyRestriction hc 3
          (integralSupportHomologyRestriction hC1 3 (omegaZ (g (f x)))) = _
      rw [hrc1, hrcG])
  have hpointf := integralOpenOrientation_point f hf
    (integralOpenOrientation g hg omegaZ) x
  have hright' := congrArg (fun a => mg a) hpointf
  rw [hmgPoint'] at hright'
  apply (ModuleCat.mono_iff_injective mf).mp inferInstance
  apply (ModuleCat.mono_iff_injective mg).mp inferInstance
  exact hleft'.trans hright'.symm

theorem integralOpenSubtypeOrientation_openEmbedding
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
    [LocallyCompactSpace Y]
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    [LocallyCompactSpace ↥(U ∩ V)] [LocallyCompactSpace ↥(U ∪ V)]
    (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ z : Y, ∀ hz : z ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaY z)
    (K : Compacts ↥(U ∩ V)) :
    homologyMap (integralSupportEmbeddingChains
      (integralOpenIntersectionUnionInclusion U V hU)
      (integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV).injective
      (K : Set ↥(U ∩ V))) 3
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
          (integralOpenOmegaData (hU.inter hV) omegaY)
          K (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)) =
      integralCompactSupportOrientation
        (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
        (integralOpenOmegaData (hU.union hV) omegaY)
        (K.map (integralOpenIntersectionUnionInclusion U V hU)
          (integralOpenIntersectionUnionInclusion U V hU).continuous)
        (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY) := by
  refine integralCompactSupportOrientation_openEmbedding
    (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
    (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
    (integralOpenOmegaData (hU.inter hV) omegaY)
    (integralOpenOmegaData (hU.union hV) omegaY)
    (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)
    (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)
    (integralOpenIntersectionUnionInclusion U V hU)
    (integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV) ?_ K
  intro x
  have hval :
      (integralOpenSubtypeVal (U ∪ V)).comp
          (integralOpenIntersectionUnionInclusion U V hU) =
        integralOpenSubtypeVal (U ∩ V) := by
    ext y
    rfl
  have hc := integralOpenOrientation_comp
    (integralOpenIntersectionUnionInclusion U V hU)
    (integralOpenSubtypeVal (U ∪ V))
    (integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV)
    (integralOpenSubtypeVal_isOpenEmbedding (U ∪ V) (hU.union hV)) omegaY x
  have hp := integralOpenOrientation_point
    (integralOpenIntersectionUnionInclusion U V hU)
    (integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV)
    (integralOpenOmegaData (hU.union hV) omegaY) x
  have hc' :
      integralOpenOmegaData (hU.inter hV) omegaY x =
        integralOpenOrientation
          (integralOpenIntersectionUnionInclusion U V hU)
          (integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV)
          (integralOpenOmegaData (hU.union hV) omegaY) x := by
    change integralOpenOrientation (integralOpenSubtypeVal (U ∩ V)) _ omegaY x = _
    convert hc using 1
    · cases hval
      rfl
    · simp [integralOpenOmegaData]
  rw [hc']
  simpa [integralOpenOmegaData, integralOpenSubtypeVal,
    integralOpenIntersectionUnionInclusion] using hp

end PoincareConjecture.Proofs.M02.Topology
