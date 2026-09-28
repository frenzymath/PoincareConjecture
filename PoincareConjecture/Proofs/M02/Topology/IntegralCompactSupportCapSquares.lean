import PoincareConjecture.Proofs.M02.Topology.IntegralCapGlobalInduction
import PoincareConjecture.Proofs.M02.Topology.IntegralCapMayerVietorisConnecting
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportRangeCap
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenOrientationCompatibility
import PoincareConjecture.Proofs.M02.IntegralOpenCapData

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

open PoincareConjecture.Proofs.M02

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
  [LocallyCompactSpace Y]

theorem integralCompactSupportCapOne_union_connecting_square
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ z : Y, ∀ hz : z ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaY z)
    [LocallyCompactSpace ↥(U ∩ V)] [LocallyCompactSpace ↥(U ∪ V)] :
    integralCompactSupportCapOne
        (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
        (integralOpenOmegaData (hU.union hV) omegaY)
        (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY) ≫
      integralOpenUnionHomologyConnectingToIntersection U V hU hV 1 =
    integralCompactSupportOpenConnecting U V hU hV 1 ≫
      integralCompactSupportCapTwo
        (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
        (integralOpenOmegaData (hU.inter hV) omegaY)
        (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY) := by
  apply integralCompactSupportCohomology_hom_ext 1
  intro P
  obtain ⟨AB, hP⟩ := exists_integralCompactSupportOpen_cover U V hU hV P
  let A := AB.1
  let B := AB.2
  let hPset : (P : Set ↥(U ∪ V)) ⊆
      (integralCompactSupportOpenPairUnion U V hU hV A B : Set ↥(U ∪ V)) :=
    hP
  rw [← Category.assoc, integralCompactSupportCapOne_class]
  rw [← Category.assoc,
    integralCompactSupportOpenConnecting_class U V hU hV 1 P A B hP]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  simp only [ModuleCat.comp_apply]
  let K0 : Compacts (↥(U ∪ V)) :=
    A.map (integralOpenSubtypeUnionInclusion U V hU)
      (integralOpenSubtypeUnionInclusion U V hU).continuous
  let L0 : Compacts (↥(U ∪ V)) :=
    B.map (integralOpenSubtypeUnionInclusionRight U V hV)
      (integralOpenSubtypeUnionInclusionRight U V hV).continuous
  have hP' : P ≤ K0 ⊔ L0 := by
    simpa [K0, L0, integralCompactSupportOpenPairUnion] using hP
  let hPset' : (P : Set ↥(U ∪ V)) ⊆ (K0 ∪ L0 : Set ↥(U ∪ V)) := hP'
  have hK0 : IsClosed (K0 : Set ↥(U ∪ V)) := K0.isCompact.isClosed
  have hL0 : IsClosed (L0 : Set ↥(U ∪ V)) := L0.isCompact.isClosed
  have hKU0 : (K0 : Set ↥(U ∪ V)) ⊆ integralOpenUnionLeft U V := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact a.property
  have hLV0 : (L0 : Set ↥(U ∪ V)) ⊆ integralOpenUnionRight U V := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact b.property
  have hcapP := integralSupportCapHomologyOne_naturality
    hPset'
    (integralCompactSupportOrientation
      (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
      (integralOpenOmegaData (hU.union hV) omegaY)
      (integralCompactSupportOpenPairUnion U V hU hV A B)
      (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)) phi
  have hrestrict :
      integralSupportHomologyRestriction hPset' 3
          (integralCompactSupportOrientation
            (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
            (integralOpenOmegaData (hU.union hV) omegaY)
            (integralCompactSupportOpenPairUnion U V hU hV A B)
            (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)) =
        integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
          (integralOpenOmegaData (hU.union hV) omegaY) P
          (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY) := by
    have h := integralCompactSupportOrientation_restrict
      (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
      (integralOpenOmegaData (hU.union hV) omegaY)
      (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY) hP'
    simpa [integralCompactSupportOpenPairUnion, K0, L0] using h
  rw [hrestrict] at hcapP
  have hfixed := integralSupportCapHomologyOne_connecting
    (X := ↥(U ∪ V))
    (integralOpenUnionLeft U V) (K0 : Set ↥(U ∪ V))
    (integralOpenUnionRight U V) (L0 : Set ↥(U ∪ V))
    (integralOpenUnionLeft_open U V hU)
    (integralOpenUnionRight_open U V hV)
    hK0 hL0 hKU0 hLV0 (integralOpenUnion_cover U V)
    (integralCompactSupportOrientation
      (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
      (integralOpenOmegaData (hU.union hV) omegaY)
      (integralCompactSupportOpenPairUnion U V hU hV A B)
      (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY))
    ((integralSupportCohomologyPushforward hPset' 1).hom phi)
  have hfixed' := congrArg
    (integralHomeomorphHomologyIso
      (integralOpenUnionIntersectionHomeomorph U V) 1).hom hfixed
  change (integralOpenUnionHomologyConnectingToIntersection U V hU hV 1).hom
      (integralSupportCapHomologyOne (P : Set ↥(U ∪ V))ᶜ
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
          (integralOpenOmegaData (hU.union hV) omegaY) P
        (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)) phi) = _
  rw [hcapP.symm]
  rw [integralCompactSupportOpenConnectingStage]
  change _ =
    (integralCompactSupportCapTwo
      (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
      (integralOpenOmegaData (hU.inter hV) omegaY)
      (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)).hom
      ((integralCompactSupportCohomologyRangeMap
        (integralOpenIntersectionUnionInclusion U V hU)
        (integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV)
        (integralCompactSupportOpenPairIntersection U V hU hV A B)
        (integralCompactSupportOpenPairIntersection_subset_range U V hU hV A B) 2).hom
        ((integralSupportCohomologyConnecting
          (A.map (integralOpenSubtypeUnionInclusion U V hU)
            (integralOpenSubtypeUnionInclusion U V hU).continuous : Set ↥(U ∪ V))
          (B.map (integralOpenSubtypeUnionInclusionRight U V hV)
            (integralOpenSubtypeUnionInclusionRight U V hV).continuous : Set ↥(U ∪ V))
          (Compacts.isCompact _).isClosed (Compacts.isCompact _).isClosed 1).hom
    ((integralSupportCohomologyPushforward hPset 1).hom phi)))
  have hcap := integralCompactSupportCapTwo_rangeMap
    (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
    (integralOpenOmegaData (hU.inter hV) omegaY)
    (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)
    (integralOpenIntersectionUnionInclusion U V hU)
    (integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV)
    (integralCompactSupportOpenPairIntersection U V hU hV A B)
    (integralCompactSupportOpenPairIntersection_subset_range U V hU hV A B)
    ((integralSupportCohomologyConnecting
      (A.map (integralOpenSubtypeUnionInclusion U V hU)
        (integralOpenSubtypeUnionInclusion U V hU).continuous : Set ↥(U ∪ V))
      (B.map (integralOpenSubtypeUnionInclusionRight U V hV)
        (integralOpenSubtypeUnionInclusionRight U V hV).continuous : Set ↥(U ∪ V))
      (Compacts.isCompact _).isClosed (Compacts.isCompact _).isClosed 1).hom
      ((integralSupportCohomologyPushforward hPset 1).hom phi))
  let eI := integralHomeomorphHomologyIso
    (integralOpenUnionIntersectionHomeomorph U V) 1
  let zI :=
    (integralOpenSupportHomologyIso ((K0 : Set ↥(U ∪ V)) ∩ (L0 : Set ↥(U ∪ V)))
      (integralOpenUnionLeft U V ∩ integralOpenUnionRight U V)
      (hK0.inter hL0) (IsOpen.inter (integralOpenUnionLeft_open U V hU)
        (integralOpenUnionRight_open U V hV))
      (inter_subset_inter hKU0 hLV0) 3).inv
      (integralSupportHomologyRestriction
        (inter_subset_left.trans subset_union_left :
          (K0 : Set ↥(U ∪ V)) ∩ (L0 : Set ↥(U ∪ V)) ⊆
            (K0 : Set ↥(U ∪ V)) ∪ (L0 : Set ↥(U ∪ V))) 3
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
          (integralOpenOmegaData (hU.union hV) omegaY)
          (integralCompactSupportOpenPairUnion U V hU hV A B)
          (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)))
  have hPset_eq : hPset = hPset' := by
    apply Subsingleton.elim
  let t := integralOpenIntersectionUnionInclusion U V hU
  let ht := integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV
  let R := integralCompactSupportOpenPairIntersection U V hU hV A B
  let I := integralOpenUnionIntersection U V
  let eC : C(I, ↥(U ∩ V)) := integralOpenUnionIntersectionHomeomorph U V
  let cI := homologyMap
    (integralDualMap
      (integralOpenSupportMap
        ((K0 : Set ↥(U ∪ V)) ∩ (L0 : Set ↥(U ∪ V)))
        (integralOpenUnionIntersection U V))) 2
    ((integralSupportCohomologyConnecting (K0 : Set ↥(U ∪ V)) (L0 : Set ↥(U ∪ V))
      hK0 hL0 1).hom ((integralSupportCohomologyPushforward hPset' 1).hom phi))
  let fixedRhs := integralSupportCapHomologyTwo
    ((Subtype.val : (integralOpenUnionIntersection U V) → ↥(U ∪ V)) ⁻¹'
      (K0 ∩ L0 : Set ↥(U ∪ V))ᶜ) zI cI
  let Aset : Set I := (Subtype.val : I → ↥(U ∪ V)) ⁻¹'
    ((K0 : Set ↥(U ∪ V)) ∩ (L0 : Set ↥(U ∪ V)))ᶜ
  let Sset : Set (↥(U ∩ V)) := t ⁻¹' (R : Set ↥(U ∪ V))ᶜ
  have hE_maps : Set.MapsTo eC Aset Sset := by
    intro x hx
    change t (eC x) ∉ (R : Set ↥(U ∪ V))
    intro hRx
    apply hx
    change (x : ↥(U ∪ V)) ∈ (R : Set ↥(U ∪ V))
    have hxunion : (t (eC x) : ↥(U ∪ V)) = (x : ↥(U ∪ V)) := by
      rfl
    rw [← hxunion]
    exact hRx
  have hchain :
      integralRelativeMap eC hE_maps ≫ integralRangeSupportMap t (R : Set ↥(U ∪ V)) =
        integralOpenSupportMap (R : Set ↥(U ∪ V)) I := by
    change integralRelativeMap eC hE_maps ≫
      integralRelativeMap t (show Set.MapsTo t Sset (R : Set ↥(U ∪ V))ᶜ from fun _ hx => hx) = _
    rw [integralRelativeMap_comp]
    rw [integralOpenSupportMap]
    congr 1
  have hdual := congrArg (fun g => homologyMap (integralDualMap g) 2) hchain
  rw [integralDualMap_comp, homologyMap_comp] at hdual
  let c0 := (integralSupportCohomologyConnecting (K0 : Set ↥(U ∪ V))
      (L0 : Set ↥(U ∪ V)) hK0 hL0 1).hom
      ((integralSupportCohomologyPushforward hPset' 1).hom phi)
  let phiB := homologyMap
    (integralDualMap (integralRangeSupportMap t (R : Set ↥(U ∪ V)))) 2 c0
  have hmap := integralSupportCapHomologyTwo_map eC hE_maps zI phiB
  let cINew := homologyMap
    (integralDualMap (integralOpenSupportMap (R : Set ↥(U ∪ V)) I)) 2 c0
  have hcINew : homologyMap (integralDualMap (integralRelativeMap eC hE_maps)) 2 phiB = cINew := by
    have h := congrArg (fun g => g c0) hdual
    change (homologyMap (integralDualMap (integralRelativeMap eC hE_maps)) 2)
        ((homologyMap (integralDualMap (integralRangeSupportMap t (R : Set ↥(U ∪ V)))) 2) c0) =
      (homologyMap (integralDualMap (integralOpenSupportMap (R : Set ↥(U ∪ V)) I)) 2) c0 at h
    simpa [phiB, cINew] using h
  have hcINewOld : cINew = cI := by
    rfl
  have hcI : homologyMap (integralDualMap (integralRelativeMap eC hE_maps)) 2 phiB = cI :=
    hcINew.trans hcINewOld
  have hRrange : (R : Set ↥(U ∪ V)) ⊆ Set.range t := by
    change (integralCompactSupportOpenPairIntersection U V hU hV A B : Set ↥(U ∪ V)) ⊆
      Set.range (integralOpenIntersectionUnionInclusion U V hU)
    exact integralCompactSupportOpenPairIntersection_subset_range U V hU hV A B
  have horient (K : Compacts ↥(U ∩ V)) :
      homologyMap (integralSupportEmbeddingChains t ht.injective (K : Set ↥(U ∩ V))) 3
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
          (integralOpenOmegaData (hU.inter hV) omegaY) K
          (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)) =
      integralCompactSupportOrientation
        (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
        (integralOpenOmegaData (hU.union hV) omegaY)
        (K.map t t.continuous)
        (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY) := by
    simpa [t, ht] using
      (integralOpenSubtypeOrientation_openEmbedding U V hU hV
        hDY omegaY hlocalY K)
  have hRangeOrient := integralCompactSupportOrientation_rangeMap
    (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
    (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
    (integralOpenOmegaData (hU.inter hV) omegaY)
    (integralOpenOmegaData (hU.union hV) omegaY)
    (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)
    (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)
    t ht horient R hRrange
  let : IsIso (homologyMap (integralRangeSupportMap t (R : Set ↥(U ∪ V))) 3) :=
    integralRangeSupportMap_homology_isIso t ht R hRrange 3
  have hrestrictR :
      homologyMap (integralSupportRestriction
        (show (R : Set ↥(U ∪ V)) ⊆
          (integralCompactSupportOpenPairUnion U V hU hV A B : Set ↥(U ∪ V)) from
          inter_subset_left.trans subset_union_left)) 3
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
          (integralOpenOmegaData (hU.union hV) omegaY)
          (integralCompactSupportOpenPairUnion U V hU hV A B)
          (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)) =
      integralCompactSupportOrientation
        (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
        (integralOpenOmegaData (hU.union hV) omegaY) R
        (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY) := by
    exact integralCompactSupportOrientation_restrict _ _ _
      (show R ≤ integralCompactSupportOpenPairUnion U V hU hV A B from
        inter_subset_left.trans subset_union_left)
  have hopen :
      homologyMap (integralOpenSupportMap (R : Set ↥(U ∪ V)) I) 3 zI =
        integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
          (integralOpenOmegaData (hU.union hV) omegaY) R
          (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY) := by
    have he := (integralOpenSupportHomologyIso
      ((K0 : Set ↥(U ∪ V)) ∩ (L0 : Set ↥(U ∪ V)))
      (integralOpenUnionLeft U V ∩ integralOpenUnionRight U V)
      (hK0.inter hL0)
      (IsOpen.inter (integralOpenUnionLeft_open U V hU)
        (integralOpenUnionRight_open U V hV))
      (inter_subset_inter hKU0 hLV0) 3).inv_hom_id_apply
      (integralSupportHomologyRestriction
        (show (K0 : Set ↥(U ∪ V)) ∩ (L0 : Set ↥(U ∪ V)) ⊆
          (K0 : Set ↥(U ∪ V)) ∪ (L0 : Set ↥(U ∪ V)) from
          inter_subset_left.trans subset_union_left) 3
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
          (integralOpenOmegaData (hU.union hV) omegaY)
          (integralCompactSupportOpenPairUnion U V hU hV A B)
          (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)))
    have hhe := he.trans hrestrictR
    change homologyMap (integralOpenSupportMap (R : Set ↥(U ∪ V)) I) 3 zI = _ at hhe
    exact hhe
  have hzmap :
      homologyMap (integralRelativeMap eC hE_maps) 3 zI =
        integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
          (integralOpenOmegaData (hU.inter hV) omegaY)
          (integralCompactSupportRangePreimage t ht R hRrange)
          (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY) := by
    apply (ModuleCat.mono_iff_injective
      (homologyMap (integralRangeSupportMap t (R : Set ↥(U ∪ V))) 3)).mp inferInstance
    rw [← ConcreteCategory.comp_apply, ← homologyMap_comp, hchain]
    exact hopen.trans hRangeOrient.symm
  have hfixedRhs : fixedRhs = integralSupportCapHomologyTwo Aset zI
      (homologyMap (integralDualMap (integralRelativeMap eC hE_maps)) 2 phiB) := by
    rw [hcI]
  calc
    _ = eI.hom fixedRhs := by
      change (ConcreteCategory.hom eI.hom)
          ((integralOpenHomologyConnecting
            (integralOpenUnionLeft U V) (integralOpenUnionRight U V)
            (integralOpenUnionLeft_open U V hU)
            (integralOpenUnionRight_open U V hV)
            (integralOpenUnion_cover U V) 1).hom _ ) =
        (ConcreteCategory.hom eI.hom) fixedRhs
      simpa [fixedRhs, R, I, cI, zI, eI, ConcreteCategory.comp_apply,
        ModuleCat.comp_apply] using hfixed'
    _ = _ := by
      rw [hPset_eq] at hcap
      rw [hcap]
      change homologyMap (integralChainsFunctor.map (TopCat.ofHom eC)) 1 fixedRhs = _
      rw [hfixedRhs]
      change _ = integralSupportCapHomologyTwo Sset
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
          (integralOpenOmegaData (hU.inter hV) omegaY)
          (integralCompactSupportRangePreimage t ht R hRrange)
          (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)) phiB
      have hmap' := hmap
      rw [hzmap] at hmap'
      exact hmap'

end PoincareConjecture.Proofs.M02.Topology
