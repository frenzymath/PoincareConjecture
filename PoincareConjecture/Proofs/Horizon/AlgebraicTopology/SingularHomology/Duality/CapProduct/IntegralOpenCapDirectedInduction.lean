import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralOpenCapProperty
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Orientation.IntegralCompactOrientationEmbedding
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Orientation.IntegralOpenOrientationCompatibility
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.IntegralCompactSupportDirectedUnion
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CompactSupport.IntegralCompactSupportCapNaturality
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Chains.IntegralOpenHomeomorphData


set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u v

namespace Poincare.Topology


variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
  [LocallyCompactSpace Y]
  (hDX : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
  (omegaX : ∀ x : Y, integralSupportHomology ({x} : Set Y) 3)
  (hlocalX : ∀ x : Y, ∃ B : Set Y, IsOpen B ∧ x ∈ B ∧
    ∃ c : integralSupportHomology B 3, ∀ y : Y, ∀ hy : y ∈ B,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaX y)

private def nestedOpenInclusion {A B : Set Y} (hAB : A ⊆ B) : C(A, B) :=
  ⟨fun x => ⟨x.1, hAB x.2⟩,
    continuous_subtype_val.subtype_mk (fun x => hAB x.property)⟩

private theorem nestedOpenInclusion_isOpenEmbedding
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
    [LocallyCompactSpace Y]
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (hAB : A ⊆ B) :
    _root_.Topology.IsOpenEmbedding (nestedOpenInclusion hAB) := by
  apply _root_.Topology.IsOpenEmbedding.of_comp (nestedOpenInclusion hAB)
    (hB.isOpenEmbedding_subtypeVal)
  have hfun : (Subtype.val : B → Y) ∘ nestedOpenInclusion hAB =
      (Subtype.val : A → Y) := by
    funext x
    rfl
  rw [hfun]
  exact hA.isOpenEmbedding_subtypeVal

private theorem nestedOpenOrientation
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (hAB : A ⊆ B)
    [LocallyCompactSpace A] [LocallyCompactSpace B]
    (K : Compacts A) :
    homologyMap (integralSupportEmbeddingChains (nestedOpenInclusion hAB)
      (nestedOpenInclusion_isOpenEmbedding hA hB hAB).injective (K : Set A)) 3
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData A hDX hA)
          (integralOpenOmegaData hA
            omegaX)
          K
          (integralOpenLocalOrientationData hA
            omegaX
            hlocalX)) =
      integralCompactSupportOrientation
        (integralOpenSupportDetectedData B hDX hB)
        (integralOpenOmegaData hB
          omegaX)
        (K.map (nestedOpenInclusion hAB) (nestedOpenInclusion hAB).continuous)
        (integralOpenLocalOrientationData hB
          omegaX
          hlocalX) := by
  refine integralCompactSupportOrientation_openEmbedding
    (integralOpenSupportDetectedData A hDX hA)
    (integralOpenSupportDetectedData B hDX hB)
    (integralOpenOmegaData hA
      omegaX)
    (integralOpenOmegaData hB
      omegaX)
    (integralOpenLocalOrientationData hA
      omegaX
      hlocalX)
    (integralOpenLocalOrientationData hB
      omegaX
      hlocalX)
    (nestedOpenInclusion hAB) (nestedOpenInclusion_isOpenEmbedding hA hB hAB) ?_ K
  intro x
  have hc := integralOpenOrientation_comp
    (nestedOpenInclusion hAB) (integralOpenSubtypeVal B)
    (nestedOpenInclusion_isOpenEmbedding hA hB hAB)
    (integralOpenSubtypeVal_isOpenEmbedding B hB)
    omegaX x
  have hval : (integralOpenSubtypeVal B).comp (nestedOpenInclusion hAB) =
      integralOpenSubtypeVal A := by
    ext y
    simp [integralOpenSubtypeVal, nestedOpenInclusion]
  have hOmega :
      integralOpenOmegaData hA
          omegaX x =
        integralOpenOrientation (nestedOpenInclusion hAB)
          (nestedOpenInclusion_isOpenEmbedding hA hB hAB)
          (integralOpenOmegaData hB
            omegaX) x := by
    rw [integralOpenOmegaData, integralOpenOmegaData]
    simpa only [hval] using hc
  rw [hOmega]
  simpa [integralOpenOmegaData] using
    (integralOpenOrientation_point (nestedOpenInclusion hAB)
      (nestedOpenInclusion_isOpenEmbedding hA hB hAB)
      (integralOpenOmegaData hB
        omegaX) x)

private theorem nestedOpenCapNaturalityOne
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (hAB : A ⊆ B)
    [LocallyCompactSpace A] [LocallyCompactSpace B] :
    integralCompactSupportCapOne
        (integralOpenSupportDetectedData A hDX hA)
        (integralOpenOmegaData hA
          omegaX)
        (integralOpenLocalOrientationData hA
          omegaX
          hlocalX) ≫
        homologyMap (integralChainsFunctor.map
          (TopCat.ofHom (nestedOpenInclusion hAB))) 2 =
      integralCompactSupportCohomologyOpenMap (nestedOpenInclusion hAB)
        (nestedOpenInclusion_isOpenEmbedding hA hB hAB) 1 ≫
        integralCompactSupportCapOne
          (integralOpenSupportDetectedData B hDX hB)
          (integralOpenOmegaData hB
            omegaX)
          (integralOpenLocalOrientationData hB
            omegaX
            hlocalX) :=
  integralCompactSupportCapOne_openEmbedding_naturality
    (integralOpenSupportDetectedData A hDX hA)
    (integralOpenSupportDetectedData B hDX hB)
    (integralOpenOmegaData hA
      omegaX)
    (integralOpenOmegaData hB
      omegaX)
    (integralOpenLocalOrientationData hA
      omegaX
      hlocalX)
    (integralOpenLocalOrientationData hB
      omegaX
      hlocalX)
    (nestedOpenInclusion hAB) (nestedOpenInclusion_isOpenEmbedding hA hB hAB)
    (nestedOpenOrientation hDX omegaX hlocalX hA hB hAB)

private theorem nestedOpenCapNaturalityTwo
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (hAB : A ⊆ B)
    [LocallyCompactSpace A] [LocallyCompactSpace B] :
    integralCompactSupportCapTwo
        (integralOpenSupportDetectedData A hDX hA)
        (integralOpenOmegaData hA
          omegaX)
        (integralOpenLocalOrientationData hA
          omegaX
          hlocalX) ≫
        homologyMap (integralChainsFunctor.map
          (TopCat.ofHom (nestedOpenInclusion hAB))) 1 =
      integralCompactSupportCohomologyOpenMap (nestedOpenInclusion hAB)
        (nestedOpenInclusion_isOpenEmbedding hA hB hAB) 2 ≫
        integralCompactSupportCapTwo
          (integralOpenSupportDetectedData B hDX hB)
          (integralOpenOmegaData hB
            omegaX)
          (integralOpenLocalOrientationData hB
            omegaX
            hlocalX) :=
  integralCompactSupportCapTwo_openEmbedding_naturality
    (integralOpenSupportDetectedData A hDX hA)
    (integralOpenSupportDetectedData B hDX hB)
    (integralOpenOmegaData hA
      omegaX)
    (integralOpenOmegaData hB
      omegaX)
    (integralOpenLocalOrientationData hA
      omegaX
      hlocalX)
    (integralOpenLocalOrientationData hB
      omegaX
      hlocalX)
    (nestedOpenInclusion hAB) (nestedOpenInclusion_isOpenEmbedding hA hB hAB)
    (nestedOpenOrientation hDX omegaX hlocalX hA hB hAB)

private theorem nestedOpenCapNaturalityThree
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (hAB : A ⊆ B)
    [LocallyCompactSpace A] [LocallyCompactSpace B] :
    integralCompactSupportCapThree
        (integralOpenSupportDetectedData A hDX hA)
        (integralOpenOmegaData hA
          omegaX)
        (integralOpenLocalOrientationData hA
          omegaX
          hlocalX) ≫
        homologyMap (integralChainsFunctor.map
          (TopCat.ofHom (nestedOpenInclusion hAB))) 0 =
      integralCompactSupportCohomologyOpenMap (nestedOpenInclusion hAB)
        (nestedOpenInclusion_isOpenEmbedding hA hB hAB) 3 ≫
        integralCompactSupportCapThree
          (integralOpenSupportDetectedData B hDX hB)
          (integralOpenOmegaData hB
            omegaX)
          (integralOpenLocalOrientationData hB
            omegaX
            hlocalX) :=
  integralCompactSupportCapThree_openEmbedding_naturality
    (integralOpenSupportDetectedData A hDX hA)
    (integralOpenSupportDetectedData B hDX hB)
    (integralOpenOmegaData hA
      omegaX)
    (integralOpenOmegaData hB
      omegaX)
    (integralOpenLocalOrientationData hA
      omegaX
      hlocalX)
    (integralOpenLocalOrientationData hB
      omegaX
      hlocalX)
    (nestedOpenInclusion hAB) (nestedOpenInclusion_isOpenEmbedding hA hB hAB)
    (nestedOpenOrientation hDX omegaX hlocalX hA hB hAB)

private theorem directedStage_openEmbedding
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
    [LocallyCompactSpace Y]
    {I : Type v} (U : I → Set Y) (i : I) (hU : ∀ j, IsOpen (U j)) :
    _root_.Topology.IsOpenEmbedding (integralDirectedUnionInclusion U i) := by
  let B : Set Y := ⋃ j, U j
  apply _root_.Topology.IsOpenEmbedding.of_comp
    (integralDirectedUnionInclusion U i) (isOpen_iUnion hU).isOpenEmbedding_subtypeVal
  change _root_.Topology.IsOpenEmbedding (integralOpenSubtypeVal (U i))
  exact (hU i).isOpenEmbedding_subtypeVal

private theorem directedStageOrientation
    {I : Type v} (U : I → Set Y) (i : I) (hU : ∀ j, IsOpen (U j))
    [LocallyCompactSpace (U i)] [LocallyCompactSpace (⋃ j, U j)]
    (K : Compacts (U i)) :
    homologyMap (integralSupportEmbeddingChains (integralDirectedUnionInclusion U i)
      (directedStage_openEmbedding U i hU).injective (K : Set (U i))) 3
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U i) hDX (hU i))
          (integralOpenOmegaData (hU i)
            omegaX) K
          (integralOpenLocalOrientationData (hU i)
            omegaX
            hlocalX)) =
      integralCompactSupportOrientation
        (integralOpenSupportDetectedData (⋃ j, U j) hDX
          (isOpen_iUnion hU))
        (integralOpenOmegaData (isOpen_iUnion hU)
          omegaX)
        (K.map (integralDirectedUnionInclusion U i)
          (integralDirectedUnionInclusion U i).continuous)
        (integralOpenLocalOrientationData (isOpen_iUnion hU)
          omegaX
          hlocalX) := by
  exact nestedOpenOrientation hDX omegaX hlocalX (hU i) (isOpen_iUnion hU)
    (fun x hx => mem_iUnion.mpr ⟨i, hx⟩) K

set_option maxHeartbeats 800000 in

private theorem integralHomology_eventually_zero_of_directed_union_zero
    {X : Type u} [TopologicalSpace X] {I : Type v} [Nonempty I]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (fun A B : Set X => A ⊆ B) U)
    (i : I) (n : Nat) (b : integralHomology (U i) n)
    (hb : integralDirectedUnionHomologyMap U i n b = 0) :
    ∃ (j : I) (hij : U i ⊆ U j),
      homologyMap (integralNestedChains hij) n b = 0 := by
  let B : Set X := ⋃ j, U j
  let hIB : U i ⊆ B := fun x hx => mem_iUnion.mpr ⟨i, hx⟩
  let F : integralChains (U i) ⟶ integralChains B := integralNestedChains hIB
  obtain ⟨z, hz⟩ :=
    (ModuleCat.epi_iff_surjective ((integralChains (U i)).homologyπ n)).mp inferInstance b
  have hzero : (integralChains B).homologyπ n
      (HomologicalComplex.cyclesMap F n z) = 0 := by
    have he := congrArg (fun f => f z)
      (HomologicalComplex.homologyπ_naturality (φ := F) (i := n))
    change homologyMap F n ((integralChains (U i)).homologyπ n z) =
      (integralChains B).homologyπ n (HomologicalComplex.cyclesMap F n z) at he
    rw [hz] at he
    rw [← integralDirectedUnionHomologyMap_eq_nested U i n, hb] at he
    exact he.symm
  obtain ⟨e, he⟩ :=
    (integralHomology_homologyπ_eq_zero_iff (integralChains B) n
      (HomologicalComplex.cyclesMap F n z)).mp hzero
  have hemap : (integralChains B).d (n + 1) n e =
      F.f n ((integralChains (U i)).iCycles n z) := by
    have hi := congrArg (fun f => f z)
      (HomologicalComplex.cyclesMap_i F n)
    change (integralChains B).iCycles n (HomologicalComplex.cyclesMap F n z) =
      F.f n ((integralChains (U i)).iCycles n z) at hi
    exact he.trans hi
  let W : I → Set B := fun j => (Subtype.val : B → X) ⁻¹' U j
  have hW : ∀ j, IsOpen (W j) := by
    intro j
    exact (hU j).preimage continuous_subtype_val
  classical
  let E := (integralChainCoordinates B (n + 1) e).support
  let K : Set B := ⋃ s ∈ E, Set.range s
  have hKcompact : IsCompact K := by
    exact E.isCompact_biUnion (fun s _ => isCompact_range s.continuous)
  have hKcover : K ⊆ ⋃ j, W j := by
    intro x hx
    obtain ⟨s, hs, y, rfl⟩ := Set.mem_iUnion₂.mp hx
    have hy : (s y : X) ∈ ⋃ j, U j := by
      exact (s y).property
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨j₀, hj₀⟩ := hKcompact.elim_directed_cover W hW hKcover (by
    intro j k
    obtain ⟨l, hjl, hkl⟩ := hdir j k
    exact ⟨l, fun x hx => hjl hx, fun x hx => hkl hx⟩)
  obtain ⟨j, hij, hj₀j⟩ := hdir i j₀
  have hUj : U j₀ ⊆ U j := hj₀j
  have hKj : K ⊆ W j := by
    intro x hx
    exact hUj (hj₀ hx)
  let hJB : U j ⊆ B := fun x hx => mem_iUnion.mpr ⟨j, hx⟩
  have hErange : ∀ s ∈ (integralChainCoordinates B (n + 1) e).support,
      Set.range ((⟨Subtype.val, continuous_subtype_val⟩ : C(B, X)).comp s) ⊆ U j := by
    intro s hs y hy
    obtain ⟨x, rfl⟩ := hy
    exact hKj (Set.mem_iUnion₂.mpr ⟨s, hs, ⟨x, rfl⟩⟩)
  obtain ⟨e', he'⟩ :=
    integralNestedChains_preimage_of_support hJB (n + 1) e hErange
  have hdd : (integralChains (U j)).d (n + 1) n e' =
      (integralNestedChains hij).f n ((integralChains (U i)).iCycles n z) := by
    apply integralNestedChains_injective hJB n
    have hcomm := congrArg (fun q => q e')
      ((integralNestedChains hJB).comm (n + 1) n)
    change (integralChains B).d (n + 1) n
        ((integralNestedChains hJB).f (n + 1) e') =
      (integralNestedChains hJB).f n
        ((integralChains (U j)).d (n + 1) n e') at hcomm
    have hcomp := congrArg (fun f => f.f (n + 1))
      (integralNestedChains_subspaceChains hJB)
    have hcomp' := congrArg (fun q => q e') hcomp
    change (integralSubspaceChains B).f (n + 1)
        ((integralNestedChains hJB).f (n + 1) e') =
      (integralSubspaceChains (U j)).f (n + 1) e' at hcomp'
    rw [he', hemap] at hcomm
    have hchain : integralNestedChains hij ≫ integralNestedChains hJB = F := by
      change integralChainsFunctor.map (integralNestedInclusion hij) ≫
          integralChainsFunctor.map (integralNestedInclusion hJB) =
        integralChainsFunctor.map (integralNestedInclusion hIB)
      rw [← integralChainsFunctor.map_comp]
      congr 1
    have hchain_n := congrArg (fun q => q.f n) hchain
    have hchain_apply := congrArg
      (fun q => q ((integralChains (U i)).iCycles n z)) hchain_n
    change (integralNestedChains hJB).f n
        ((integralNestedChains hij).f n
          ((integralChains (U i)).iCycles n z)) =
      F.f n ((integralChains (U i)).iCycles n z) at hchain_apply
    exact hcomm.symm.trans hchain_apply.symm
  let zj : (integralChains (U j)).cycles n :=
    HomologicalComplex.cyclesMap (integralNestedChains hij) n z
  have hzj : (integralChains B).homologyπ n
      (HomologicalComplex.cyclesMap (integralNestedChains hJB) n zj) = 0 := by
    have hchain : integralNestedChains hij ≫ integralNestedChains hJB = F := by
      change integralChainsFunctor.map (integralNestedInclusion hij) ≫
          integralChainsFunctor.map (integralNestedInclusion hJB) =
        integralChainsFunctor.map (integralNestedInclusion hIB)
      rw [← integralChainsFunctor.map_comp]
      congr 1
    have hcycle : HomologicalComplex.cyclesMap (integralNestedChains hJB) n zj =
        HomologicalComplex.cyclesMap F n z := by
      dsimp [zj]
      have hc := congrArg (fun q => q z)
        (HomologicalComplex.cyclesMap_comp
          (integralNestedChains hij) (integralNestedChains hJB) n)
      change (HomologicalComplex.cyclesMap
          (integralNestedChains hij ≫ integralNestedChains hJB) n) z =
        (HomologicalComplex.cyclesMap (integralNestedChains hJB) n)
          ((HomologicalComplex.cyclesMap (integralNestedChains hij) n) z) at hc
      rw [← hc]
      rw [hchain]
    rw [hcycle]
    exact hzero
  have hmap : homologyMap (integralNestedChains hij) n b =
      (integralChains (U j)).homologyπ n zj := by
    have heq := congrArg (fun f => f z)
      (HomologicalComplex.homologyπ_naturality
        (φ := integralNestedChains hij) (i := n))
    change homologyMap (integralNestedChains hij) n
        ((integralChains (U i)).homologyπ n z) =
      (integralChains (U j)).homologyπ n zj at heq
    rw [← hz]
    exact heq
  refine ⟨j, hij, ?_⟩
  rw [hmap]
  apply (integralHomology_homologyπ_eq_zero_iff (integralChains (U j)) n zj).mpr
  have hzj_i : (integralChains (U j)).iCycles n zj =
      (integralNestedChains hij).f n ((integralChains (U i)).iCycles n z) := by
    exact congrArg (fun q => q z)
      (HomologicalComplex.cyclesMap_i (integralNestedChains hij) n)
  exact ⟨e', hdd.trans hzj_i.symm⟩

theorem integralOpenCapProperty_directed_union
    {I : Type v} [Nonempty I] (U : I → Set Y)
    (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (fun A B : Set Y => A ⊆ B) U)
    (hstage : ∀ i, integralOpenCapProperty hDX omegaX hlocalX (U i) (hU i)) :
    integralOpenCapProperty hDX omegaX hlocalX (⋃ i, U i) (isOpen_iUnion hU) := by
  let B : Set Y := ⋃ i, U i
  let hB : IsOpen B := isOpen_iUnion hU
  let : LocallyCompactSpace B := hB.locallyCompactSpace
  dsimp [integralOpenCapProperty] at hstage ⊢
  let d1B := integralCompactSupportCapOne
    (integralOpenSupportDetectedData B hDX hB)
    (integralOpenOmegaData hB
      omegaX)
    (integralOpenLocalOrientationData hB
      omegaX
      hlocalX)
  let d2B := integralCompactSupportCapTwo
    (integralOpenSupportDetectedData B hDX hB)
    (integralOpenOmegaData hB
      omegaX)
    (integralOpenLocalOrientationData hB
      omegaX
      hlocalX)
  let d3B := integralCompactSupportCapThree
    (integralOpenSupportDetectedData B hDX hB)
    (integralOpenOmegaData hB
      omegaX)
    (integralOpenLocalOrientationData hB
      omegaX
      hlocalX)
  have hd1 : Function.Surjective d1B := by
    intro y
    obtain ⟨i, yi, hy⟩ := exists_integralHomology_directed_union_stage U hU hdir 2 y
    let : LocallyCompactSpace (U i) := (hU i).locallyCompactSpace
    obtain ⟨xi, hxi⟩ := (ModuleCat.epi_iff_surjective _).mp (hstage i).1 yi
    let f := integralDirectedUnionInclusion U i
    let hf := directedStage_openEmbedding U i hU
    have hn := integralCompactSupportCapOne_openEmbedding_naturality
      (integralOpenSupportDetectedData (U i) hDX (hU i))
      (integralOpenSupportDetectedData B hDX hB)
      (integralOpenOmegaData (hU i)
        omegaX)
      (integralOpenOmegaData hB
        omegaX)
      (integralOpenLocalOrientationData (hU i)
        omegaX
        hlocalX)
      (integralOpenLocalOrientationData hB
        omegaX
        hlocalX)
      f hf (directedStageOrientation hDX omegaX hlocalX U i hU)
    refine ⟨(integralCompactSupportCohomologyOpenMap f hf 1).hom xi, ?_⟩
    have heval := congrArg (fun g => g xi) hn
    change homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 2
        ((integralCompactSupportCapOne
          (integralOpenSupportDetectedData (U i) hDX (hU i))
          (integralOpenOmegaData (hU i)
            omegaX)
          (integralOpenLocalOrientationData (hU i)
            omegaX
            hlocalX)) xi) =
      d1B ((integralCompactSupportCohomologyOpenMap f hf 1).hom xi) at heval
    rw [hxi] at heval
    exact heval.symm.trans hy
  have hd2 : IsIso d2B := by
    apply (ConcreteCategory.isIso_iff_bijective d2B).mpr
    constructor
    · intro x y hxy
      obtain ⟨i, zi, hzi⟩ :=
        exists_integralCompactSupportCohomology_directed_union_stage U hU hdir 2 (x - y)
      let : LocallyCompactSpace (U i) := (hU i).locallyCompactSpace
      let d2i := integralCompactSupportCapTwo
        (integralOpenSupportDetectedData (U i) hDX (hU i))
        (integralOpenOmegaData (hU i)
          omegaX)
        (integralOpenLocalOrientationData (hU i)
          omegaX
          hlocalX)
      let f := integralDirectedUnionInclusion U i
      let hf := directedStage_openEmbedding U i hU
      have hn := integralCompactSupportCapTwo_openEmbedding_naturality
        (integralOpenSupportDetectedData (U i) hDX (hU i))
        (integralOpenSupportDetectedData B hDX hB)
        (integralOpenOmegaData (hU i)
          omegaX)
        (integralOpenOmegaData hB
          omegaX)
        (integralOpenLocalOrientationData (hU i)
          omegaX
          hlocalX)
        (integralOpenLocalOrientationData hB
          omegaX
          hlocalX)
        f hf (directedStageOrientation hDX omegaX hlocalX U i hU)
      have hz : d2B (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      have heval := congrArg (fun g => g zi) hn
      change homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 1
          (d2i zi) =
        d2B ((integralCompactSupportCohomologyOpenMap f hf 2).hom zi) at heval
      rw [hzi] at heval
      have hzeroStage : integralDirectedUnionHomologyMap U i 1 (d2i zi) = 0 := by
        change homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 1 (d2i zi) = 0
        exact heval.trans hz
      obtain ⟨j, hij, hzeroj⟩ :=
        integralHomology_eventually_zero_of_directed_union_zero U hU hdir i 1
          (d2i zi) hzeroStage
      let : LocallyCompactSpace (U j) := (hU j).locallyCompactSpace
      let d2j := integralCompactSupportCapTwo
        (integralOpenSupportDetectedData (U j) hDX (hU j))
        (integralOpenOmegaData (hU j)
          omegaX)
        (integralOpenLocalOrientationData (hU j)
          omegaX
          hlocalX)
      let fij := nestedOpenInclusion hij
      let hfij := nestedOpenInclusion_isOpenEmbedding (hU i) (hU j) hij
      have hnij := nestedOpenCapNaturalityTwo hDX omegaX hlocalX (hU i) (hU j) hij
      let xj := (integralCompactSupportCohomologyOpenMap fij hfij 2).hom zi
      have heij := congrArg (fun g => g zi) hnij
      change homologyMap (integralChainsFunctor.map (TopCat.ofHom fij)) 1
          (d2i zi) = d2j xj at heij
      have htop : TopCat.ofHom fij = integralNestedInclusion hij := by
        ext x
        rfl
      have hfchain : integralChainsFunctor.map (TopCat.ofHom fij) =
          integralNestedChains hij := by
        rw [integralNestedChains, htop]
      have hcapjzero : d2j xj = 0 := by
        calc
          d2j xj = homologyMap (integralChainsFunctor.map (TopCat.ofHom fij)) 1
              (d2i zi) := heij.symm
          _ = 0 := by rw [hfchain]; exact hzeroj
      let : IsIso d2j := (hstage j).2.1
      have hxj0 : xj = 0 := by
        apply (ModuleCat.mono_iff_injective d2j).mp
        · infer_instance
        · simpa using hcapjzero
      let fjB := integralDirectedUnionInclusion U j
      let hfjB := directedStage_openEmbedding U j hU
      let fiB := integralDirectedUnionInclusion U i
      let hfiB := directedStage_openEmbedding U i hU
      have hcompMap :
          integralCompactSupportCohomologyOpenMap fij hfij 2 ≫
              integralCompactSupportCohomologyOpenMap fjB hfjB 2 =
            integralCompactSupportCohomologyOpenMap fiB hfiB 2 := by
        have hc := integralCompactSupportCohomologyOpenMap_comp fij fjB hfij hfjB 2
        have hfun : fjB.comp fij = fiB := by
          ext x
          rfl
        simpa [hfun]
          using hc
      have hmapx := congrArg (fun g => g zi) hcompMap
      change (integralCompactSupportCohomologyOpenMap fjB hfjB 2).hom xj =
          (integralCompactSupportCohomologyOpenMap fiB hfiB 2).hom zi at hmapx
      rw [hzi] at hmapx
      rw [hxj0, map_zero] at hmapx
      exact sub_eq_zero.mp hmapx.symm
    · intro y
      obtain ⟨i, yi, hy⟩ := exists_integralHomology_directed_union_stage U hU hdir 1 y
      let : LocallyCompactSpace (U i) := (hU i).locallyCompactSpace
      let d2i := integralCompactSupportCapTwo
        (integralOpenSupportDetectedData (U i) hDX (hU i))
        (integralOpenOmegaData (hU i)
          omegaX)
        (integralOpenLocalOrientationData (hU i)
          omegaX
          hlocalX)
      let : IsIso d2i := (hstage i).2.1
      obtain ⟨xi, hxi⟩ :=
        (ModuleCat.epi_iff_surjective d2i).mp inferInstance yi
      let f := integralDirectedUnionInclusion U i
      let hf := directedStage_openEmbedding U i hU
      have hn := integralCompactSupportCapTwo_openEmbedding_naturality
        (integralOpenSupportDetectedData (U i) hDX (hU i))
        (integralOpenSupportDetectedData B hDX hB)
        (integralOpenOmegaData (hU i)
          omegaX)
        (integralOpenOmegaData hB
          omegaX)
        (integralOpenLocalOrientationData (hU i)
          omegaX
          hlocalX)
        (integralOpenLocalOrientationData hB
          omegaX
          hlocalX)
        f hf (directedStageOrientation hDX omegaX hlocalX U i hU)
      refine ⟨(integralCompactSupportCohomologyOpenMap f hf 2).hom xi, ?_⟩
      have heval := congrArg (fun g => g xi) hn
      change homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 1
          (d2i xi) =
        d2B ((integralCompactSupportCohomologyOpenMap f hf 2).hom xi) at heval
      rw [hxi] at heval
      exact heval.symm.trans hy
  have hd3 : IsIso d3B := by
    apply (ConcreteCategory.isIso_iff_bijective d3B).mpr
    constructor
    · intro x y hxy
      obtain ⟨i, zi, hzi⟩ :=
        exists_integralCompactSupportCohomology_directed_union_stage U hU hdir 3 (x - y)
      let : LocallyCompactSpace (U i) := (hU i).locallyCompactSpace
      let d3i := integralCompactSupportCapThree
        (integralOpenSupportDetectedData (U i) hDX (hU i))
        (integralOpenOmegaData (hU i)
          omegaX)
        (integralOpenLocalOrientationData (hU i)
          omegaX
          hlocalX)
      let f := integralDirectedUnionInclusion U i
      let hf := directedStage_openEmbedding U i hU
      have hn := integralCompactSupportCapThree_openEmbedding_naturality
        (integralOpenSupportDetectedData (U i) hDX (hU i))
        (integralOpenSupportDetectedData B hDX hB)
        (integralOpenOmegaData (hU i)
          omegaX)
        (integralOpenOmegaData hB
          omegaX)
        (integralOpenLocalOrientationData (hU i)
          omegaX
          hlocalX)
        (integralOpenLocalOrientationData hB
          omegaX
          hlocalX)
        f hf (directedStageOrientation hDX omegaX hlocalX U i hU)
      have hz : d3B (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      have heval := congrArg (fun g => g zi) hn
      change homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0
          (d3i zi) =
        d3B ((integralCompactSupportCohomologyOpenMap f hf 3).hom zi) at heval
      rw [hzi] at heval
      have hzeroStage : integralDirectedUnionHomologyMap U i 0 (d3i zi) = 0 := by
        change homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0 (d3i zi) = 0
        exact heval.trans hz
      obtain ⟨j, hij, hzeroj⟩ :=
        integralHomology_eventually_zero_of_directed_union_zero U hU hdir i 0
          (d3i zi) hzeroStage
      let : LocallyCompactSpace (U j) := (hU j).locallyCompactSpace
      let d3j := integralCompactSupportCapThree
        (integralOpenSupportDetectedData (U j) hDX (hU j))
        (integralOpenOmegaData (hU j)
          omegaX)
        (integralOpenLocalOrientationData (hU j)
          omegaX
          hlocalX)
      let fij := nestedOpenInclusion hij
      let hfij := nestedOpenInclusion_isOpenEmbedding (hU i) (hU j) hij
      have hnij := nestedOpenCapNaturalityThree hDX omegaX hlocalX (hU i) (hU j) hij
      let xj := (integralCompactSupportCohomologyOpenMap fij hfij 3).hom zi
      have heij := congrArg (fun g => g zi) hnij
      change homologyMap (integralChainsFunctor.map (TopCat.ofHom fij)) 0
          (d3i zi) = d3j xj at heij
      have htop : TopCat.ofHom fij = integralNestedInclusion hij := by
        ext x
        rfl
      have hfchain : integralChainsFunctor.map (TopCat.ofHom fij) =
          integralNestedChains hij := by
        rw [integralNestedChains, htop]
      have hcapjzero : d3j xj = 0 := by
        calc
          d3j xj = homologyMap (integralChainsFunctor.map (TopCat.ofHom fij)) 0
              (d3i zi) := heij.symm
          _ = 0 := by rw [hfchain]; exact hzeroj
      let : IsIso d3j := (hstage j).2.2.1
      have hxj0 : xj = 0 := by
        apply (ModuleCat.mono_iff_injective d3j).mp
        · infer_instance
        · simpa using hcapjzero
      let fjB := integralDirectedUnionInclusion U j
      let hfjB := directedStage_openEmbedding U j hU
      let fiB := integralDirectedUnionInclusion U i
      let hfiB := directedStage_openEmbedding U i hU
      have hcompMap :
          integralCompactSupportCohomologyOpenMap fij hfij 3 ≫
              integralCompactSupportCohomologyOpenMap fjB hfjB 3 =
            integralCompactSupportCohomologyOpenMap fiB hfiB 3 := by
        have hc := integralCompactSupportCohomologyOpenMap_comp fij fjB hfij hfjB 3
        have hfun : fjB.comp fij = fiB := by
          ext x
          rfl
        simpa [hfun] using hc
      have hmapx := congrArg (fun g => g zi) hcompMap
      change (integralCompactSupportCohomologyOpenMap fjB hfjB 3).hom xj =
          (integralCompactSupportCohomologyOpenMap fiB hfiB 3).hom zi at hmapx
      rw [hzi] at hmapx
      rw [hxj0, map_zero] at hmapx
      exact sub_eq_zero.mp hmapx.symm
    · intro y
      obtain ⟨i, yi, hy⟩ := exists_integralHomology_directed_union_stage U hU hdir 0 y
      let : LocallyCompactSpace (U i) := (hU i).locallyCompactSpace
      let d3i := integralCompactSupportCapThree
        (integralOpenSupportDetectedData (U i) hDX (hU i))
        (integralOpenOmegaData (hU i)
          omegaX)
        (integralOpenLocalOrientationData (hU i)
          omegaX
          hlocalX)
      let : IsIso d3i := (hstage i).2.2.1
      obtain ⟨xi, hxi⟩ :=
        (ModuleCat.epi_iff_surjective d3i).mp inferInstance yi
      let f := integralDirectedUnionInclusion U i
      let hf := directedStage_openEmbedding U i hU
      have hn := integralCompactSupportCapThree_openEmbedding_naturality
        (integralOpenSupportDetectedData (U i) hDX (hU i))
        (integralOpenSupportDetectedData B hDX hB)
        (integralOpenOmegaData (hU i)
          omegaX)
        (integralOpenOmegaData hB
          omegaX)
        (integralOpenLocalOrientationData (hU i)
          omegaX
          hlocalX)
        (integralOpenLocalOrientationData hB
          omegaX
          hlocalX)
        f hf (directedStageOrientation hDX omegaX hlocalX U i hU)
      refine ⟨(integralCompactSupportCohomologyOpenMap f hf 3).hom xi, ?_⟩
      have heval := congrArg (fun g => g xi) hn
      change homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0
          (d3i xi) =
        d3B ((integralCompactSupportCohomologyOpenMap f hf 3).hom xi) at heval
      rw [hxi] at heval
      exact heval.symm.trans hy
  have hd4 : ∀ q, 4 ≤ q → IsZero (integralCompactSupportCohomology B q) := by
    intro q hq
    let : Subsingleton (integralCompactSupportCohomology B q) := by
      constructor
      intro a b
      obtain ⟨i, ai, hai⟩ :=
        exists_integralCompactSupportCohomology_directed_union_stage U hU hdir q a
      obtain ⟨j, bj, hbj⟩ :=
        exists_integralCompactSupportCohomology_directed_union_stage U hU hdir q b
      let : LocallyCompactSpace (U i) := (hU i).locallyCompactSpace
      let : LocallyCompactSpace (U j) := (hU j).locallyCompactSpace
      let : Subsingleton (integralCompactSupportCohomology (U i) q) :=
        ModuleCat.subsingleton_of_isZero ((hstage i).2.2.2 q hq)
      let : Subsingleton (integralCompactSupportCohomology (U j) q) :=
        ModuleCat.subsingleton_of_isZero ((hstage j).2.2.2 q hq)
      have hai0 : ai = 0 := Subsingleton.elim _ _
      have hbj0 : bj = 0 := Subsingleton.elim _ _
      rw [← hai, ← hbj, hai0, hbj0, map_zero, map_zero]
    exact ModuleCat.isZero_of_subsingleton _
  exact ⟨(ModuleCat.epi_iff_surjective d1B).mpr hd1, hd2, hd3, hd4⟩

end Poincare.Topology
