import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralOpenMayerVietoris
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Homology.IntegralSmallHomology
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralChainSupport

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u v

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem integralSmallChains_support
    {I : Type v} (U : I → Set X) (n : Nat)
    {c : (integralChains X).X n} (hc : c ∈ integralSmallChains U n) :
    ∀ s ∈ (integralChainCoordinates X n c).support,
      IntegralSmallSimplex U s := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨s, rfl⟩ t ht
    have hts : t = s.val := by
      rw [integralChainCoordinates_generator,
        Finsupp.mem_support_iff] at ht
      by_contra hne
      exact ht (Finsupp.single_eq_of_ne hne)
    simpa [hts] using s.property
  · intro t ht
    have ht' : (integralChainCoordinates X n (0 : (integralChains X).X n)) t ≠ 0 :=
      Finsupp.mem_support_iff.mp ht
    exact False.elim (ht' (by simp))
  · intro x y hx hy hxs hys t ht
    by_cases hxt : t ∈ (integralChainCoordinates X n x).support
    · exact hxs t hxt
    · by_cases hyt : t ∈ (integralChainCoordinates X n y).support
      · exact hys t hyt
      · exfalso
        apply (Finsupp.mem_support_iff.mp ht)
        rw [map_add]
        have hx0 : (integralChainCoordinates X n x) t = 0 := by
          by_contra hx0
          exact hxt (Finsupp.mem_support_iff.mpr hx0)
        have hy0 : (integralChainCoordinates X n y) t = 0 := by
          by_contra hy0
          exact hyt (Finsupp.mem_support_iff.mpr hy0)
        change (integralChainCoordinates X n x) t +
          (integralChainCoordinates X n y) t = 0
        rw [hx0, hy0, add_zero]
  · intro a x hx hxs t ht
    by_cases hxt : t ∈ (integralChainCoordinates X n x).support
    · exact hxs t hxt
    · exfalso
      apply (Finsupp.mem_support_iff.mp ht)
      have hx0 : (integralChainCoordinates X n x) t = 0 := by
        by_contra hx0
        exact hxt (Finsupp.mem_support_iff.mpr hx0)
      have hcoord := congrArg (fun q => q t)
        ((integralChainCoordinates X n).map_smul a x)
      rw [hcoord]
      exact (by simpa only [Finsupp.smul_apply, smul_zero] using
        congrArg (fun q : ULift.{u} Int => a • q) hx0)

theorem integralNestedChains_preimage_of_support
    {A B : Set X} (hAB : A ⊆ B) (n : Nat)
    (c : (integralChains B).X n)
    (hc : ∀ s ∈ (integralChainCoordinates B n c).support,
      Set.range ((⟨Subtype.val, continuous_subtype_val⟩ : C(B, X)).comp s) ⊆ A) :
    ∃ d : (integralChains A).X n,
      (integralNestedChains hAB).f n d = c := by
  let fB : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let iB := integralSubspaceChains B
  let cB := iB.f n c
  have hf : Function.Injective (fun s : C(integralSimplex n, B) => fB.comp s) := by
    intro s t h
    ext z
    exact congrArg (fun q : C(integralSimplex n, X) => q z) h
  have hcoord := integralChainCoordinates_map fB n c
  have hcoords : ∀ t ∈ (integralChainCoordinates X n cB).support,
      Set.range t ⊆ A := by
    change ∀ t ∈ (integralChainCoordinates X n
      ((integralChainsFunctor.map (TopCat.ofHom fB)).f n c)).support,
      Set.range t ⊆ A
    rw [hcoord]
    intro t ht
    obtain ⟨s, rfl⟩ :=
      Finsupp.mem_range_of_mapDomain_ne_zero (Finsupp.mem_support_iff.mp ht)
    have hs : s ∈ (integralChainCoordinates B n c).support := by
      have heq := Finsupp.mapDomain_apply hf
        (integralChainCoordinates B n c) s
      rw [Finsupp.mem_support_iff]
      rw [← heq]
      exact Finsupp.mem_support_iff.mp ht
    exact hc s hs
  obtain ⟨d, hd⟩ :=
    (integral_subspace_range_iff A n cB).mpr hcoords
  refine ⟨d, ?_⟩
  let := integralSubspaceChains_mono B
  apply (ModuleCat.mono_iff_injective ((integralSubspaceChains B).f n)).mp inferInstance
  have hcomp := congrArg (fun f => f.f n)
    (integralNestedChains_subspaceChains hAB)
  have hcomp' := congrArg (fun f => f d) hcomp
  change (integralSubspaceChains B).f n
      ((integralNestedChains hAB).f n d) =
    (integralSubspaceChains A).f n d at hcomp'
  exact hcomp'.trans (hd.trans rfl)

theorem exists_finset_upper_subset
    {X : Type u} [TopologicalSpace X]
    {I : Type v} [Nonempty I] (U : I → Set X)
    (hdir : Directed (fun A B : Set X => A ⊆ B) U)
    (s : Finset I) : ∃ j, ∀ i ∈ s, U i ⊆ U j := by
  classical
  let i0 : I := Classical.choice (inferInstance : Nonempty I)
  induction s using Finset.induction_on with
  | empty => exact ⟨i0, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨k, hik, hjk⟩ := hdir i j
      refine ⟨k, ?_⟩
      intro l hl
      simp only [Finset.mem_insert] at hl
      rcases hl with rfl | hl
      · exact hik
      · exact (hj l hl).trans hjk

def integralDirectedUnionInclusion
    {I : Type v} (U : I → Set X) (i : I) :
    C(U i, ⋃ j, U j) :=
  ⟨fun x => ⟨x.1, mem_iUnion.mpr ⟨i, x.2⟩⟩,
    continuous_subtype_val.subtype_mk (fun x => mem_iUnion.mpr ⟨i, x.property⟩)⟩

def integralDirectedUnionHomologyMap
    {I : Type v} (U : I → Set X) (i : I) (n : Nat) :
    integralHomology (U i) n ⟶ integralHomology (⋃ j, U j) n :=
  homologyMap (integralChainsFunctor.map
    (TopCat.ofHom (integralDirectedUnionInclusion U i))) n

theorem integralDirectedUnionHomologyMap_eq_nested
    {I : Type v} (U : I → Set X) (i : I) (n : Nat) :
    integralDirectedUnionHomologyMap U i n =
      homologyMap (integralNestedChains (show U i ⊆ ⋃ j, U j from
        fun x hx => show x ∈ ⋃ j, U j from mem_iUnion.mpr ⟨i, hx⟩)) n := by
  change homologyMap (integralChainsFunctor.map
      (integralNestedInclusion (show U i ⊆ ⋃ j, U j from
        fun x hx => mem_iUnion.mpr ⟨i, hx⟩))) n = _
  rfl

theorem exists_integralHomology_directed_union_stage
    {I : Type v} [Nonempty I] (U : I → Set X)
    (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (fun A B : Set X => A ⊆ B) U)
    (n : Nat) (a : integralHomology (⋃ i, U i) n) :
    ∃ i, ∃ b : integralHomology (U i) n,
      integralDirectedUnionHomologyMap U i n b = a := by
  let B : Set X := ⋃ i, U i
  let W : I → Set B := fun i => (Subtype.val : B → X) ⁻¹' U i
  have hW : ∀ i, IsOpen (W i) := by
    intro i
    exact (hU i).preimage continuous_subtype_val
  have hWcover : (⋃ i, W i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨z, hz⟩ :=
    (ModuleCat.epi_iff_surjective ((integralChains B).homologyπ n)).mp inferInstance a
  let c := (integralChains B).iCycles n z
  obtain ⟨k, hk⟩ := integral_subdivision_eventually_small W hW hWcover n c
  let S := integralSubdivisionIterate B k
  let c' := S.f n c
  have hcsmall : c' ∈ integralSmallChains W n := by
    exact hk
  have hsmall := integralSmallChains_support W n hcsmall
  classical
  let T := (integralChainCoordinates B n c').support
  choose i hi using fun s : T => hsmall s.1 s.2
  let inds : Finset I := T.attach.image i
  obtain ⟨j, hj⟩ := exists_finset_upper_subset U hdir inds
  have hcj : ∀ s ∈ (integralChainCoordinates B n c').support,
      Set.range ((⟨Subtype.val, continuous_subtype_val⟩ : C(B, X)).comp s) ⊆ U j := by
    intro s hs
    let q : T := ⟨s, hs⟩
    have hq : U (i q) ⊆ U j := hj (i q) (by
      change i q ∈ T.attach.image i
      exact Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩)
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact hq (hi q ⟨z, rfl⟩)
  obtain ⟨d, hd⟩ := integralNestedChains_preimage_of_support
    (show U j ⊆ B from fun x hx => mem_iUnion.mpr ⟨j, hx⟩) n c' hcj
  have hdc : (integralChains B).d n ((ComplexShape.down Nat).next n) c' = 0 := by
    have hcycle := congrArg (fun f => f c)
      (S.comm n ((ComplexShape.down Nat).next n))
    have hc0 : (integralChains B).d n ((ComplexShape.down Nat).next n) c = 0 := by
      exact congrArg (fun f => f z)
        ((integralChains B).iCycles_d n ((ComplexShape.down Nat).next n))
    change (integralChains B).d n ((ComplexShape.down Nat).next n) (S.f n c) =
      S.f ((ComplexShape.down Nat).next n)
        ((integralChains B).d n ((ComplexShape.down Nat).next n) c) at hcycle
    rw [hc0, map_zero] at hcycle
    exact hcycle
  have hdd : (integralChains (U j)).d n ((ComplexShape.down Nat).next n) d = 0 := by
    let hJB : U j ⊆ B := fun x hx => mem_iUnion.mpr ⟨j, hx⟩
    apply integralNestedChains_injective hJB ((ComplexShape.down Nat).next n)
    have hcomm := congrArg (fun q => q d)
      ((integralNestedChains hJB).comm n ((ComplexShape.down Nat).next n))
    change (integralChains B).d n ((ComplexShape.down Nat).next n)
      ((integralNestedChains hJB).f n d) =
      (integralNestedChains hJB).f ((ComplexShape.down Nat).next n)
      ((integralChains (U j)).d n ((ComplexShape.down Nat).next n) d) at hcomm
    rw [hd, hdc] at hcomm
    rw [map_zero]
    exact hcomm.symm
  let zj : (integralChains (U j)).cycles n :=
    (integralChains (U j)).sc n |>.cyclesMk d (by
      change (integralChains (U j)).d n ((ComplexShape.down Nat).next n) d = 0
      simpa only [ChainComplex.next] using hdd)
  let hJB : U j ⊆ B := fun x hx => mem_iUnion.mpr ⟨j, hx⟩
  let zj' : (integralChains B).cycles n :=
    HomologicalComplex.cyclesMap (integralNestedChains hJB) n zj
  have hzj : (integralChains B).homologyπ n zj' =
      (integralDirectedUnionHomologyMap U j n)
        ((integralChains (U j)).homologyπ n zj) := by
    exact (congrArg (fun f => f zj)
      (HomologicalComplex.homologyπ_naturality
        (φ := integralNestedChains hJB) (i := n))).symm
  have hzjmap : zj' = HomologicalComplex.cyclesMap S n z := by
    apply (ModuleCat.mono_iff_injective ((integralChains B).iCycles n)).mp inferInstance
    have hjval : (integralChains (U j)).iCycles n zj = d :=
      ((integralChains (U j)).sc n).i_cyclesMk d _
    have hi := congrArg (fun q => q zj)
      (HomologicalComplex.cyclesMap_i (integralNestedChains hJB) n)
    have hSval := congrArg (fun q => q z)
      (HomologicalComplex.cyclesMap_i S n)
    change (integralChains B).iCycles n zj' =
      (integralNestedChains hJB).f n ((integralChains (U j)).iCycles n zj) at hi
    rw [hjval, hd] at hi
    exact hi.trans hSval.symm
  have hS : HomologicalComplex.homologyMap S n = 𝟙 _ := by
    simpa only [HomologicalComplex.homologyMap_id] using
      (integralIteratedSubdivisionPrism B k).homologyMap_eq n |>.symm
  have hsub : (integralChains B).homologyπ n
      ((integralChains B).cyclesMap S n z) =
      (integralChains B).homologyπ n z := by
    have he := congrArg (fun f => f z)
      (HomologicalComplex.homologyπ_naturality (φ := S) (i := n))
    rw [hS] at he
    exact he.symm
  have hclass : (integralChains B).homologyπ n zj' = a := by
    rw [hzjmap, hsub]
    exact hz
  refine ⟨j, (integralChains (U j)).homologyπ n zj, ?_⟩
  exact hzj.symm.trans hclass

theorem integralHomology_homologyπ_eq_zero_iff
    (K : ChainComplex (ModuleCat.{u} Int) Nat) (n : Nat) (z : K.cycles n) :
    K.homologyπ n z = 0 ↔
      ∃ b : K.X (n + 1), K.d (n + 1) n b = K.iCycles n z := by
  let T := ShortComplex.mk (K.toCycles (n + 1) n) (K.homologyπ n)
    (K.toCycles_comp_homologyπ (n + 1) n)
  have hT : T.Exact := T.exact_of_g_is_cokernel
    (K.homologyIsCokernel (n + 1) n (by simp))
  constructor
  · intro hz
    obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff T).mp hT z hz
    refine ⟨b, ?_⟩
    have he := congrArg (K.iCycles n) hb
    simpa only [T, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i] using he
  · rintro ⟨b, hb⟩
    have hb' : K.toCycles (n + 1) n b = z := by
      apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
      simpa only [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i] using hb
    rw [← hb']
    exact congrArg (fun q => q b) (K.toCycles_comp_homologyπ (n + 1) n)

theorem exists_integralHomology_ambient_directed_union_stage
    {I : Type v} [Nonempty I] (U : I → Set X)
    (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ)
    (hdir : Directed (fun A B : Set X => A ⊆ B) U)
    (n : Nat) (a : integralHomology X n) :
    ∃ i, ∃ b : integralHomology (U i) n,
      homologyMap (integralSubspaceChains (U i)) n b = a := by
  obtain ⟨z, hz⟩ :=
    (ModuleCat.epi_iff_surjective ((integralChains X).homologyπ n)).mp inferInstance a
  let c := (integralChains X).iCycles n z
  obtain ⟨k, hk⟩ := integral_subdivision_eventually_small U hU hcover n c
  let S := integralSubdivisionIterate X k
  let c' := S.f n c
  have hcsmall : c' ∈ integralSmallChains U n := by
    exact hk
  have hsmall := integralSmallChains_support U n hcsmall
  classical
  let T := (integralChainCoordinates X n c').support
  choose i hi using fun s : T => hsmall s.1 s.2
  let inds : Finset I := T.attach.image i
  obtain ⟨j, hj⟩ := exists_finset_upper_subset U hdir inds
  have hcj : ∀ s ∈ (integralChainCoordinates X n c').support,
      Set.range s ⊆ U j := by
    intro s hs
    let q : T := ⟨s, hs⟩
    have hq : U (i q) ⊆ U j := hj (i q) (by
      change i q ∈ T.attach.image i
      exact Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩)
    intro y hy
    exact hq (hi q hy)
  obtain ⟨d, hd⟩ := (integral_subspace_range_iff (U j) n c').mpr hcj
  have hdc : (integralChains X).d n ((ComplexShape.down Nat).next n) c' = 0 := by
    have hcycle := congrArg (fun f => f c)
      (S.comm n ((ComplexShape.down Nat).next n))
    have hc0 : (integralChains X).d n ((ComplexShape.down Nat).next n) c = 0 :=
      congrArg (fun f => f z)
        ((integralChains X).iCycles_d n ((ComplexShape.down Nat).next n))
    change (integralChains X).d n ((ComplexShape.down Nat).next n) (S.f n c) =
      S.f ((ComplexShape.down Nat).next n)
        ((integralChains X).d n ((ComplexShape.down Nat).next n) c) at hcycle
    rw [hc0, map_zero] at hcycle
    exact hcycle
  have hdd : (integralChains (U j)).d n ((ComplexShape.down Nat).next n) d = 0 := by
    let := integralSubspaceChains_mono (U j)
    apply (ModuleCat.mono_iff_injective
      ((integralSubspaceChains (U j)).f ((ComplexShape.down Nat).next n))).mp inferInstance
    have hcomm := congrArg (fun q => q d)
      ((integralSubspaceChains (U j)).comm n ((ComplexShape.down Nat).next n))
    change (integralChains X).d n ((ComplexShape.down Nat).next n)
        ((integralSubspaceChains (U j)).f n d) =
      (integralSubspaceChains (U j)).f ((ComplexShape.down Nat).next n)
        ((integralChains (U j)).d n ((ComplexShape.down Nat).next n) d) at hcomm
    rw [hd, hdc] at hcomm
    rw [map_zero]
    exact hcomm.symm
  let zj : (integralChains (U j)).cycles n :=
    (integralChains (U j)).sc n |>.cyclesMk d hdd
  have hzj : (integralChains X).homologyπ n
      (HomologicalComplex.cyclesMap (integralSubspaceChains (U j)) n zj) =
      homologyMap (integralSubspaceChains (U j)) n
        ((integralChains (U j)).homologyπ n zj) := by
    exact (congrArg (fun f => f zj)
      (HomologicalComplex.homologyπ_naturality
        (φ := integralSubspaceChains (U j)) (i := n))).symm
  have hzjmap : HomologicalComplex.cyclesMap (integralSubspaceChains (U j)) n zj =
      HomologicalComplex.cyclesMap S n z := by
    apply (ModuleCat.mono_iff_injective ((integralChains X).iCycles n)).mp inferInstance
    have hjval : (integralChains (U j)).iCycles n zj = d :=
      ((integralChains (U j)).sc n).i_cyclesMk d hdd
    have hi := congrArg (fun q => q zj)
      (HomologicalComplex.cyclesMap_i (integralSubspaceChains (U j)) n)
    have hSval := congrArg (fun q => q z)
      (HomologicalComplex.cyclesMap_i S n)
    change (integralChains X).iCycles n
        (HomologicalComplex.cyclesMap (integralSubspaceChains (U j)) n zj) =
      (integralSubspaceChains (U j)).f n
        ((integralChains (U j)).iCycles n zj) at hi
    rw [hjval, hd] at hi
    exact hi.trans hSval.symm
  have hS : HomologicalComplex.homologyMap S n = 𝟙 _ := by
    simpa only [HomologicalComplex.homologyMap_id] using
      (integralIteratedSubdivisionPrism X k).homologyMap_eq n |>.symm
  have hsub : (integralChains X).homologyπ n
      (HomologicalComplex.cyclesMap S n z) =
      (integralChains X).homologyπ n z := by
    have he := congrArg (fun f => f z)
      (HomologicalComplex.homologyπ_naturality (φ := S) (i := n))
    rw [hS] at he
    exact he.symm
  have hclass : (integralChains X).homologyπ n
      (HomologicalComplex.cyclesMap (integralSubspaceChains (U j)) n zj) = a := by
    rw [hzjmap, hsub]
    exact hz
  refine ⟨j, (integralChains (U j)).homologyπ n zj, ?_⟩
  exact hzj.symm.trans hclass

theorem integralHomology_eventually_zero_of_ambient_zero
    {I : Type v} [Nonempty I] (U : I → Set X)
    (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ)
    (hdir : Directed (fun A B : Set X => A ⊆ B) U)
    (i : I) (n : Nat) (b : integralHomology (U i) n)
    (hb : homologyMap (integralSubspaceChains (U i)) n b = 0) :
    ∃ (j : I) (hij : U i ⊆ U j),
      homologyMap (integralNestedChains hij) n b = 0 := by
  obtain ⟨z, hz⟩ :=
    (ModuleCat.epi_iff_surjective ((integralChains (U i)).homologyπ n)).mp inferInstance b
  let F : integralChains (U i) ⟶ integralChains X := integralSubspaceChains (U i)
  have hzero : (integralChains X).homologyπ n
      (HomologicalComplex.cyclesMap F n z) = 0 := by
    have he := congrArg (fun f => f z)
      (HomologicalComplex.homologyπ_naturality (φ := F) (i := n))
    change homologyMap F n ((integralChains (U i)).homologyπ n z) =
      (integralChains X).homologyπ n (HomologicalComplex.cyclesMap F n z) at he
    rw [hz, hb] at he
    exact he.symm
  obtain ⟨e, he⟩ :=
    (integralHomology_homologyπ_eq_zero_iff (integralChains X) n
      (HomologicalComplex.cyclesMap F n z)).mp hzero
  have hemap : (integralChains X).d (n + 1) n e =
      F.f n ((integralChains (U i)).iCycles n z) := by
    have hi := congrArg (fun f => f z)
      (HomologicalComplex.cyclesMap_i F n)
    change (integralChains X).iCycles n (HomologicalComplex.cyclesMap F n z) =
      F.f n ((integralChains (U i)).iCycles n z) at hi
    exact he.trans hi
  classical
  let E := (integralChainCoordinates X (n + 1) e).support
  let K : Set X := ⋃ s ∈ E, Set.range s
  have hKcompact : IsCompact K := by
    exact E.isCompact_biUnion (fun s _ => isCompact_range s.continuous)
  have hKcover : K ⊆ ⋃ k, U k := by
    intro x hx
    rw [hcover]
    exact Set.mem_univ x
  obtain ⟨j₀, hj₀⟩ := hKcompact.elim_directed_cover U hU hKcover hdir
  obtain ⟨j, hij, hj₀j⟩ := hdir i j₀
  have hKj : K ⊆ U j := hj₀.trans hj₀j
  have hErange : ∀ s ∈ (integralChainCoordinates X (n + 1) e).support,
      Set.range s ⊆ U j := by
    intro s hs y hy
    exact hKj (Set.mem_iUnion₂.mpr ⟨s, hs, hy⟩)
  obtain ⟨e', he'⟩ :=
    (integral_subspace_range_iff (U j) (n + 1) e).mpr hErange
  have hstage : (integralChains (U j)).d (n + 1) n e' =
      (integralNestedChains hij).f n
        ((integralChains (U i)).iCycles n z) := by
    let := integralSubspaceChains_mono (U j)
    apply (ModuleCat.mono_iff_injective
      ((integralSubspaceChains (U j)).f n)).mp inferInstance
    have hcomm := congrArg (fun q => q e')
      ((integralSubspaceChains (U j)).comm (n + 1) n)
    change (integralChains X).d (n + 1) n
        ((integralSubspaceChains (U j)).f (n + 1) e') =
      (integralSubspaceChains (U j)).f n
        ((integralChains (U j)).d (n + 1) n e') at hcomm
    have hcomp := congrArg (fun f => f.f n)
      (integralNestedChains_subspaceChains hij)
    have hcomp' := congrArg (fun q => q ((integralChains (U i)).iCycles n z)) hcomp
    change (integralSubspaceChains (U j)).f n
        ((integralNestedChains hij).f n
          ((integralChains (U i)).iCycles n z)) =
      (integralSubspaceChains (U i)).f n
        ((integralChains (U i)).iCycles n z) at hcomp'
    rw [he', hemap] at hcomm
    exact hcomm.symm.trans hcomp'.symm
  let zj : (integralChains (U j)).cycles n :=
    HomologicalComplex.cyclesMap (integralNestedChains hij) n z
  have hzj_i : (integralChains (U j)).iCycles n zj =
      (integralNestedChains hij).f n ((integralChains (U i)).iCycles n z) := by
    exact congrArg (fun q => q z)
      (HomologicalComplex.cyclesMap_i (integralNestedChains hij) n)
  have hzeroj : (integralChains (U j)).homologyπ n zj = 0 := by
    apply (integralHomology_homologyπ_eq_zero_iff (integralChains (U j)) n zj).mpr
    exact ⟨e', hstage.trans hzj_i.symm⟩
  have hmap : homologyMap (integralNestedChains hij) n b =
      (integralChains (U j)).homologyπ n zj := by
    have he := congrArg (fun f => f z)
      (HomologicalComplex.homologyπ_naturality
        (φ := integralNestedChains hij) (i := n))
    change homologyMap (integralNestedChains hij) n
        ((integralChains (U i)).homologyπ n z) =
      (integralChains (U j)).homologyπ n zj at he
    rw [← hz]
    exact he
  refine ⟨j, hij, ?_⟩
  rw [hmap, hzeroj]

end Poincare.Topology
