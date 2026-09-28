import PoincareConjecture.Proofs.M02.Topology.IntegralSupportUniv
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactGluing
import Mathlib.Topology.Compactness.LocallyCompact










set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable {X : Type u} [TopologicalSpace X]



theorem integralDisjointToRelativeHomology_mono
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (n : Nat) (hzero : IsZero (integralRelativeHomology (V ∪ U) (n + 1))) :
    Mono (homologyMap (integralSubspaceChains U ≫ integralRelativeProjection V) n) := by
  have hempty : (Subtype.val : U → X) ⁻¹' V = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact Set.disjoint_left.mp hUV x.property hx
  let : IsIso (integralRelativeProjection ((Subtype.val : U → X) ⁻¹' V)) := by
    rw [hempty]
    exact integralRelativeProjection_empty_isIso
  let := integralSumComparison_homology_isIso V U hV hU (n + 1)
  have hQ : IsZero ((integralSumQuotient V U).homology (n + 1)) :=
    hzero.of_iso (asIso (homologyMap (integralSumComparison V U) (n + 1)))
  have hS : (ShortComplex.cokernelSequence (integralPairInclusion V U)).ShortExact := {
    exact := ShortComplex.cokernelSequence_exact _
    mono_f := integralPairInclusion_mono V U }
  let : Mono (homologyMap (integralPairInclusion V U) n) :=
    (hS.homology_exact₁ (n + 1) n rfl).mono_g (hQ.eq_zero_of_src _)
  rw [← integralPairInclusion_projection, homologyMap_comp]
  infer_instance



theorem exists_integralSubspaceHomology_lift (U : Set X) (n : Nat)
    (z : (integralChains X).cycles n)
    (hz : (integralChains X).iCycles n z ∈
      LinearMap.range ((integralSubspaceChains U).f n).hom) :
    ∃ b : integralHomology U n,
      homologyMap (integralSubspaceChains U) n b = (integralChains X).homologyπ n z := by
  let C := integralChains X
  let D := integralChains U
  let f := integralSubspaceChains U
  obtain ⟨c, hc⟩ := hz
  let : Mono f := integralSubspaceChains_mono U
  have hd : (D.sc n).g c = 0 := by
    apply (ModuleCat.mono_iff_injective (f.f ((ComplexShape.down Nat).next n))).mp
      inferInstance
    change (f.f _).hom ((D.d n _).hom c) = (f.f _).hom 0
    rw [map_zero]
    change f.f _ (D.d n _ c) = 0
    rw [← ConcreteCategory.comp_apply, ← f.comm, ConcreteCategory.comp_apply]
    rw [hc]
    exact congrArg (fun k => k.hom z) (C.iCycles_d n ((ComplexShape.down Nat).next n))
  let w : D.cycles n := (D.sc n).moduleCatCyclesIso.inv ⟨c, hd⟩
  have hw : D.iCycles n w = c :=
    congrArg (fun k => k ⟨c, hd⟩) (D.sc n).moduleCatCyclesIso_inv_iCycles
  have hcycles : cyclesMap f n w = z := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply, hw]
    exact hc
  refine ⟨D.homologyπ n w, ?_⟩
  rw [← ConcreteCategory.comp_apply, homologyπ_naturality, ConcreteCategory.comp_apply,
    hcycles]



theorem exists_integralHomology_compact_open_lift [T2Space X] [LocallyCompactSpace X]
    (n : Nat) (a : integralHomology X n) :
    ∃ U : Set X, IsOpen U ∧ IsCompact (closure U) ∧
      ∃ b : integralHomology U n, homologyMap (integralSubspaceChains U) n b = a := by
  classical
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective ((integralChains X).homologyπ n)).mp
    inferInstance a
  let c := (integralChains X).iCycles n z
  let F := (integralChainCoordinates X n c).support
  let K : Set X := ⋃ s ∈ F, Set.range s
  have hK : IsCompact K := F.isCompact_biUnion (fun s _ => isCompact_range s.continuous)
  obtain ⟨L, hL, hKL, _⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  have hclosure : IsCompact (closure (interior L)) :=
    hL.of_isClosed_subset isClosed_closure (closure_minimal interior_subset hL.isClosed)
  have hc : c ∈ LinearMap.range ((integralSubspaceChains (interior L)).f n).hom := by
    apply (integral_subspace_range_iff (interior L) n c).mpr
    intro s hs x hx
    exact hKL (mem_iUnion₂.mpr ⟨s, hs, hx⟩)
  obtain ⟨b, hb⟩ := exists_integralSubspaceHomology_lift (interior L) n z hc
  exact ⟨interior L, isOpen_interior, hclosure, b, hb.trans hz⟩



theorem integralToRelativeHomology_restriction {A B : Set X} (hAB : A ⊆ B)
    (n : Nat) (a : integralHomology X n) :
    homologyMap (integralRelativeRestriction hAB) n (integralToRelativeHomology A n a) =
      integralToRelativeHomology B n a := by
  rw [← ConcreteCategory.comp_apply, ← homologyMap_comp,
    integralRelativeRestriction_projection]



theorem integralHomology_eq_zero_of_point_restrictions [T2Space X] [LocallyCompactSpace X]
    (n : Nat)
    (hupper : ∀ K : Set X, IsCompact K → IsZero (integralSupportHomology K (n + 1)))
    (hdet : ∀ K : Set X, IsCompact K → IntegralSupportDetected K n)
    (a : integralHomology X n)
    (ha : ∀ x : X, integralToRelativeHomology ({x}ᶜ : Set X) n a = 0) : a = 0 := by
  obtain ⟨U, hU, hclosure, b, hb⟩ := exists_integralHomology_compact_open_lift n a
  let V := (closure U)ᶜ
  have hV : IsOpen V := isClosed_closure.isOpen_compl
  have hUV : Disjoint U V := Set.disjoint_left.mpr fun _ hx hy => hy (subset_closure hx)
  have hcompact : IsCompact (V ∪ U)ᶜ :=
    hclosure.of_isClosed_subset (hV.union hU).isClosed_compl (by
      intro x hx
      by_contra h
      exact hx (Or.inl h))
  have hzero : IsZero (integralRelativeHomology (V ∪ U) (n + 1)) := by
    simpa only [integralSupportHomology, compl_compl] using hupper (V ∪ U)ᶜ hcompact
  let := integralDisjointToRelativeHomology_mono U V hU hV hUV n hzero
  have hrelative : integralToRelativeHomology V n a = 0 := by
    apply hdet (closure U) hclosure
    intro x hx
    exact (integralToRelativeHomology_restriction
      (compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) n a).trans (ha x)
  have hbzero : b = 0 := by
    apply (ModuleCat.mono_iff_injective
      (homologyMap (integralSubspaceChains U ≫ integralRelativeProjection V) n)).mp
      inferInstance
    rw [map_zero, homologyMap_comp, ConcreteCategory.comp_apply, hb]
    exact hrelative
  rw [← hb, hbzero, map_zero]



theorem exists_integralHomology_point_restriction_zero
    (hnoncompact : ¬IsCompact (univ : Set X)) (n : Nat) (a : integralHomology X n) :
    ∃ x : X, integralToRelativeHomology ({x}ᶜ : Set X) n a = 0 := by
  classical
  let C := integralChains X
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance a
  let c := C.iCycles n z
  let F := (integralChainCoordinates X n c).support
  let K : Set X := ⋃ s ∈ F, Set.range s
  have hK : IsCompact K := F.isCompact_biUnion (fun s _ => isCompact_range s.continuous)
  have hproper : K ≠ univ := fun h => hnoncompact (h ▸ hK)
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem K).mp hproper
  let P := integralRelativeProjection ({x}ᶜ : Set X)
  have hc : P.f n c = 0 := by
    apply (integralProjection_eq_zero_iff (integralSubspaceChains ({x}ᶜ : Set X)) n c).mpr
    apply (integral_subspace_range_iff ({x}ᶜ : Set X) n c).mpr
    intro s hs y hy hyx
    exact hx (hyx ▸ mem_iUnion₂.mpr ⟨s, hs, hy⟩)
  have hcycles : cyclesMap P n z = 0 := by
    apply (ModuleCat.mono_iff_injective ((integralRelativeChains ({x}ᶜ : Set X)).iCycles n)).mp
      inferInstance
    rw [map_zero, ← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply]
    exact hc
  refine ⟨x, ?_⟩
  rw [← hz]
  change homologyMap P n (C.homologyπ n z) = 0
  rw [← ConcreteCategory.comp_apply, homologyπ_naturality, ConcreteCategory.comp_apply,
    hcycles, map_zero]

end PoincareConjecture.Proofs.M59
