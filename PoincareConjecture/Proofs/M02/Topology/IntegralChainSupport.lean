import PoincareConjecture.Proofs.M02.Topology.IntegralSmallChains

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped BigOperators

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {I : Type v}

theorem integralChainCoordinates_map (f : C(X, Y)) (n : Nat)
    (c : (integralChains X).X n) :
    integralChainCoordinates Y n ((integralChainsFunctor.map (TopCat.ofHom f)).f n c) =
      Finsupp.mapDomain (fun s => f.comp s) (integralChainCoordinates X n c) := by
  let EX := integralChainCoordinates X n
  let EY := integralChainCoordinates Y n
  let q := (integralChainsFunctor.map (TopCat.ofHom f)).f n
  have he : EY.toLinearMap.comp (q.hom.comp EX.symm.toLinearMap) =
      Finsupp.lmapDomain (ULift.{u} Int) Int (fun s => f.comp s) := by
    apply Finsupp.lhom_ext
    intro s a
    have hs : EX.symm (Finsupp.single s a) = integralSingularGenerator s a := by
      apply EX.injective
      rw [EX.apply_symm_apply]
      exact (integralChainCoordinates_generator s a).symm
    change EY (q (EX.symm (Finsupp.single s a))) =
      Finsupp.mapDomain (fun s => f.comp s) (Finsupp.single s a)
    rw [hs]
    have hq : q (integralSingularGenerator s a) = integralSingularGenerator (f.comp s) a :=
      congrArg (fun k => k a) (integralSingularGenerator_map s f)
    rw [hq, integralChainCoordinates_generator, Finsupp.mapDomain_single]
  have hec := LinearMap.congr_fun he (EX c)
  change EY (q (EX.symm (EX c))) = Finsupp.mapDomain (fun s => f.comp s) (EX c) at hec
  simpa only [EX.symm_apply_apply] using hec

theorem integralSingularGenerator_mem_small (U : I → Set X) {n : Nat}
    (s : C(integralSimplex n, X)) (hs : IntegralSmallSimplex U s)
    (a : ULift.{u} Int) : integralSingularGenerator s a ∈ integralSmallChains U n := by
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  rw [ha, map_zsmul]
  apply (integralSmallChains U n).toAddSubgroup.zsmul_mem
  exact Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩

theorem integralSmallChains_of_support (U : I → Set X) (n : Nat)
    (c : (integralChains X).X n)
    (hc : ∀ s ∈ (integralChainCoordinates X n c).support, IntegralSmallSimplex U s) :
    c ∈ integralSmallChains U n := by
  rw [integral_chain_finite_representation n c]
  apply Submodule.sum_mem
  intro s hs
  exact integralSingularGenerator_mem_small U s (hc s hs) _

theorem integralSmallChains_eq_top_of_univ (U : I → Set X) (i : I)
    (hi : U i = Set.univ) (n : Nat) : integralSmallChains U n = ⊤ := by
  apply top_unique
  intro c _
  apply integralSmallChains_of_support U n c
  intro s _
  exact ⟨i, by rw [hi]; exact Set.subset_univ _⟩

theorem integralSmallChainInclusion_isIso_of_univ (U : I → Set X) (i : I)
    (hi : U i = Set.univ) : IsIso (integralSmallChainInclusion U) := by
  have hdeg (n : Nat) : IsIso ((integralSmallChainInclusion U).f n) := by
    let : Mono ((integralSmallChainInclusion U).f n) :=
      (ModuleCat.mono_iff_injective _).mpr (fun _ _ h => Subtype.ext h)
    let : Epi ((integralSmallChainInclusion U).f n) :=
      (ModuleCat.epi_iff_surjective _).mpr (by
        intro c
        refine ⟨⟨c, ?_⟩, rfl⟩
        rw [integralSmallChains_eq_top_of_univ U i hi n]
        exact Submodule.mem_top)
    exact isIso_of_mono_of_epi _
  let := hdeg
  exact HomologicalComplex.Hom.isIso_of_components _

theorem integralSubspaceChains_range_le_small (U : I → Set X) (A : Set X)
    (i : I) (hi : A ⊆ U i) (n : Nat) :
    LinearMap.range ((integralSubspaceChains A).f n).hom ≤ integralSmallChains U n := by
  rintro _ ⟨c, rfl⟩
  apply integralSmallChains_of_support
  intro s hs
  let v : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hcoord := integralChainCoordinates_map v n c
  change integralChainCoordinates X n ((integralSubspaceChains A).f n c) = _ at hcoord
  rw [hcoord] at hs
  obtain ⟨t, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero (Finsupp.mem_support_iff.mp hs)
  refine ⟨i, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact hi (t z).property

theorem integralSingularGenerator_mem_subspace (A : Set X) {n : Nat}
    (s : C(integralSimplex n, X)) (hs : Set.range s ⊆ A) (a : ULift.{u} Int) :
    integralSingularGenerator s a ∈ LinearMap.range ((integralSubspaceChains A).f n).hom := by
  classical
  apply (integral_subspace_range_iff A n _).mpr
  rw [integralChainCoordinates_generator]
  intro t ht
  have hts : t = s := by
    by_contra hne
    exact (Finsupp.mem_support_iff.mp ht) (Finsupp.single_eq_of_ne hne)
  exact hts ▸ hs

theorem integralSubspaceChains_range_inf (A B : Set X) (n : Nat) :
    LinearMap.range ((integralSubspaceChains A).f n).hom ⊓
        LinearMap.range ((integralSubspaceChains B).f n).hom =
      LinearMap.range ((integralSubspaceChains (A ∩ B)).f n).hom := by
  ext c
  simp only [Submodule.mem_inf, integral_subspace_range_iff]
  constructor
  · rintro ⟨hA, hB⟩ s hs x hx
    exact ⟨hA s hs hx, hB s hs hx⟩
  · intro h
    exact ⟨fun s hs x hx => (h s hs hx).1, fun s hs x hx => (h s hs hx).2⟩

theorem integralSubspaceChains_range_preimage (A B : Set X) (n : Nat)
    (c : (integralChains B).X n) :
    (integralSubspaceChains B).f n c ∈ LinearMap.range ((integralSubspaceChains A).f n).hom ↔
      c ∈ LinearMap.range
        ((integralSubspaceChains ((Subtype.val : B → X) ⁻¹' A)).f n).hom := by
  let v : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let g : C(integralSimplex n, B) → C(integralSimplex n, X) := fun s => v.comp s
  have hg : Function.Injective g := by
    intro s t h
    ext z
    exact congrArg (fun q : C(integralSimplex n, X) => q z) h
  rw [integral_subspace_range_iff, integral_subspace_range_iff]
  have hcoord := integralChainCoordinates_map v n c
  change integralChainCoordinates X n ((integralSubspaceChains B).f n c) =
    Finsupp.mapDomain g (integralChainCoordinates B n c) at hcoord
  rw [hcoord]
  constructor
  · intro h s hs x hx
    have hmem : g s ∈ (Finsupp.mapDomain g (integralChainCoordinates B n c)).support := by
      rw [Finsupp.mem_support_iff, Finsupp.mapDomain_apply hg]
      exact Finsupp.mem_support_iff.mp hs
    obtain ⟨z, rfl⟩ := hx
    exact h (g s) hmem ⟨z, rfl⟩
  · intro h s hs x hx
    obtain ⟨t, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero (Finsupp.mem_support_iff.mp hs)
    have ht : t ∈ (integralChainCoordinates B n c).support := by
      rw [Finsupp.mem_support_iff, Finsupp.mapDomain_apply hg] at hs
      exact Finsupp.mem_support_iff.mpr hs
    obtain ⟨z, rfl⟩ := hx
    exact h t ht ⟨z, rfl⟩

theorem integralSmallChains_two_eq_sup (A B : Set X) (n : Nat) :
    integralSmallChains (fun b : Bool => if b then A else B) n =
      LinearMap.range ((integralSubspaceChains A).f n).hom ⊔
        LinearMap.range ((integralSubspaceChains B).f n).hom := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    obtain ⟨b, hb⟩ := s.property
    cases b with
    | false =>
        exact Submodule.mem_sup_right (integralSingularGenerator_mem_subspace B s.val hb _)
    | true =>
        exact Submodule.mem_sup_left (integralSingularGenerator_mem_subspace A s.val hb _)
  · apply sup_le
    · exact integralSubspaceChains_range_le_small _ A true (fun _ h => h) n
    · exact integralSubspaceChains_range_le_small _ B false (fun _ h => h) n

end PoincareConjecture.Proofs.M02.Topology
