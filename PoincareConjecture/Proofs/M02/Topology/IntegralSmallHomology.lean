import PoincareConjecture.Proofs.M02.Topology.IntegralSubdivision
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

private theorem integralHomologyπ_eq_zero_iff
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

private theorem integralSmall_boundary
    {X : Type u} [TopologicalSpace X] {I : Type v}
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (n : Nat)
    (c : (integralChains X).X n)
    (hc : (integralChains X).d n (n - 1) c = 0)
    (hsmall : c ∈ integralSmallChains U n)
    (b : (integralChains X).X (n + 1))
    (hb : (integralChains X).d (n + 1) n b = c) :
    ∃ b' : (integralChains X).X (n + 1),
      b' ∈ integralSmallChains U (n + 1) ∧
      (integralChains X).d (n + 1) n b' = c := by
  obtain ⟨k, hk⟩ := integral_subdivision_eventually_small U hU hcover (n + 1) b
  let K := integralChains X
  let S := integralSubdivisionIterate X k
  let H := integralIteratedSubdivisionPrism X k
  refine ⟨S.f (n + 1) b + H.hom n (n + 1) c,
    (integralSmallChains U (n + 1)).add_mem hk
      (integralIteratedSubdivisionPrism_small U k n (n + 1) c hsmall), ?_⟩
  have hbS : K.d (n + 1) n (S.f (n + 1) b) = S.f n c := by
    have he := congrArg (fun q => q b) (S.comm (n + 1) n)
    change K.d (n + 1) n (S.f (n + 1) b) = S.f n (K.d (n + 1) n b) at he
    rw [hb] at he
    exact he
  rw [map_add, hbS]
  have he := congrArg (fun q => q c) (H.comm n)
  rw [HomologicalComplex.id_f] at he
  cases n with
  | zero =>
      rw [dNext_eq_zero H.hom 0 (by simp),
        prevD_eq H.hom (show (ComplexShape.down Nat).Rel 1 0 from rfl)] at he
      change c = 0 + K.d 1 0 (H.hom 0 1 c) + S.f 0 c at he
      rw [zero_add] at he
      exact (add_comm _ _).trans he.symm
  | succ m =>
      rw [dNext_eq H.hom (show (ComplexShape.down Nat).Rel (m + 1) m from rfl),
        prevD_eq H.hom (show (ComplexShape.down Nat).Rel (m + 2) (m + 1) from rfl)] at he
      change c = H.hom m (m + 1) (K.d (m + 1) m c) +
        K.d (m + 2) (m + 1) (H.hom (m + 1) (m + 2) c) + S.f (m + 1) c at he
      have hc' : K.d (m + 1) m c = 0 := by simpa using hc
      rw [hc', map_zero, zero_add] at he
      exact (add_comm _ _).trans he.symm

variable {X : Type u} [TopologicalSpace X] {I : Type v}

theorem integralSmallChainInclusion_homology_isIso
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap (integralSmallChainInclusion U) n) := by
  let K := integralChains X
  let L := integralSmallChainComplex U
  let f := integralSmallChainInclusion U
  have hi (z : L.cycles n) :
      K.iCycles n (HomologicalComplex.cyclesMap f n z) =
        f.f n (L.iCycles n z) := by
    exact congrArg (fun q => q z) (HomologicalComplex.cyclesMap_i f n)
  have hπ (z : L.cycles n) :
      K.homologyπ n (HomologicalComplex.cyclesMap f n z) =
        HomologicalComplex.homologyMap f n (L.homologyπ n z) := by
    exact (congrArg (fun q => q z)
      (HomologicalComplex.homologyπ_naturality (φ := f) (i := n))).symm
  have hinj : Function.Injective (HomologicalComplex.homologyMap f n) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro y hy
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (L.homologyπ n)).mp inferInstance y
    have hz0 : K.homologyπ n (HomologicalComplex.cyclesMap f n z) = 0 := by
      rw [hπ, hz, hy]
    obtain ⟨b, hb⟩ := (integralHomologyπ_eq_zero_iff K n _).mp hz0
    rw [hi] at hb
    let c := L.iCycles n z
    have hc : K.d n (n - 1) (f.f n c) = 0 := by
      have he := congrArg (fun q => q c) (f.comm n (n - 1))
      change K.d n (n - 1) (f.f n c) = f.f (n - 1) (L.d n (n - 1) c) at he
      have hcz : L.d n (n - 1) c = 0 :=
        congrArg (fun q => q z) (L.iCycles_d n (n - 1))
      rw [hcz, map_zero] at he
      exact he
    obtain ⟨b', hb'small, hb'⟩ := integralSmall_boundary U hU hcover n
      (f.f n c) hc c.property b hb
    have hzsmall : L.homologyπ n z = 0 := by
      apply (integralHomologyπ_eq_zero_iff L n z).mpr
      refine ⟨⟨b', hb'small⟩, ?_⟩
      apply Subtype.ext
      exact hb'
    exact hz.symm.trans hzsmall
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap f n) := by
    intro y
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance y
    obtain ⟨k, hk⟩ := integral_subdivision_eventually_small U hU hcover n (K.iCycles n z)
    let S := integralSubdivisionIterate X k
    let z' := HomologicalComplex.cyclesMap S n z
    have hi' : K.iCycles n z' = S.f n (K.iCycles n z) :=
      congrArg (fun q => q z) (HomologicalComplex.cyclesMap_i S n)
    let c : L.X n := ⟨K.iCycles n z', by rw [hi']; exact hk⟩
    have hc : (L.sc n).g c = 0 := by
      apply Subtype.ext
      exact congrArg (fun q => q z') (K.iCycles_d n ((ComplexShape.down Nat).next n))
    let w : L.cycles n := (L.sc n).cyclesMk c hc
    have hw : L.iCycles n w = c := (L.sc n).i_cyclesMk c hc
    have hwmap : HomologicalComplex.cyclesMap f n w = z' := by
      apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
      rw [hi, hw]
      rfl
    refine ⟨L.homologyπ n w, ?_⟩
    rw [← hπ, hwmap]
    have hS : HomologicalComplex.homologyMap S n = 𝟙 _ := by
      simpa only [HomologicalComplex.homologyMap_id] using
        (integralIteratedSubdivisionPrism X k).homologyMap_eq n |>.symm
    have he := congrArg (fun q => q z)
      (HomologicalComplex.homologyπ_naturality (φ := S) (i := n))
    rw [hS] at he
    exact he.symm.trans hz
  let : Mono (HomologicalComplex.homologyMap f n) :=
    (ModuleCat.mono_iff_injective _).mpr hinj
  let : Epi (HomologicalComplex.homologyMap f n) :=
    (ModuleCat.epi_iff_surjective _).mpr hsurj
  exact isIso_of_mono_of_epi _

theorem integralSmallChainInclusion_quasiIso
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) :
    QuasiIso (integralSmallChainInclusion U) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact integralSmallChainInclusion_homology_isIso U hU hcover n

end PoincareConjecture.Proofs.M02.Topology
