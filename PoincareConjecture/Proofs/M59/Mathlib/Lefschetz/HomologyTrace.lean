import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.ChainTrace
import Mathlib.Algebra.Homology.HomologySequence

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open scoped BigOperators

universe u v

namespace ChainComplex

variable {K : Type u} [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
  {C : ChainComplex (ModuleCat.{v} K) ℕ}

omit [IsDomain K] in

theorem moduleFinite_cycles [∀ i, Module.Finite K (C.X i)] (i : ℕ) :
    Module.Finite K (C.cycles i) :=
  Module.Finite.of_injective (C.iCycles i).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

theorem moduleFree_cycles [∀ i, Module.Free K (C.X i)]
    [∀ i, Module.Finite K (C.X i)] (i : ℕ) : Module.Free K (C.cycles i) := by
  let e := (C.sc i).moduleCatCyclesIso.toLinearEquiv
  let : Module.Free K (C.sc i).moduleCatLeftHomologyData.K :=
    inferInstanceAs (Module.Free K (LinearMap.ker (C.dFrom i).hom))
  exact Module.Free.of_equiv e.symm

omit [IsDomain K] in

theorem moduleFinite_homology [∀ i, Module.Finite K (C.X i)] (i : ℕ) :
    Module.Finite K (C.homology i) := by
  let := moduleFinite_cycles (C := C) i
  exact Module.Finite.of_surjective (C.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

theorem trace_chains_succ_sub_cycles
    [∀ i, Module.Free K (C.X i)] [∀ i, Module.Finite K (C.X i)]
    [∀ i, Module.Free K (C.homology i)] (f : C ⟶ C) (i : ℕ) :
    LinearMap.trace K (C.X (i + 1)) (f.f (i + 1)).hom -
        LinearMap.trace K (C.cycles i) (cyclesMap f i).hom =
      LinearMap.trace K (C.cycles (i + 1)) (cyclesMap f (i + 1)).hom -
        LinearMap.trace K (C.homology i) (homologyMap f i).hom := by
  let cycF (j : ℕ) := moduleFree_cycles (C := C) j
  let cycFD (j : ℕ) := moduleFinite_cycles (C := C) j
  let homFD (j : ℕ) := moduleFinite_homology (C := C) j
  have hzero : C.iCycles (i + 1) ≫ C.toCycles (i + 1) i = 0 := by
    rw [← cancel_mono (C.iCycles i), Category.assoc, toCycles_i,
      iCycles_d, zero_comp]
  let S := ShortComplex.mk (C.iCycles (i + 1)) (C.toCycles (i + 1) i) hzero
  let S' := ShortComplex.mk (C.iCycles (i + 1)) (C.d (i + 1) i)
    (C.iCycles_d (i + 1) i)
  let φ : S ⟶ S' := {
    τ₁ := 𝟙 _
    τ₂ := 𝟙 _
    τ₃ := C.iCycles i
    comm₁₂ := by simp [S, S']
    comm₂₃ := by simp [S, S'] }
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
    exact S'.exact_of_f_is_kernel (C.cyclesIsKernel (i + 1) i (by simp))
  let T := ShortComplex.mk (C.toCycles (i + 1) i) (C.homologyπ i)
    (C.toCycles_comp_homologyπ (i + 1) i)
  have hT : T.Exact :=
    T.exact_of_g_is_cokernel (C.homologyIsCokernel (i + 1) i (by simp))
  apply LinearMap.trace_exact_four (C.iCycles (i + 1)).hom
    (C.toCycles (i + 1) i).hom (C.homologyπ i).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT)
    (cyclesMap f (i + 1)).hom (f.f (i + 1)).hom (cyclesMap f i).hom
    (homologyMap f i).hom
  · exact congrArg ModuleCat.Hom.hom (cyclesMap_i f (i + 1)).symm
  · apply ModuleCat.hom_ext_iff.mp
    change C.toCycles (i + 1) i ≫ cyclesMap f i = f.f (i + 1) ≫ C.toCycles (i + 1) i
    apply (cancel_mono (C.iCycles i)).mp
    simp only [Category.assoc, toCycles_i, cyclesMap_i, toCycles_i_assoc]
    exact (f.comm (i + 1) i).symm
  · exact congrArg ModuleCat.Hom.hom (homologyπ_naturality f i)

theorem alternatingTrace_eq_homology_sum_add_cycles
    [∀ i, Module.Free K (C.X i)] [∀ i, Module.Finite K (C.X i)]
    [∀ i, Module.Free K (C.homology i)] (f : C ⟶ C) (N : ℕ) :
    alternatingTrace f N =
      (∑ i ∈ Finset.range N, (-1 : K) ^ i *
        LinearMap.trace K (C.homology i) (homologyMap f i).hom) +
      (-1 : K) ^ N * LinearMap.trace K (C.cycles N) (cyclesMap f N).hom := by
  let cycF (j : ℕ) := moduleFree_cycles (C := C) j
  let cycFD (j : ℕ) := moduleFinite_cycles (C := C) j
  induction N with
  | zero =>
      simp only [alternatingTrace, zero_add, Finset.sum_range_one,
        pow_zero, one_mul, Finset.range_zero, Finset.sum_empty]
      exact (ModuleCat.trace_eq_of_iso (asIso (C.iCycles 0))
        (cyclesMap f 0) (f.f 0) (cyclesMap_i f 0)).symm
  | succ N ih =>
      have h := trace_chains_succ_sub_cycles f N
      simp only [alternatingTrace, Finset.sum_range_succ] at ih ⊢
      rw [pow_succ]
      linear_combination ih + (-1 : K) ^ (N + 1) * h

theorem alternatingTrace_eq_homology_sum
    [∀ i, Module.Free K (C.X i)] [∀ i, Module.Finite K (C.X i)]
    [∀ i, Module.Free K (C.homology i)] (f : C ⟶ C) (N : ℕ)
    (htop : C.d (N + 1) N = 0) :
    alternatingTrace f N = ∑ i ∈ Finset.range (N + 1), (-1 : K) ^ i *
      LinearMap.trace K (C.homology i) (homologyMap f i).hom := by
  let cycF (j : ℕ) := moduleFree_cycles (C := C) j
  let cycFD (j : ℕ) := moduleFinite_cycles (C := C) j
  let homFD (j : ℕ) := moduleFinite_homology (C := C) j
  rw [alternatingTrace_eq_homology_sum_add_cycles, Finset.sum_range_succ]
  congr 2
  exact ModuleCat.trace_eq_of_iso (C.isoHomologyπ (N + 1) N (by simp) htop)
    (cyclesMap f N) (homologyMap f N) (homologyπ_naturality f N).symm

end ChainComplex
