import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.TraceExact
import Mathlib.Algebra.Homology.Homotopy

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Module
open scoped BigOperators

universe u v

namespace ChainComplex

variable {K : Type u} [CommRing K] {C : ChainComplex (ModuleCat.{v} K) ℕ}

def alternatingTrace (f : C ⟶ C) (N : ℕ) : K :=
  ∑ i ∈ Finset.range (N + 1), (-1 : K) ^ i * LinearMap.trace K (C.X i) (f.f i).hom

theorem alternatingTrace_sub_of_homotopy
    [∀ i, Module.Free K (C.X i)] [∀ i, Module.Finite K (C.X i)] {f g : C ⟶ C}
    (H : Homotopy f g) (N : ℕ) :
    alternatingTrace f N - alternatingTrace g N =
      (-1 : K) ^ N * LinearMap.trace K (C.X N)
        (H.hom N (N + 1) ≫ C.d (N + 1) N).hom := by
  let t (i : ℕ) := LinearMap.trace K (C.X i) (H.hom i (i + 1) ≫ C.d (i + 1) i).hom
  have hzero : LinearMap.trace K (C.X 0) (f.f 0).hom =
      t 0 + LinearMap.trace K (C.X 0) (g.f 0).hom := by
    have hc := H.comm 0
    rw [dNext_eq_zero H.hom 0 (by simp),
      prevD_eq H.hom (show (ComplexShape.down ℕ).Rel 1 0 by rfl), zero_add] at hc
    rw [hc, ModuleCat.hom_add, map_add]
  have hsucc (i : ℕ) : LinearMap.trace K (C.X (i + 1)) (f.f (i + 1)).hom =
      t i + t (i + 1) + LinearMap.trace K (C.X (i + 1)) (g.f (i + 1)).hom := by
    have hc := H.comm (i + 1)
    rw [dNext_eq H.hom (show (ComplexShape.down ℕ).Rel (i + 1) i by rfl),
      prevD_eq H.hom (show (ComplexShape.down ℕ).Rel (i + 2) (i + 1) by rfl)] at hc
    rw [hc, ModuleCat.hom_add, map_add, ModuleCat.hom_add, map_add]
    congr 2
    exact LinearMap.trace_comp_comm' (C.d (i + 1) i).hom (H.hom i (i + 1)).hom
  change alternatingTrace f N - alternatingTrace g N = (-1 : K) ^ N * t N
  induction N with
  | zero => simpa [alternatingTrace, t] using (sub_eq_iff_eq_add.mpr hzero)
  | succ N ih =>
      simp only [alternatingTrace, Finset.sum_range_succ] at ih ⊢
      rw [hsucc N, pow_succ]
      linear_combination ih

theorem alternatingTrace_eq_of_homotopy
    [∀ i, Module.Free K (C.X i)] [∀ i, Module.Finite K (C.X i)] {f g : C ⟶ C}
    (H : Homotopy f g) (N : ℕ) (htop : C.d (N + 1) N = 0) :
    alternatingTrace f N = alternatingTrace g N := by
  apply sub_eq_zero.mp
  rw [alternatingTrace_sub_of_homotopy H N, htop, comp_zero,
    ModuleCat.hom_zero, map_zero, mul_zero]

theorem alternatingTrace_eq_zero_of_diagonal_eq_zero
    (f : C ⟶ C) (N : ℕ) (ι : ℕ → Type*) [∀ i, Finite (ι i)]
    (b : ∀ i, Basis (ι i) K (C.X i))
    (hdiag : ∀ i ≤ N, ∀ j, (b i).repr ((f.f i).hom (b i j)) j = 0) :
    alternatingTrace f N = 0 := by
  classical
  let iF (i : ℕ) : Fintype (ι i) := Fintype.ofFinite (ι i)
  apply Finset.sum_eq_zero
  intro i hi
  have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [LinearMap.trace_eq_matrix_trace K (b i)]
  have htrace : Matrix.trace (LinearMap.toMatrix (b i) (b i) (f.f i).hom) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact (LinearMap.toMatrix_apply (b i) (b i) (f.f i).hom j j).trans (hdiag i hiN j)
  rw [htrace, mul_zero]

end ChainComplex
