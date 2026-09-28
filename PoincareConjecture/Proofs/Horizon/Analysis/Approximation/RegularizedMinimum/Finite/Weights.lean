import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.RegularizedMinimum.Finite.Basic
import Mathlib.Analysis.Calculus.Deriv.Pi

set_option autoImplicit false

open Set
open scoped ContDiff

namespace Poincare

noncomputable def finiteRegularizedMinWeight (δ : ℝ) (hδ : 0 < δ) :
    (n : ℕ) → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, _ => fun _ => 1
  | n + 1, f =>
    let d := deriv (regularizedAbs δ hδ) (f 0 - finiteRegularizedMin δ hδ n (Fin.tail f))
    Fin.cases ((1 - d) / 2)
      (fun i => ((1 + d) / 2) * finiteRegularizedMinWeight δ hδ n (Fin.tail f) i)

theorem finiteRegularizedMinWeight_nonneg (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : 0 ≤ finiteRegularizedMinWeight δ hδ n f i := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih =>
    have hd := abs_le.mp (abs_deriv_regularizedAbs_le_one δ hδ
      (f 0 - finiteRegularizedMin δ hδ n (Fin.tail f)))
    refine Fin.cases (by dsimp [finiteRegularizedMinWeight]; linarith) (fun i => ?_) i
    exact mul_nonneg (by linarith) (ih (Fin.tail f) i)

theorem sum_finiteRegularizedMinWeight (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (f : Fin (n + 1) → ℝ) : ∑ i, finiteRegularizedMinWeight δ hδ n f i = 1 := by
  induction n with
  | zero => simp [finiteRegularizedMinWeight]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [finiteRegularizedMinWeight, Fin.cases_zero, Fin.cases_succ]
    rw [← Finset.mul_sum, ih]
    ring

theorem hasDerivAt_finiteRegularizedMin (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (u : Fin (n + 1) → ℝ → ℝ) (v : Fin (n + 1) → ℝ) (x : ℝ)
    (hu : ∀ i, HasDerivAt (u i) (v i) x) :
    HasDerivAt (fun t => finiteRegularizedMin δ hδ n (fun i => u i t))
      (∑ i, finiteRegularizedMinWeight δ hδ n (fun i => u i x) i * v i) x := by
  induction n with
  | zero => simpa [finiteRegularizedMin, finiteRegularizedMinWeight] using hu 0
  | succ n ih =>
    have ht := ih (fun i => u i.succ) (fun i => v i.succ) (fun i => hu i.succ)
    let d := deriv (regularizedAbs δ hδ)
      (u 0 x - finiteRegularizedMin δ hδ n (fun i => u i.succ x))
    have ha : HasDerivAt (regularizedAbs δ hδ) d
        (u 0 x - finiteRegularizedMin δ hδ n (fun i => u i.succ x)) :=
      ((contDiff_regularizedAbs δ hδ).differentiable (by simp) _).hasDerivAt
    have heq : (∑ i, finiteRegularizedMinWeight δ hδ (n + 1) (fun i => u i x) i * v i) =
        (v 0 + (∑ i, finiteRegularizedMinWeight δ hδ n (fun i => u i.succ x) i * v i.succ) -
          d * (v 0 - (∑ i, finiteRegularizedMinWeight δ hδ n (fun i => u i.succ x) i * v i.succ))) / 2 := by
      rw [Fin.sum_univ_succ]
      simp only [finiteRegularizedMinWeight, Fin.cases_zero, Fin.cases_succ, Fin.tail_def]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      dsimp only [d]
      ring
    rw [heq]
    simpa +instances only [finiteRegularizedMin, regularizedMin, Fin.tail_def,
      Function.comp_def, Pi.add_apply, Pi.sub_apply] using
      (((hu 0).add ht).sub (ha.comp x ((hu 0).sub ht))).div_const 2

theorem fderiv_finiteRegularizedMin_apply (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (f v : Fin (n + 1) → ℝ) :
    fderiv ℝ (finiteRegularizedMin δ hδ n) f v =
      ∑ i, finiteRegularizedMinWeight δ hδ n f i * v i := by
  have hline : HasDerivAt (fun t : ℝ => f + t • v) v 0 := by
    simpa +instances only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add f
  have hd := ((contDiff_finiteRegularizedMin δ hδ n).differentiable (by simp) f).hasFDerivAt
  have hd' : HasFDerivAt (finiteRegularizedMin δ hδ n)
      (fderiv ℝ (finiteRegularizedMin δ hδ n) f) (f + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using hd
  have hcomp := hd'.comp_hasDerivAt 0 hline
  have hcomp' : HasDerivAt (fun t => finiteRegularizedMin δ hδ n (fun i => f i + t * v i))
      (fderiv ℝ (finiteRegularizedMin δ hδ n) f v) 0 := by
    simpa +instances only [zero_smul, add_zero, Function.comp_def, Pi.add_def, Pi.smul_def,
      smul_eq_mul] using hcomp
  have h := hasDerivAt_finiteRegularizedMin δ hδ n
    (fun i t => f i + t * v i) v 0 (fun i => by
      simpa +instances only [one_mul, id_eq] using
        ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (f i))
  simpa only [zero_mul, add_zero] using hcomp'.unique h

theorem finiteRegularizedMinWeight_eq_fderiv (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    finiteRegularizedMinWeight δ hδ n f i =
      fderiv ℝ (finiteRegularizedMin δ hδ n) f (Pi.single i 1) := by
  rw [fderiv_finiteRegularizedMin_apply]
  simp [Pi.single_apply]

theorem fderiv2_finiteRegularizedMin_nonpos (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (f v : Fin (n + 1) → ℝ) :
    fderiv ℝ (fderiv ℝ (finiteRegularizedMin δ hδ n)) f v v ≤ 0 := by
  let A : ℝ → (Fin (n + 1) → ℝ) := fun t => f + t • v
  let q : ℝ → ℝ := fun t => finiteRegularizedMin δ hδ n (A t)
  have hA (t : ℝ) : HasDerivAt A v t := by
    simpa +instances only [A, one_smul, id_eq] using
      ((hasDerivAt_id t).smul_const v).const_add f
  have hq : ConcaveOn ℝ univ q := by
    simpa [A, q, Function.comp_def, AffineMap.coe_lineMap, add_comm] using
      (concaveOn_finiteRegularizedMin δ hδ n).comp_affineMap (AffineMap.lineMap f (f + v))
  have hd (t : ℝ) : HasDerivAt q
      (fderiv ℝ (finiteRegularizedMin δ hδ n) (A t) v) t :=
    ((contDiff_finiteRegularizedMin δ hδ n).differentiable (by simp) (A t)).hasFDerivAt.comp_hasDerivAt
      t (hA t)
  have hant := hq.antitoneOn_deriv (fun t _ => (hd t).differentiableAt)
  have hn : deriv (deriv q) 0 ≤ 0 :=
    (show Antitone (deriv q) from fun x y hxy => hant (mem_univ x) (mem_univ y) hxy).deriv_nonpos
  have hdf : HasFDerivAt (fderiv ℝ (finiteRegularizedMin δ hδ n))
      (fderiv ℝ (fderiv ℝ (finiteRegularizedMin δ hδ n)) f) (A 0) := by
    simpa [A] using
      (((contDiff_finiteRegularizedMin δ hδ n).fderiv_right (m := ∞) (by simp)).differentiable
        (by simp) f).hasFDerivAt
  have hsecond := (hdf.comp_hasDerivAt 0 (hA 0)).clm_apply (hasDerivAt_const 0 v)
  simp only [Function.comp_def, map_zero, add_zero] at hsecond
  have heq : deriv q = fun t => fderiv ℝ (finiteRegularizedMin δ hδ n) (A t) v :=
    funext fun t => (hd t).deriv
  rw [heq, hsecond.deriv] at hn
  simpa using hn

end Poincare
