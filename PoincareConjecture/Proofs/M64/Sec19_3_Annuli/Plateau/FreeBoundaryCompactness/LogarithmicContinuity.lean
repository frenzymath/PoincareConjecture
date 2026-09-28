import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.MonotoneHelly
import Mathlib.Topology.MetricSpace.Equicontinuity

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M64

theorem equicontinuousAt_of_monotone_logarithmic_gap
    {I : Type*} (f : I → ℝ → ℝ)
    (hmono : ∀ i, MonotoneOn (f i) (Icc (0 : ℝ) curvePeriod))
    {x rho : ℝ} (hrho : 0 < rho) (hx : rho < x) (hP : x + rho < curvePeriod)
    (C : ℝ) (hgap : ∀ i, ∀ N : ℕ, 0 < N →
      (f i (x + rho * Real.exp (-(N : ℝ))) - f i (x - rho * Real.exp (-(N : ℝ)))) ^ 2 ≤ C / N) :
    EquicontinuousAt f x := by
  apply Metric.equicontinuousAt_iff.mpr
  intro eps heps
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (C / eps ^ 2))
  have hNpos : 0 < N := by
    have hh : (0 : ℝ) < N := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hN)
    exact_mod_cast hh
  have hsmall : C / N < eps ^ 2 := by
    apply (div_lt_iff₀ (by exact_mod_cast hNpos : (0 : ℝ) < N)).mpr
    have hh := (div_lt_iff₀ (sq_pos_of_pos heps)).mp ((le_max_right _ _).trans_lt hN)
    nlinarith
  let d := rho * Real.exp (-(N : ℝ))
  have hd : 0 < d := mul_pos hrho (Real.exp_pos _)
  have hdle : d ≤ rho := mul_le_of_le_one_right hrho.le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N)))
  refine ⟨d, hd, ?_⟩
  intro y hy i
  rw [Real.dist_eq] at hy
  have hy' := abs_lt.mp hy
  have hl : x - d ∈ Icc (0 : ℝ) curvePeriod := ⟨by linarith, by linarith⟩
  have hu : x + d ∈ Icc (0 : ℝ) curvePeriod := ⟨by linarith, by linarith⟩
  have hxx : x ∈ Icc (0 : ℝ) curvePeriod := ⟨by linarith, by linarith⟩
  have hyy : y ∈ Icc (0 : ℝ) curvePeriod := ⟨by linarith, by linarith⟩
  have hlx := hmono i hl hxx (by linarith)
  have hxu := hmono i hxx hu (by linarith)
  have hly := hmono i hl hyy (by linarith)
  have hyu := hmono i hyy hu (by linarith)
  have hgap' := (hgap i N hNpos).trans_lt hsmall
  have hspan : f i (x + d) - f i (x - d) < eps := by
    change (f i (x + d) - f i (x - d)) ^ 2 < eps ^ 2 at hgap'
    nlinarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem continuousAt_liminf_of_equicontinuousAt
    (f : ℕ → ℝ → ℝ)
    (hbounded : ∀ y : ℝ, ∃ lo hi : ℝ, ∀ j, f j y ∈ Icc lo hi)
    {x : ℝ} (hequi : EquicontinuousAt f x) :
    ContinuousAt (fun y => liminf (fun j => f j y) atTop) x := by
  choose lo hi hb using hbounded
  have hbelow (y : ℝ) : IsBoundedUnder (· ≥ ·) atTop (fun j => f j y) :=
    isBoundedUnder_of ⟨lo y, fun j => (hb y j).1⟩
  have habove (y : ℝ) : IsBoundedUnder (· ≤ ·) atTop (fun j => f j y) :=
    isBoundedUnder_of ⟨hi y, fun j => (hb y j).2⟩
  apply Metric.continuousAt_iff.mpr
  intro eps heps
  obtain ⟨d, hd, hdist⟩ := Metric.equicontinuousAt_iff.mp hequi (eps / 2) (half_pos heps)
  refine ⟨d, hd, ?_⟩
  intro y hy
  have hleft : liminf (fun j => f j x) atTop - eps / 2 ≤
      liminf (fun j => f j y) atTop := by
    rw [← liminf_sub_const atTop (fun j => f j x) (eps / 2)
      (habove x).isCobounded_ge (hbelow x)]
    apply liminf_le_liminf
      (Eventually.of_forall fun j => ?_)
      (isBoundedUnder_of ⟨lo x - eps / 2, fun j => sub_le_sub_right (hb x j).1 _⟩)
      (habove y).isCobounded_ge
    have hh := abs_lt.mp (show |f j x - f j y| < eps / 2 from hdist y hy j)
    linarith
  have hright : liminf (fun j => f j y) atTop ≤
      liminf (fun j => f j x) atTop + eps / 2 := by
    rw [← liminf_add_const atTop (fun j => f j x) (eps / 2)
      (habove x).isCobounded_ge (hbelow x)]
    apply liminf_le_liminf (Eventually.of_forall fun j => ?_) (hbelow y)
      (isBoundedUnder_of ⟨hi x + eps / 2, fun j => by linarith [(hb x j).2]⟩).isCobounded_ge
    have hh := abs_lt.mp (show |f j x - f j y| < eps / 2 from hdist y hy j)
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end PoincareConjecture.M64
