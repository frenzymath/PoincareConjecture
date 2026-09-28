import Mathlib

open Matrix
open scoped BigOperators ContDiff NNReal

noncomputable section

local instance : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedAddCommGroup
local instance : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedSpace

namespace Poincare.Geometry.Curvature.Operator

def curvatureOperatorCongr {ι : Type*} [Fintype ι]
    (U A : Matrix ι ι ℝ) : Matrix ι ι ℝ := Uᴴ * A * U

def curvatureReaction (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (2 : ℝ) • (A * A + Matrix.adjugate A)

theorem adjugate_fin3_eq_trace_polynomial
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsSymm) :
    Matrix.adjugate A =
      A * A - A.trace • A +
        ((A.trace ^ 2 - (A * A).trace) / 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h10 : A 1 0 = A 0 1 := congrFun (congrFun hA 0) 1
  have h20 : A 2 0 = A 0 2 := congrFun (congrFun hA 0) 2
  have h21 : A 2 1 = A 1 2 := congrFun (congrFun hA 1) 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_apply, Matrix.det_fin_three, Matrix.mul_apply, Matrix.trace,
      Fin.sum_univ_succ, h10, h20, h21]
  all_goals ring

theorem curvatureReaction_eq_trace_polynomial
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsSymm) :
    curvatureReaction A =
      (4 : ℝ) • (A * A) - (2 * A.trace) • A +
        (A.trace ^ 2 - (A * A).trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [curvatureReaction, adjugate_fin3_eq_trace_polynomial hA]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.mul_apply]
  ring

theorem curvatureReaction_diagonal (lam mu nu : ℝ) :
    curvatureReaction (Matrix.diagonal ![lam, mu, nu]) =
      Matrix.diagonal ![2 * (lam ^ 2 + mu * nu),
        2 * (mu ^ 2 + lam * nu), 2 * (nu ^ 2 + lam * mu)] := by
  have hp0 : (∏ j ∈ Finset.univ.erase (0 : Fin 3), ![lam, mu, nu] j) = mu * nu := by
    have h : Finset.univ.erase (0 : Fin 3) = ({1, 2} : Finset (Fin 3)) := by
      ext j
      fin_cases j <;> simp
    rw [h]
    simp [mul_comm]
  have hp1 : (∏ j ∈ Finset.univ.erase (1 : Fin 3), ![lam, mu, nu] j) = lam * nu := by
    have h : Finset.univ.erase (1 : Fin 3) = ({0, 2} : Finset (Fin 3)) := by
      ext j
      fin_cases j <;> simp
    rw [h]
    simp [mul_comm]
  have hp2 : (∏ j ∈ Finset.univ.erase (2 : Fin 3), ![lam, mu, nu] j) = lam * mu := by
    have h : Finset.univ.erase (2 : Fin 3) = ({0, 1} : Finset (Fin 3)) := by
      ext j
      fin_cases j <;> simp
    rw [h]
    simp [mul_comm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [curvatureReaction, Matrix.adjugate_apply, Matrix.det_fin_three, Matrix.mul_apply,
      Fin.sum_univ_succ, hp0, hp1, hp2]
  all_goals ring

private theorem curvatureOperatorCongr_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A B : Matrix ι ι ℝ) :
    curvatureOperatorCongr (U : Matrix ι ι ℝ) (A * B) =
      curvatureOperatorCongr (U : Matrix ι ι ℝ) A *
        curvatureOperatorCongr (U : Matrix ι ι ℝ) B := by
  have hU : (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)ᴴ = 1 := U.property.2
  simp only [curvatureOperatorCongr, Matrix.mul_assoc,
    ← Matrix.mul_assoc (U : Matrix ι ι ℝ) (U : Matrix ι ι ℝ)ᴴ, hU, one_mul]

private theorem trace_curvatureOperatorCongr
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (curvatureOperatorCongr (U : Matrix ι ι ℝ) A).trace = A.trace := by
  have hU : (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)ᴴ = 1 := U.property.2
  rw [curvatureOperatorCongr, Matrix.trace_mul_cycle, hU, one_mul]

theorem curvatureReaction_congr
    (U : Matrix.unitaryGroup (Fin 3) ℝ)
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian) :
    curvatureReaction (curvatureOperatorCongr (U : Matrix (Fin 3) (Fin 3) ℝ) A) =
      curvatureOperatorCongr (U : Matrix (Fin 3) (Fin 3) ℝ) (curvatureReaction A) := by
  have hUA : (curvatureOperatorCongr (U : Matrix (Fin 3) (Fin 3) ℝ) A).IsHermitian := by
    change ((U : Matrix (Fin 3) (Fin 3) ℝ)ᴴ * A * U).IsHermitian
    exact Matrix.isHermitian_conjTranspose_mul_mul (U : Matrix (Fin 3) (Fin 3) ℝ) hA
  rw [curvatureReaction_eq_trace_polynomial
      (Matrix.isHermitian_iff_isSymm.mp hUA),
    curvatureReaction_eq_trace_polynomial (Matrix.isHermitian_iff_isSymm.mp hA),
    ← curvatureOperatorCongr_mul, trace_curvatureOperatorCongr,
    trace_curvatureOperatorCongr]
  simp only [curvatureOperatorCongr, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one]
  have hUU : (U : Matrix (Fin 3) (Fin 3) ℝ)ᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.property.1
  rw [hUU]

private theorem contDiff_matrix_entry (a b : Fin 3) :
    ContDiff ℝ ∞ (fun A : Matrix (Fin 3) (Fin 3) ℝ => A a b) := by
  have ho : ContDiff ℝ ∞ (fun A : Matrix (Fin 3) (Fin 3) ℝ => A a) :=
    contDiff_apply ℝ _ a
  have hi : ContDiff ℝ ∞ (fun x : Fin 3 → ℝ => x b) :=
    contDiff_apply ℝ _ b
  simpa [Function.comp_def] using hi.comp ho

private theorem contDiff_matrix_det_update (a b : Fin 3) :
    ContDiff ℝ ∞ (fun A : Matrix (Fin 3) (Fin 3) ℝ =>
      (A.updateRow b (Pi.single a (1 : ℝ))).det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ hσ
  refine contDiff_const.mul ?_
  apply contDiff_prod
  intro i hi
  by_cases h : σ i = b
  · by_cases e : a = i
    · simpa [Matrix.updateRow_apply, h, e] using
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : Matrix (Fin 3) (Fin 3) ℝ => (1 : ℝ)))
    · simpa [Matrix.updateRow_apply, h, e] using
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : Matrix (Fin 3) (Fin 3) ℝ => (0 : ℝ)))
  · have hb : b ≠ σ i := by
      intro e
      apply h
      exact e.symm
    simpa [Matrix.updateRow_apply, h, hb] using contDiff_matrix_entry (σ i) i

private theorem contDiff_reaction_entry (a b : Fin 3) :
    ContDiff ℝ ∞ (fun A : Matrix (Fin 3) (Fin 3) ℝ => curvatureReaction A a b) := by
  unfold curvatureReaction
  change ContDiff ℝ ∞ (fun A : Matrix (Fin 3) (Fin 3) ℝ =>
    2 * ((∑ c, A a c * A c b) + Matrix.adjugate A a b))
  simp only [Matrix.adjugate_apply]
  refine contDiff_const.mul ?_
  apply (ContDiff.sum (fun c _ =>
    (contDiff_matrix_entry a c).mul (contDiff_matrix_entry c b))).add
  exact contDiff_matrix_det_update a b

theorem contDiff_curvatureReaction :
    ContDiff ℝ ∞ (fun A : Matrix (Fin 3) (Fin 3) ℝ => curvatureReaction A) := by
  let f : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ := curvatureReaction
  have hentries : ∀ a b, ContDiff ℝ ∞ (fun A => f A a b) := by
    intro a b
    exact contDiff_reaction_entry a b
  have hsum : ContDiff ℝ ∞ (fun A =>
      ∑ a, ∑ b, (f A a b) • (Matrix.single a b (1 : ℝ))) := by
    apply ContDiff.sum
    intro a ha
    apply ContDiff.sum
    intro b hb
    exact (hentries a b).smul contDiff_const
  have heq : (fun A => f A) = (fun A =>
      ∑ a, ∑ b, (f A a b) • (Matrix.single a b (1 : ℝ))) := by
    funext A
    ext a b
    change f A a b = ∑ x, ∑ y, (f A x y • (Matrix.single x y (1 : ℝ))) a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.single_apply, Fin.sum_univ_succ]
  change ContDiff ℝ ∞ (fun A => f A)
  rw [heq]
  exact hsum

theorem exists_lipschitzOnWith_curvatureReaction
    (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K)
    (hconv : Convex ℝ K) :
    ∃ C : ℝ≥0, LipschitzOnWith C curvatureReaction K := by
  exact contDiff_curvatureReaction.contDiffOn.exists_lipschitzOnWith
    (by simp) hconv hK

end Poincare.Geometry.Curvature.Operator
