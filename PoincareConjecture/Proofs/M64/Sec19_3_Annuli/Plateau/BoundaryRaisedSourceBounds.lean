import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryInverseCoefficientBounds













set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped ContDiff

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64BoundaryRaisedSourceBounds_bilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64BoundaryRaisedSourceBounds_bilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace







def m64BoundaryRaisedSource (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (w : Fin 2 → ℝ) (z : E) (V : Fin 2 → E) (b : Fin n → ℝ) (k : Fin n) : ℝ :=
  (∑ j : Fin n, b j * (m64BoundaryMetricInverse (G z) (EuclideanSpace.single k 1)) j) -
    ∑ i : Fin 2, ∑ j : Fin n, (w i * G z (V i) (EuclideanSpace.single j 1)) *
      fderiv ℝ (fun y => (m64BoundaryMetricInverse (G y) (EuclideanSpace.single k 1)) j)
        z (V i)






theorem m64BoundaryRaisedSource_bound
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (w : Fin 2 → ℝ)
    (z : E) (V : Fin 2 → E) (b : Fin n → ℝ) (k : Fin n)
    {L Lambda Cb : ℝ} (hL : 0 ≤ L) (hLambda : 0 ≤ Lambda) (hCb : 0 ≤ Cb)
    (hG : ‖G z‖ ≤ L) (hw : ∀ i, |w i| ≤ Lambda)
    (ha : ∀ j : Fin n,
      |(m64BoundaryMetricInverse (G z) (EuclideanSpace.single k 1)) j| ≤ L ∧
      ‖fderiv ℝ (fun y =>
        (m64BoundaryMetricInverse (G y) (EuclideanSpace.single k 1)) j) z‖ ≤ L)
    (hb : ∀ j, |b j| ≤ Cb * ∑ i : Fin 2, ‖V i‖ ^ 2) :
    |m64BoundaryRaisedSource G w z V b k| ≤
      (n : ℝ) * L * (Cb + Lambda * L) * ∑ i : Fin 2, ‖V i‖ ^ 2 := by
  let A : Fin n → E → ℝ := fun j y =>
    (m64BoundaryMetricInverse (G y) (EuclideanSpace.single k 1)) j
  have hfirst : |∑ j : Fin n, b j * A j z| ≤
      (n : ℝ) * Cb * L * ∑ i : Fin 2, ‖V i‖ ^ 2 := by
    calc
      _ ≤ ∑ j : Fin n, |b j * A j z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, (Cb * ∑ i : Fin 2, ‖V i‖ ^ 2) * L := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hb j) (ha j).1 (abs_nonneg _) (by positivity)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring
  have hpoint (i : Fin 2) (j : Fin n) :
      |(w i * G z (V i) (EuclideanSpace.single j 1)) * fderiv ℝ (A j) z (V i)| ≤
        Lambda * L ^ 2 * ‖V i‖ ^ 2 := by
    have hg : |G z (V i) (EuclideanSpace.single j 1)| ≤ L * ‖V i‖ := by
      have hh := (G z).le_opNorm₂ (V i) (EuclideanSpace.single j 1)
      simp only [PiLp.norm_single, Real.norm_eq_abs, abs_one, mul_one] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hG (norm_nonneg _))
    have hd : |fderiv ℝ (A j) z (V i)| ≤ L * ‖V i‖ :=
      ((fderiv ℝ (A j) z).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (ha j).2 (norm_nonneg _))
    calc
      _ = |w i| * |G z (V i) (EuclideanSpace.single j 1)| *
          |fderiv ℝ (A j) z (V i)| := by rw [abs_mul, abs_mul]
      _ ≤ (Lambda * (L * ‖V i‖)) * (L * ‖V i‖) :=
        mul_le_mul (mul_le_mul (hw i) hg (abs_nonneg _) hLambda) hd
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hsecond : |∑ i : Fin 2, ∑ j : Fin n,
      (w i * G z (V i) (EuclideanSpace.single j 1)) * fderiv ℝ (A j) z (V i)| ≤
      (n : ℝ) * Lambda * L ^ 2 * ∑ i : Fin 2, ‖V i‖ ^ 2 := by
    calc
      _ ≤ ∑ i : Fin 2, |∑ j : Fin n,
          (w i * G z (V i) (EuclideanSpace.single j 1)) * fderiv ℝ (A j) z (V i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 2, ∑ _j : Fin n, Lambda * L ^ 2 * ‖V i‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => hpoint i j)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp_rw [← mul_assoc]
        rw [← Finset.mul_sum]
  exact (abs_sub _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end PoincareConjecture
