import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetLogDensity










noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M65Gauss

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}




def curvatureCoefficientBound (D : LeviCivitaData g) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖g.euclideanCoefficients x‖ *
    (2 * ‖fderiv ℝ (connectionCoefficient D) x‖ + 2 * ‖connectionCoefficient D x‖ ^ 2)



theorem curvatureCoefficientBound_continuous (D : LeviCivitaData g) :
    Continuous (curvatureCoefficientBound D) := by
  have hG := (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).continuous
  have hC := (contDiff_connectionCoefficient D).continuous
  have hDC := (contDiff_connectionCoefficient D).continuous_fderiv (by simp)
  exact hG.norm.mul ((hDC.norm.const_mul 2).add ((hC.norm.pow 2).const_mul 2))

private theorem fderiv_connection_const (D : LeviCivitaData g)
    (x u v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (D.euclideanConnection v w) x u =
      fderiv ℝ (connectionCoefficient D) x u v w := by
  have hC := ((contDiff_connectionCoefficient D).differentiable (by simp) x).hasFDerivAt
  have hd := (hC.clm_apply (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x)
  have he := congrArg (fun L => L u) hd.fderiv
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] at he
  exact he





theorem abs_curvatureTensor_le_coefficient (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    |D.curvatureTensor x u v u v| ≤ curvatureCoefficientBound D x * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  let C := connectionCoefficient D x
  let A := fderiv ℝ (connectionCoefficient D) x
  let G := g.euclideanCoefficients x
  have hA (a b d : EuclideanSpace ℝ (Fin n)) :
      ‖A a b d‖ ≤ ‖A‖ * ‖a‖ * ‖b‖ * ‖d‖ :=
    ((A a b).le_opNorm d).trans (mul_le_mul_of_nonneg_right
      (A.le_opNorm₂ a b) (norm_nonneg d))
  have hC (a b d : EuclideanSpace ℝ (Fin n)) :
      ‖C a (C b d)‖ ≤ ‖C‖ ^ 2 * ‖a‖ * ‖b‖ * ‖d‖ := by
    calc
      _ ≤ ‖C‖ * ‖a‖ * ‖C b d‖ := C.le_opNorm₂ a (C b d)
      _ ≤ ‖C‖ * ‖a‖ * (‖C‖ * ‖b‖ * ‖d‖) :=
        mul_le_mul_of_nonneg_left (C.le_opNorm₂ b d)
          (mul_nonneg (norm_nonneg C) (norm_nonneg a))
      _ = _ := by ring
  let R : EuclideanSpace ℝ (Fin n) := D.curvature x u v v
  have hR : ‖R‖ ≤ (2 * ‖A‖ + 2 * ‖C‖ ^ 2) * ‖u‖ * ‖v‖ ^ 2 := by
    dsimp only [R]
    rw [D.curvature_eq_euclideanConnection, fderiv_connection_const, fderiv_connection_const]
    change ‖A u v v + C u (C v v) - (A v u v + C v (C u v))‖ ≤ _
    calc
      _ ≤ (‖A u v v‖ + ‖C u (C v v)‖) + (‖A v u v‖ + ‖C v (C u v)‖) :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ ≤ (‖A‖ * ‖u‖ * ‖v‖ * ‖v‖ + ‖C‖ ^ 2 * ‖u‖ * ‖v‖ * ‖v‖) +
          (‖A‖ * ‖v‖ * ‖u‖ * ‖v‖ + ‖C‖ ^ 2 * ‖v‖ * ‖u‖ * ‖v‖) :=
        add_le_add (add_le_add (hA u v v) (hC u v v))
          (add_le_add (hA v u v) (hC v u v))
      _ = _ := by ring
  change |G R u| ≤ _
  calc
    _ ≤ ‖G‖ * ‖R‖ * ‖u‖ := by simpa only [Real.norm_eq_abs] using G.le_opNorm₂ R u
    _ ≤ ‖G‖ * ((2 * ‖A‖ + 2 * ‖C‖ ^ 2) * ‖u‖ * ‖v‖ ^ 2) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR (norm_nonneg G)) (norm_nonneg u)
    _ = _ := by dsimp only [curvatureCoefficientBound, A, C, G]; ring

end PoincareConjecture.M65Gauss
