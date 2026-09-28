import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Euclidean








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped ContDiff BigOperators

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ}



theorem norm_bilinear_le_dim_sq_mul_of_entries
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hB : ∀ i j : Fin n,
      |B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤ M) :
    ‖B‖ ≤ (n : ℝ) ^ 2 * M := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hexp (u v : EuclideanSpace ℝ (Fin n)) :
      B u v = ∑ j, ∑ i, (v j * u i) * B (b i) (b j) := by
    have hu : ∑ i, u i • b i = u := by
      simpa only [b, EuclideanSpace.basisFun_repr] using b.sum_repr u
    have hv : ∑ j, v j • b j = v := by
      simpa only [b, EuclideanSpace.basisFun_repr] using b.sum_repr v
    calc
      _ = B (∑ i, u i • b i) (∑ j, v j • b j) := by rw [hu, hv]
      _ = _ := by
        simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, smul_apply,
          smul_eq_mul, Finset.mul_sum, mul_assoc]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [Real.norm_eq_abs, hexp]
  calc
    _ ≤ ∑ j, ∑ i, |(v j * u i) * B (b i) (b j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _j : Fin n, ∑ _i : Fin n, (‖u‖ * ‖v‖) * M := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      have hui : |u i| ≤ ‖u‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
      have hvj : |v j| ≤ ‖v‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j
      rw [abs_mul, abs_mul]
      have hprod := mul_le_mul
        (mul_le_mul hvj hui (abs_nonneg _) (norm_nonneg _))
        (hB i j) (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hprod
    _ = ((n : ℝ) ^ 2 * M) * ‖u‖ * ‖v‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring


theorem abs_bilinear_basis_apply_le_norm
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (i j : Fin n) :
    |B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤ ‖B‖ := by
  simpa only [Real.norm_eq_abs, OrthonormalBasis.norm_eq_one, mul_one] using
    B.le_opNorm₂ (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)



theorem fderiv_bilinear_field_apply
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hA : DifferentiableAt ℝ A x)
    (w u v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => A y u v) x w = fderiv ℝ A x w u v := by
  have h := (hA.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_const v x)
  simpa using congrArg (fun L => L w) h.fderiv



theorem norm_fderiv_bilinear_field_entry_le
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hA : DifferentiableAt ℝ A x) (i j : Fin n) :
    ‖fderiv ℝ (fun y => A y (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)) x‖ ≤ ‖fderiv ℝ A x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro w
  rw [fderiv_bilinear_field_apply hA, Real.norm_eq_abs]
  exact (abs_bilinear_basis_apply_le_norm (fderiv ℝ A x w) i j).trans
    ((fderiv ℝ A x).le_opNorm w)



theorem norm_fderiv_bilinear_field_sub_le_of_entry_derivatives
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : DifferentiableAt ℝ A x) (hy : DifferentiableAt ℝ A y)
    {M : ℝ} (hM : 0 ≤ M)
    (hentry : ∀ i j : Fin n,
      ‖fderiv ℝ (fun z => A z (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) x -
        fderiv ℝ (fun z => A z (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) y‖ ≤ M) :
    ‖fderiv ℝ A x - fderiv ℝ A y‖ ≤ (n : ℝ) ^ 2 * M := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let B := fderiv ℝ A x - fderiv ℝ A y
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have hb (i j : Fin n) : |B w (b i) (b j)| ≤ M * ‖w‖ := by
    have heq : B w (b i) (b j) =
        (fderiv ℝ (fun z => A z (b i) (b j)) x -
          fderiv ℝ (fun z => A z (b i) (b j)) y) w := by
      simp only [B, sub_apply, fderiv_bilinear_field_apply hx, fderiv_bilinear_field_apply hy]
    rw [heq, ← Real.norm_eq_abs]
    exact ((fderiv ℝ (fun z => A z (b i) (b j)) x -
      fderiv ℝ (fun z => A z (b i) (b j)) y).le_opNorm w).trans
        (mul_le_mul_of_nonneg_right (hentry i j) (norm_nonneg w))
  have hbound := norm_bilinear_le_dim_sq_mul_of_entries (B w)
    (mul_nonneg hM (norm_nonneg w)) hb
  simpa only [B, mul_assoc] using hbound



theorem norm_fderiv_bilinear_field_sub_le_of_entry_halfHolder
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {R H : ℝ} (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 R)) (hH : 0 ≤ H)
    (hentry : ∀ i j : Fin n, ∀ x ∈ Metric.ball 0 R, ∀ y ∈ Metric.ball 0 R,
      ‖fderiv ℝ (fun z => A z (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) x -
        fderiv ℝ (fun z => A z (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ))
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball 0 R) (hy : y ∈ Metric.ball 0 R) :
    ‖fderiv ℝ A x - fderiv ℝ A y‖ ≤ (n : ℝ) ^ 2 * H * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  have hbound := norm_fderiv_bilinear_field_sub_le_of_entry_derivatives
    ((hA.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
    ((hA.contDiffAt (Metric.isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
    (mul_nonneg hH (Real.rpow_nonneg (norm_nonneg _) _)) (fun i j => hentry i j x hx y hy)
  simpa only [mul_assoc] using hbound

end PoincareConjecture.HarmonicCoordinates

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ}



theorem norm_fderiv_euclideanCoefficients_sub_le_of_entry_halfHolder
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) {R H : ℝ} (hH : 0 ≤ H)
    (hentry : ∀ i j : Fin n, ∀ x ∈ Metric.ball 0 R, ∀ y ∈ Metric.ball 0 R,
      ‖fderiv ℝ (fun z => g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) x -
        fderiv ℝ (fun z => g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ))
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball 0 R) (hy : y ∈ Metric.ball 0 R) :
    ‖fderiv ℝ g.euclideanCoefficients x - fderiv ℝ g.euclideanCoefficients y‖ ≤
      (n : ℝ) ^ 2 * H * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  exact HarmonicCoordinates.norm_fderiv_bilinear_field_sub_le_of_entry_halfHolder
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).contDiffOn hH hentry hx hy

end PoincareConjecture.RiemannianMetric
