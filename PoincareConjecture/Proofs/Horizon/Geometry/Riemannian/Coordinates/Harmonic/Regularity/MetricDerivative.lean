import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.AlongCurve.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Tensor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.NormBounds









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}



theorem hessian_coordinate_eq_neg_connectionCoefficient (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    D.hessian (fun y : EuclideanSpace ℝ (Fin n) => y i) x u v =
      -(D.connectionCoefficient x u v) i := by
  have hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y : EuclideanSpace ℝ (Fin n) => y i) :=
    contMDiff_iff_contDiff.mpr (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  have hV : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (fun y : EuclideanSpace ℝ (Fin n) => (show TangentSpace (𝓡 n) y from v))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hcoord (y w : EuclideanSpace ℝ (Fin n)) :
      mvfderiv (𝓡 n) (fun z : EuclideanSpace ℝ (Fin n) => z i) y w = w i := by
    simp only [mvfderiv, mfderiv_eq_fderiv]
    change fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) i) y w = w i
    rw [ContinuousLinearMap.fderiv]
    rfl
  have h := D.hessianOnFields_eq_inner_connection_gradient (hq x)
    (fun _ : EuclideanSpace ℝ (Fin n) => u) ((hV x).mdifferentiableAt (by simp))
  rw [← D.hessian_eq_inner_connection_gradient (hq x)] at h
  simp only [hessianOnFields, hcoord, mvfderiv_const, zero_apply, zero_sub] at h
  exact h.symm

private theorem tangentNorm_le_sqrt_upper (x : EuclideanSpace ℝ (Fin n))
    {b : ℝ} (hb : 0 ≤ b)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) : g.tangentNorm x v ≤ Real.sqrt b * ‖v‖ := by
  have h := Real.sqrt_le_sqrt (hupper v)
  simpa only [RiemannianMetric.tangentNorm, Real.sqrt_mul hb,
    Real.sqrt_sq (norm_nonneg v)] using h

private theorem abs_inner_le_upper (x : EuclideanSpace ℝ (Fin n))
    {b : ℝ} (hb : 0 ≤ b)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2)
    (u v : EuclideanSpace ℝ (Fin n)) : |g.inner x u v| ≤ b * ‖u‖ * ‖v‖ := by
  have hcs : |g.inner x u v| ≤ g.tangentNorm x u * g.tangentNorm x v := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact abs_real_inner_le_norm (show TangentSpace (𝓡 n) x from u)
      (show TangentSpace (𝓡 n) x from v)
  calc
    _ ≤ g.tangentNorm x u * g.tangentNorm x v := hcs
    _ ≤ (Real.sqrt b * ‖u‖) * (Real.sqrt b * ‖v‖) :=
      mul_le_mul (tangentNorm_le_sqrt_upper x hb hupper u)
        (tangentNorm_le_sqrt_upper x hb hupper v) (Real.sqrt_nonneg _) (by positivity)
    _ = (Real.sqrt b) ^ 2 * ‖u‖ * ‖v‖ := by ring
    _ = _ := by rw [Real.sq_sqrt hb]



theorem norm_connectionCoefficient_apply_le_of_coordinate_hessian_bound
    (D : LeviCivitaData g) (x : EuclideanSpace ℝ (Fin n)) {b L : ℝ}
    (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2)
    (hH : ∀ i : Fin n, g.tensorNorm (k := 2)
      (fun y v => D.hessian (fun z : EuclideanSpace ℝ (Fin n) => z i) y (v 0) (v 1)) x ≤ L)
    (u v : EuclideanSpace ℝ (Fin n)) :
    ‖D.connectionCoefficient x u v‖ ≤ Real.sqrt n * L * b * ‖u‖ * ‖v‖ := by
  have hcomponent (i : Fin n) : |(D.connectionCoefficient x u v) i| ≤ L * b * ‖u‖ * ‖v‖ := by
    have hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y : EuclideanSpace ℝ (Fin n) => y i) :=
      contMDiff_iff_contDiff.mpr (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
    obtain ⟨A, hA⟩ := (D.hessian_isSmoothCovariantTensor hq).1 x
    have h := abs_tensor_evaluation_le_tensorNorm g
      (fun y w => D.hessian (fun z : EuclideanSpace ℝ (Fin n) => z i) y (w 0) (w 1))
      x A hA ![u, v]
    have heval : |D.hessian (fun z : EuclideanSpace ℝ (Fin n) => z i) x u v| ≤
        g.tensorNorm (k := 2) (fun y w => D.hessian
          (fun z : EuclideanSpace ℝ (Fin n) => z i) y (w 0) (w 1)) x *
            g.tangentNorm x u * g.tangentNorm x v := by
      simpa [Fin.prod_univ_succ, mul_assoc] using h
    rw [D.hessian_coordinate_eq_neg_connectionCoefficient, abs_neg] at heval
    calc
      _ ≤ g.tensorNorm (k := 2) (fun y w => D.hessian
          (fun z : EuclideanSpace ℝ (Fin n) => z i) y (w 0) (w 1)) x *
            g.tangentNorm x u * g.tangentNorm x v := heval
      _ ≤ L * (Real.sqrt b * ‖u‖) * (Real.sqrt b * ‖v‖) := by
        gcongr
        · exact Real.sqrt_nonneg _
        · exact Real.sqrt_nonneg _
        · exact hH i
        · exact tangentNorm_le_sqrt_upper x hb hupper u
        · exact tangentNorm_le_sqrt_upper x hb hupper v
      _ = L * (Real.sqrt b) ^ 2 * ‖u‖ * ‖v‖ := by ring
      _ = _ := by rw [Real.sq_sqrt hb]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin n, (L * b * ‖u‖ * ‖v‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hcomponent i)
    _ = (Real.sqrt n * L * b * ‖u‖ * ‖v‖) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      ring



theorem norm_fderiv_euclideanCoefficients_le_of_coordinate_hessian_bound
    (D : LeviCivitaData g) (x : EuclideanSpace ℝ (Fin n)) {b L : ℝ}
    (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2)
    (hH : ∀ i : Fin n, g.tensorNorm (k := 2)
      (fun y v => D.hessian (fun z : EuclideanSpace ℝ (Fin n) => z i) y (v 0) (v 1)) x ≤ L) :
    ‖fderiv ℝ g.euclideanCoefficients x‖ ≤ 2 * Real.sqrt n * L * b ^ 2 := by
  have hconn := D.norm_connectionCoefficient_apply_le_of_coordinate_hessian_bound x hb hL hupper hH
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [Real.norm_eq_abs, D.connectionCoefficient_metricCompatible]
  change |g.inner x (D.connectionCoefficient x u v) w +
    g.inner x v (D.connectionCoefficient x u w)| ≤ _
  calc
    _ ≤ |g.inner x (D.connectionCoefficient x u v) w| +
        |g.inner x v (D.connectionCoefficient x u w)| := abs_add_le _ _
    _ ≤ b * ‖D.connectionCoefficient x u v‖ * ‖w‖ +
        b * ‖v‖ * ‖D.connectionCoefficient x u w‖ :=
      add_le_add (abs_inner_le_upper x hb hupper _ _) (abs_inner_le_upper x hb hupper _ _)
    _ ≤ b * (Real.sqrt n * L * b * ‖u‖ * ‖v‖) * ‖w‖ +
        b * ‖v‖ * (Real.sqrt n * L * b * ‖u‖ * ‖w‖) := by
      gcongr
      · exact hconn u v
      · exact hconn u w
    _ = _ := by ring



theorem norm_fderiv_euclideanCoefficients_le_of_coordinate_hessian_normSq_bound
    (D : LeviCivitaData g) (x : EuclideanSpace ℝ (Fin n)) {b L : ℝ}
    (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2)
    (hH : ∀ i : Fin n, (∑ j, ∑ k,
      D.hessian (fun z : EuclideanSpace ℝ (Fin n) => z i) x
        (g.orthonormalBasis x j) (g.orthonormalBasis x k) ^ 2) ≤ L ^ 2) :
    ‖fderiv ℝ g.euclideanCoefficients x‖ ≤ 2 * Real.sqrt n * L * b ^ 2 := by
  apply D.norm_fderiv_euclideanCoefficients_le_of_coordinate_hessian_bound x hb hL hupper
  intro i
  unfold RiemannianMetric.tensorNorm
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hL, ?_⟩
  have hsum : (∑ j : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      D.hessian (fun z : EuclideanSpace ℝ (Fin n) => z i) x
        (g.orthonormalBasis x (j 0)) (g.orthonormalBasis x (j 1)) ^ 2) =
      ∑ j, ∑ k, D.hessian (fun z : EuclideanSpace ℝ (Fin n) => z i) x
        (g.orthonormalBasis x j) (g.orthonormalBasis x k) ^ 2 := by
    calc
      _ = ∑ jk : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          D.hessian (fun z : EuclideanSpace ℝ (Fin n) => z i) x
            (g.orthonormalBasis x jk.1) (g.orthonormalBasis x jk.2) ^ 2 :=
        Fintype.sum_equiv (finTwoArrowEquiv _) _ _ (fun _ => rfl)
      _ = _ := Fintype.sum_prod_type _
  exact hsum.trans_le (hH i)

end PoincareConjecture.LeviCivitaData
