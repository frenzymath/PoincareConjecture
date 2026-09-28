import PoincareConjecture.Proofs.M35.Thm12_28.NeckDerivativeEstimates
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Matrix.Bounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35

private theorem tangentNorm_orthonormal (g : RiemannianMetric 3 StandardCapSpace)
    (x : StandardCapSpace) (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
    g.tangentNorm x (g.orthonormalBasis x i) = 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Real.sqrt (inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x i)) = 1
  rw [real_inner_self_eq_norm_sq, (g.orthonormalBasis x).norm_eq_one]
  norm_num

theorem abs_scalar_derivative_le_curvature_derivative
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : StandardCapSpace) (v : TangentSpace (𝓡 3) x) :
    |mvfderiv (𝓡 3) D.scalarCurvature x v| ≤
      9 * D.curvatureDerivativeNorm 1 x * g.tangentNorm x v := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 :=
    finrank_euclideanSpace_fin
  rw [← D.sum_covariantTensorDerivative_ricci_eq_scalar_derivative hD x v]
  calc
    _ ≤ ∑ i, |D.covariantTensorDerivative D.ricciEvaluation x
      ![v, g.orthonormalBasis x i, g.orthonormalBasis x i]| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        3 * D.curvatureDerivativeNorm 1 x * g.tangentNorm x v := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Nat.cast_ofNat, tangentNorm_orthonormal, mul_one] using
        D.abs_covariantTensorDerivative_ricci_le_curvatureDerivativeNorm hD x v
          (g.orthonormalBasis x i) (g.orthonormalBasis x i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        hdim, nsmul_eq_mul]; ring

theorem ricciNormSq_le_curvature_derivative_zero
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : StandardCapSpace) :
    D.ricciNormSq x ≤ 81 * (D.curvatureDerivativeNorm 0 x) ^ 2 := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 :=
    finrank_euclideanSpace_fin
  have hb (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      (D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2 ≤
        (3 * D.curvatureDerivativeNorm 0 x) ^ 2 := by
    have h := D.abs_ricci_le_curvatureDerivativeNorm_zero hD x
      (g.orthonormalBasis x i) (g.orthonormalBasis x j)
    simp only [Nat.cast_ofNat, tangentNorm_orthonormal, mul_one] at h
    exact (sq_abs _).symm.trans_le ((sq_le_sq₀ (abs_nonneg _) (by
      have hnonneg : 0 ≤ D.curvatureDerivativeNorm 0 x := Real.sqrt_nonneg _
      positivity)).mpr h)
  calc
    D.ricciNormSq x ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
          (3 * D.curvatureDerivativeNorm 0 x) ^ 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        hdim, nsmul_eq_mul]; ring

theorem exists_short_neck_scalar_bounds (P : RicciFlowCurvatureTheory.{0}) :
    ∃ delta A : ℝ, 0 < delta ∧ 0 < A ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
        ∀ T : ℝ, 1 / 2 ≤ T → T ≤ 1 →
        ∀ (F : RicciFlow 3 StandardCapSpace (Icc 0 T)) (x : StandardCapSpace)
          (N : StandardCylinderPatch epsilon⁻¹ x), MetricComplete (F.metric 0) →
          (∀ s ∈ Icc (0 : ℝ) T,
            RoundCylinderClose epsilon (s - T) (roundCylinderPullback (F.metric s) N.coordinate)) →
          (∀ v : TangentSpace (𝓡 3) x,
            |mvfderiv (𝓡 3) (F.connection T).scalarCurvature x v| ≤
              A * (F.metric T).tangentNorm x v) ∧
          |(F.connection T).laplacian (F.connection T).scalarCurvature x +
            2 * (F.connection T).ricciNormSq x| ≤ A := by
  obtain ⟨delta, hdelta, hderiv⟩ := exists_short_neck_derivative_bounds P
  obtain ⟨C0, hC0, hzero⟩ := hderiv 0
  obtain ⟨C1, hC1, hone⟩ := hderiv 1
  obtain ⟨C2, hC2, htwo⟩ := hderiv 2
  refine ⟨delta, 9 * C1 + 27 * C2 + 162 * C0 ^ 2 + 1, hdelta, by positivity, ?_⟩
  intro epsilon he hedelta T hTlower hTupper F x N hcomplete hclose
  have h0 := hzero epsilon he hedelta T hTlower hTupper F x N hcomplete hclose
  have h1 := hone epsilon he hedelta T hTlower hTupper F x N hcomplete hclose
  have h2 := htwo epsilon he hedelta T hTlower hTupper F x N hcomplete hclose
  have hD := P.tensor_calculus 3 StandardCapSpace (F.metric T) (F.connection T)
  constructor
  · intro v
    have h := abs_scalar_derivative_le_curvature_derivative (F.connection T) hD x v
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    nlinarith [sq_nonneg C0]
  · have h := (F.connection T).abs_laplacian_scalar_le_curvatureDerivativeNorm hD x
    have hr := ricciNormSq_le_curvature_derivative_zero (F.connection T) hD x
    have hr0 : 0 ≤ (F.connection T).ricciNormSq x :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hk0 : 0 ≤ (F.connection T).curvatureDerivativeNorm 0 x := Real.sqrt_nonneg _
    have hsquare := (sq_le_sq₀ hk0 hC0.le).mpr h0
    have hsum := abs_add_le ((F.connection T).laplacian (F.connection T).scalarCurvature x)
      (2 * (F.connection T).ricciNormSq x)
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hr0)] at hsum
    norm_num only [Nat.cast_ofNat, pow_succ, pow_zero] at h
    nlinarith

theorem exists_unit_neck_scalar_bounds (P : RicciFlowCurvatureTheory.{0}) :
    ∃ delta A : ℝ, 0 < delta ∧ 0 < A ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
        ∀ (F : RicciFlow 3 StandardCapSpace (Icc 0 1)) (x : StandardCapSpace)
          (N : StandardCylinderPatch epsilon⁻¹ x), MetricComplete (F.metric 0) →
          (∀ s ∈ Icc (0 : ℝ) 1,
            RoundCylinderClose epsilon (s - 1) (roundCylinderPullback (F.metric s) N.coordinate)) →
          (∀ v : TangentSpace (𝓡 3) x,
            |mvfderiv (𝓡 3) (F.connection 1).scalarCurvature x v| ≤
              A * (F.metric 1).tangentNorm x v) ∧
          |(F.connection 1).laplacian (F.connection 1).scalarCurvature x +
            2 * (F.connection 1).ricciNormSq x| ≤ A := by
  obtain ⟨delta, A, hdelta, hA, hbound⟩ := exists_short_neck_scalar_bounds P
  exact ⟨delta, A, hdelta, hA,
    fun epsilon he hedelta => hbound epsilon he hedelta 1 (by norm_num) le_rfl⟩

end PoincareConjecture.M35
