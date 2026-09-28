import PoincareConjecture.Proofs.M36.CylinderMetricEstimates
import PoincareConjecture.Proofs.M36.CylinderTwoJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M36

open PoincareConjecture.SpacetimeBounds

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem exists_cylinderMetric_uniform_estimates :
    ∃ delta : ℝ, 0 < delta ∧ ∃ K : ℝ, 1 ≤ K ∧
      ∀ (g : RiemannianMetric 3 E₃) (D : LeviCivitaData g) (e : ℝ),
        0 ≤ e → e ≤ delta → ‖metricTwoJet g.euclideanCoefficients 0 - cylinderModelJet‖ ≤ e →
        (1 / 2 ≤ g.inner 0 (D.gradient cylinderHeightCovector 0)
            (D.gradient cylinderHeightCovector 0) ∧
          g.inner 0 (D.gradient cylinderHeightCovector 0)
            (D.gradient cylinderHeightCovector 0) ≤ 2) ∧
        (∀ v w : E₃, |D.hessian cylinderHeightCovector 0 v w| ≤
          K * e * g.tangentNorm 0 v * g.tangentNorm 0 w) ∧
        |D.laplacian cylinderHeightCovector 0| ≤ K * e ∧
        1 / 2 ≤ D.scalarCurvature 0 ∧
        (∀ v w : E₃, LeviCivitaData.IsOrthonormalPair g 0 v w →
          -K * e ≤ D.sectionalCurvature 0 v w) ∧
        (∀ v w : E₃, LeviCivitaData.IsOrthonormalPair g 0 v w →
          cylinderHeightCovector v ^ 2 + cylinderHeightCovector w ^ 2 ≤ 1 / 2 →
          1 / 8 ≤ D.sectionalCurvature 0 v w) := by
  obtain ⟨r, hr, L, hL, hb⟩ := exists_jetCurvature_component_bounds
    cylinderModelJet cylinderModelJet_isInvertible
  let delta := min (r / 2) (min (1 / 4)
    (min (1 / (2 * (1944 * L + 76))) (1 / (8 * (324 * L + 12)))))
  have hdpos : 0 < delta := by dsimp [delta]; positivity
  have hdr : delta ≤ r / 2 := min_le_left _ _
  have hdq : delta ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hds : delta ≤ 1 / (2 * (1944 * L + 76)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdp : delta ≤ 1 / (8 * (324 * L + 12)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨delta, hdpos, max 18 (324 * L), (by norm_num : (1 : ℝ) ≤ 18).trans
    (le_max_left _ _), ?_⟩
  intro g D e he hedelta hj
  have heq : e ≤ 1 / 4 := hedelta.trans hdq
  have hes : e ≤ 1 / 2 := by linarith only [heq]
  have hnear : ‖metricTwoJet g.euclideanCoefficients 0 - cylinderModelJet‖ < r :=
    hj.trans_lt ((hedelta.trans hdr).trans_lt (by linarith only [hr]))
  obtain ⟨hc, _⟩ := hb _ hnear
  have hA : ‖g.euclideanCoefficients 0 - cylinderModelField 0‖ ≤ e :=
    (norm_fst_le (metricTwoJet g.euclideanCoefficients 0 - cylinderModelJet)).trans hj
  have hfirst : ‖fderiv ℝ g.euclideanCoefficients 0‖ ≤ e := by
    have h := (norm_fst_le
      (metricTwoJet g.euclideanCoefficients 0 - cylinderModelJet).2).trans
        ((norm_snd_le (metricTwoJet g.euclideanCoefficients 0 - cylinderModelJet)).trans hj)
    simpa only [metricTwoJet, cylinderModelJet, Prod.snd_sub, Prod.fst_sub,
      cylinderModelField_fderiv_zero, sub_zero] using h
  have hT (a : Fin 4 → Fin 3) :
      |D.curvatureTensor 0 (EuclideanSpace.basisFun (Fin 3) ℝ (a 0))
          (EuclideanSpace.basisFun (Fin 3) ℝ (a 1))
          (EuclideanSpace.basisFun (Fin 3) ℝ (a 2))
          (EuclideanSpace.basisFun (Fin 3) ℝ (a 3)) -
        cylinderModelCurvature (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j))| ≤ L * e := by
    have h := (hc (a 0) (a 1) (a 2) (a 3)).trans
      (mul_le_mul_of_nonneg_left hj hL.le)
    rw [jetCurvature_metricTwoJet D, jetCurvature_cylinderModelJet] at h
    exact h
  have hG := cylinderMetric_gradient_error g D he hes hA
  have hS := cylinderMetric_scalar_error g D he hes (mul_nonneg hL.le he) hA hT
  have hH := cylinderMetric_height_hessian_bound g D hes hA hfirst
  have hLap : |D.laplacian cylinderHeightCovector 0| ≤ 18 * e := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : E₃ → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let b := g.orthonormalBasis 0
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) (0 : E₃)) = 3 := by
      change Module.finrank ℝ E₃ = 3
      simp
    have hn (i) : g.tangentNorm 0 (b i) = 1 := by
      have hi : g.inner 0 (b i) (b i) = 1 := b.inner_eq_one i
      rw [RiemannianMetric.tangentNorm, hi, Real.sqrt_one]
    change |∑ i, D.hessian cylinderHeightCovector 0 (b i) (b i)| ≤ 18 * e
    calc
      _ ≤ ∑ i, |D.hessian cylinderHeightCovector 0 (b i) (b i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) (0 : E₃))), 6 * e := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [hn, mul_one] using hH (b i) (b i)
      _ = _ := by simp [hdim]; ring
  have hscalarSmall : (1944 * L + 76) * e ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (1944 * L + 76))).mp (hedelta.trans hds)
    nlinarith only [h]
  have hplaneSmall : (324 * L + 12) * e ≤ 1 / 8 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * (324 * L + 12))).mp (hedelta.trans hdp)
    nlinarith only [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hlo, hhi⟩ := abs_le.mp hG
    constructor <;> linarith only [hlo, hhi, heq]
  · intro v w
    apply (hH v w).trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_right
      ((by norm_num : (6 : ℝ) ≤ 18).trans (le_max_left _ _)) he
  · exact hLap.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) he)
  · have hlo := (abs_le.mp hS).1
    nlinarith only [hlo, hscalarSmall]
  · intro v w hvw
    have h := (cylinderMetric_sectional_bounds g D he hes (mul_nonneg hL.le he)
      hA hT v w hvw).1
    have hK := mul_le_mul_of_nonneg_right (le_max_right 18 (324 * L)) he
    nlinarith only [h, hK]
  · intro v w hvw haxial
    have h := (abs_le.mp (cylinderMetric_sectional_bounds g D he hes
      (mul_nonneg hL.le he) hA hT v w hvw).2).1
    nlinarith only [h, haxial, hplaneSmall]

end PoincareConjecture.M36
