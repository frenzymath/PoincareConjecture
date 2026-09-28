import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.TangentRicciDerivatives
import PoincareConjecture.Proofs.M62.Cor0_3_PointwiseBounds











set_option autoImplicit false

open Set Bundle Manifold
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}





theorem normalizationCoefficient_spatial_abs_bound [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    |deriv (fun y => m62TangentRicci F c t y + m62CurvatureSquared F c t y) x| ≤
      curveSpeed F c t x * (K1 + 2 * K2 * m62Curvature F c t x +
        2 * m62Curvature F c t x *
          (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x)) := by
  let p := c x t
  let g := F.metric t
  let D := F.connection t
  let S := spatialUnitTangent F c t x
  let H := m63CurvatureJet F c 0 t x
  let B := m63CurvatureJet F c 1 t x
  let v := curveSpeed F c t x
  let k := m62Curvature F c t x
  let u := g.tangentNorm p B
  let r := m62TangentRicci F c t
  let q := m62CurvatureSquared F c t
  let A : ℝ → ℝ := fun y => r y + q y
  have ht' := Ioo_subset_Icc_self ht
  have hv : 0 < v := speed_pos F c hc ht' x
  have hS : g.tangentNorm p S = 1 := unitTangent_norm F c hc ht' x
  have hH : g.tangentNorm p H = k := rfl
  have hB : g.tangentNorm p B = u := rfl
  have hA : ContDiff ℝ ∞ A :=
    (normalization_coefficient_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hq : ContDiff ℝ ∞ q :=
    (curvatureSquared_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hr : ContDiff ℝ ∞ r := by
    convert! hA.sub hq using 1
    funext y
    dsimp only [A]
    ring
  have hsplit : m62ArcDerivative F c t A x =
      m62ArcDerivative F c t r x + m62ArcDerivative F c t q x := by
    have hd : HasDerivAt A (deriv r x + deriv q x) x :=
      ((hr.differentiable (by simp) x).hasDerivAt).add
      ((hq.differentiable (by simp) x).hasDerivAt)
    rw [m62ArcDerivative, hd.deriv]
    dsimp only [m62ArcDerivative]
    ring
  have hqarc : m62ArcDerivative F c t q x = 2 * g.inner p H B := by
    have hHsmooth := curvatureJet_joint_contMDiff F c hc 0
    have h := m63ArcDerivative_metric_pairing F c hc
      (fun z => m63CurvatureJet F c 0 z.2 z.1)
      (fun z => m63CurvatureJet F c 0 z.2 z.1) hHsmooth hHsmooth ht x
    change m62ArcDerivative F c t q x = g.inner p B H + g.inner p H B at h
    rw [g.symm p B H] at h
    linarith
  have hrarc : m62ArcDerivative F c t r x =
      D.covariantTensorDerivative D.ricciEvaluation p ![S, S, S] +
        2 * D.ricci p H S := (m63TangentRicci_arc_derivatives F c hc ht x).1
  have hdx : v * m62ArcDerivative F c t A x = deriv A x := by
    dsimp only [m62ArcDerivative]
    change v * (v⁻¹ * deriv A x) = deriv A x
    rw [← mul_assoc, mul_inv_cancel₀ hv.ne', one_mul]
  have hDer : |D.covariantTensorDerivative D.ricciEvaluation p ![S, S, S]| ≤ K1 := by
    apply hBounds.ricci_derivative t ht' p
    intro i
    fin_cases i <;> simpa [g] using hS.le
  have hRic : |D.ricci p H S| ≤ K2 * k := by
    have h := tensor_abs_le_of_unit_bound g D.ricciEvaluation
      (M04.isSmoothCovariantTensor_ricciEvaluation D) p
      (fun w hw => hBounds.ricci t ht' p (w 0) (w 1) (hw 0) (hw 1)) ![H, S]
    simpa [LeviCivitaData.ricciEvaluation, Fin.prod_univ_succ, hH, hS] using h
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hn (Z : TangentSpace (𝓡 n) p) : ‖Z‖ = g.tangentNorm p Z := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hN : |g.inner p H B| ≤ k * u := by
    change |inner ℝ H B| ≤ k * u
    simpa only [hn, hH, hB] using abs_real_inner_le_norm H B
  change |deriv A x| ≤ v * (K1 + 2 * K2 * k + 2 * k * u)
  rw [← hdx, hsplit, hrarc, hqarc, abs_mul, abs_of_pos hv]
  apply mul_le_mul_of_nonneg_left _ hv.le
  apply abs_le.mpr
  constructor
  · nlinarith only [(abs_le.mp hDer).1, (abs_le.mp hRic).1, (abs_le.mp hN).1]
  · nlinarith only [(abs_le.mp hDer).2, (abs_le.mp hRic).2, (abs_le.mp hN).2]

end PoincareConjecture.M63
