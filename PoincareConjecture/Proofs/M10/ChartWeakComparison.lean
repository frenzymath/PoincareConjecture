import PoincareConjecture.Proofs.M10.SemiconcaveWeakComparison
import PoincareConjecture.Proofs.M10.ChartNullPullback
import PoincareConjecture.Proofs.M10.LaplacianContinuity
import PoincareConjecture.Proofs.M10.SupportedIntegralTransport
import PoincareConjecture.Proofs.M10.SupportedPullbackIntegrable









set_option autoImplicit false

open Set Filter Metric MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]

noncomputable local instance chartWeakBilinearNormedAddCommGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance chartWeakBilinearNormedSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option backward.isDefEq.respectTransparency false in


theorem calibrated_weak_comparison_in_chart (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (q₀ : M) {u H φ : M → ℝ} (hu : Continuous u) (hH : Measurable H)
    {r K S A : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hS : 0 ≤ S) (_hA : 0 ≤ A)
    (htarget : ball (extChartAt (𝓡 n) q₀ q₀) (4 * r) ⊆ (extChartAt (𝓡 n) q₀).target)
    (hconc : ConcaveOn ℝ (ball (extChartAt (𝓡 n) q₀ q₀) (4 * r))
      (fun y ↦ u ((extChartAt (𝓡 n) q₀).symm y) - K * ‖y‖ ^ 2 / 2))
    (hcoeff : ∀ y ∈ ball (extChartAt (𝓡 n) q₀ q₀) (4 * r),
      ‖fderiv ℝ (pullbackMetricForm g (extChartAt (𝓡 n) q₀).symm) y‖ ≤ S ∧
      ‖(pullbackMetricForm g (extChartAt (𝓡 n) q₀).symm y).inverse‖ ≤ S ∧
      pullbackJacobian g (extChartAt (𝓡 n) q₀).symm y ≤ S ∧
      ‖fderiv ℝ (pullbackJacobian g (extChartAt (𝓡 n) q₀).symm) y‖ ≤ S)
    (hregular : ∀ᵐ q ∂calibratedMetricVolume g,
      ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 u q ∧ D.laplacian u q ≤ H q)
    (hbound : ∀ᵐ q ∂calibratedMetricVolume g,
      q ∈ (extChartAt (𝓡 n) q₀).source →
      extChartAt (𝓡 n) q₀ q ∈ ball (extChartAt (𝓡 n) q₀ q₀) (4 * r) → |H q| ≤ A)
    (hφ : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (extChartAt (𝓡 n) q₀).source ∩
      (extChartAt (𝓡 n) q₀) ⁻¹' ball (extChartAt (𝓡 n) q₀ q₀) r)
    (hpos : ∀ q, 0 ≤ φ q) :
    Integrable (fun q ↦ φ q * H q - u q * D.laplacian φ q) (calibratedMetricVolume g) ∧
      0 ≤ ∫ q, φ q * H q - u q * D.laplacian φ q ∂calibratedMetricVolume g := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) q₀
  let B := pullbackMetricForm g e.symm
  let ρ := pullbackJacobian g e.symm
  let uc := u ∘ e.symm
  let ψ := chartSupportedTest e φ
  let v := fun y ↦ LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
    (fderiv ℝ (weightedMetricDual B ρ ψ) y).toLinearMap
  have heT : (extChartAt (𝓡 n) q₀).target = e.target := by
    simp only [extChartAt_target, modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe,
      preimage_id, range_id, inter_univ, e]
  have heS : (extChartAt (𝓡 n) q₀).source = e.source := extChartAt_source _ _
  have hefun : ⇑(extChartAt (𝓡 n) q₀) = e := by
    simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp, e]
  have heinv : ⇑(extChartAt (𝓡 n) q₀).symm = e.symm := by
    simp only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id, e]
  simp only [hefun, heinv, heS, heT] at htarget hconc hcoeff hbound hs
  have he (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ e.target) :
      y ∈ (extChartAt (𝓡 n) q₀).target := heT.symm ▸ hy
  have hec : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target := contMDiffOn_chart_symm
  have heci : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source := contMDiffOn_chart
  have hB : ContDiffOn ℝ 1 B e.target := by
    simpa only [heT, heinv] using (chartMetricForm_contDiffOn g q₀).of_le
      (by decide : (1 : ℕ∞ω) ≤ ∞)
  have hρ : ContDiffOn ℝ 1 ρ e.target := by
    simpa only [heT, heinv] using (chartJacobian_contDiffOn g q₀).of_le
      (by decide : (1 : ℕ∞ω) ≤ ∞)
  have hsmall : ball (e q₀) r ⊆ ball (e q₀) (4 * r) := ball_subset_ball (by linarith)
  have hballT : ball (e q₀) (4 * r) ⊆ e.target := htarget
  have hscalar {f : M → ℝ} {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ e.target)
      (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f (e.symm y)) :
      ContDiffAt ℝ 2 (f ∘ e.symm) y := by
    have hf' : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f ((extChartAt (𝓡 n) q₀).symm y) :=
      heinv.symm ▸ hf
    simpa only [heinv] using fixedChart_scalar_contDiffAt q₀ (he y hy) hf'
  have hdiv {f : M → ℝ} {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ e.target)
      (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f (e.symm y)) :
      ρ y * D.laplacian f (e.symm y) = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        (fderiv ℝ (weightedMetricDual B ρ (f ∘ e.symm)) y).toLinearMap := by
    have hf' : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f ((extChartAt (𝓡 n) q₀).symm y) :=
      heinv.symm ▸ hf
    unfold weightedMetricDual
    simpa only [heinv] using chart_laplacian_divergence g D q₀ (he y hy) hf'
  have hsφ : tsupport φ ⊆ e.source := fun q hq ↦ (hs hq).1
  have hsψ := chartSupportedTest_support e hc hsφ
  have hψball : tsupport ψ ⊆ ball (e q₀) r := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := hsψ.2.1 hy
    exact (hs hq).2
  have hφ2 := hφ.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)
  have hψ : ContDiff ℝ 2 ψ := chartSupportedTest_contDiff e hc hsφ
    (fun y hy ↦ (hscalar hy (hφ2 (e.symm y))).contDiffWithinAt)
  have hψpos (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ ψ y := by
    by_cases hy : y ∈ e.target
    · simpa only [ψ, chartSupportedTest, indicator_of_mem hy, Function.comp_apply] using
        hpos (e.symm y)
    · simp only [ψ, chartSupportedTest, indicator_of_notMem hy, le_refl]
  have hregc := ae_calibrated_pullback g e.symm hec heci hρ.continuousOn hregular
  have hboundc := ae_calibrated_pullback g e.symm hec heci hρ.continuousOn hbound
  have hHprod : Integrable (fun y ↦ ψ y * (ρ y * H (e.symm y))) volume := by
    apply integrable_supported_pullback e (A := S * A)
      hψ.continuous hsψ.1 hsψ.2.2 hρ.continuousOn hH
    filter_upwards [hboundc] with y hy hys
    have hyball := hsmall (hψball hys)
    have hyT := hballT hyball
    have hHy : |H (e.symm y)| ≤ A :=
      hy hyT (e.map_target hyT) (by simpa only [e.right_inv hyT] using hyball)
    rw [abs_mul, abs_of_nonneg (pullbackJacobian_nonneg g e.symm y)]
    exact mul_le_mul (hcoeff y hyball).2.2.1 hHy (abs_nonneg _) hS
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ ball (e q₀) r) : (B y).IsInvertible := by
    apply positive_bilinear_isInvertible _
    intro v hv
    simpa only [heinv] using chartMetricForm_pos g q₀ (he y (hballT (hsmall hy))) hv
  have hframe (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ ball (e q₀) r) :
      ∃ C : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        ∀ v w, B y (C v) (C w) = inner ℝ v w := by
    have hD : (mfderiv (𝓡 n) (𝓡 n) e.symm y).IsInvertible := by
      exact (congrArg (fun f : EuclideanSpace ℝ (Fin n) → M ↦
        (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible) heinv).mp
        (inverseChart_mfderiv_isInvertible q₀ (he y (hballT (hsmall hy))))
    obtain ⟨C, hC⟩ := exists_pullback_source_normalization g hD
    refine ⟨C, fun v w ↦ ?_⟩
    change g.inner (e.symm y) (mfderiv (𝓡 n) (𝓡 n) e.symm y (C v))
      (mfderiv (𝓡 n) (𝓡 n) e.symm y (C w)) = _
    rw [hC, hC, metricCoordinates_inner]
  have hweak := integral_weighted_comparison_of_semiconcave (μ := volume)
    (EuclideanSpace.basisFun (Fin n) ℝ) hr hK hS
    (hu.continuousOn.comp (e.symm.continuousOn.mono hballT) (fun _ _ ↦ mem_univ _))
    hconc (hB.mono (hsmall.trans hballT)) (hρ.mono (hsmall.trans hballT)) hi
    (fun y _ v w ↦ g.symm _ _ _) hframe
    (fun y hy ↦ ⟨(hcoeff y (hsmall hy)).1, (hcoeff y (hsmall hy)).2.1,
      pullbackJacobian_nonneg g e.symm y, (hcoeff y (hsmall hy)).2.2⟩)
    (show ∀ᵐ y ∂volume, y ∈ ball (e q₀) r → ContDiffAt ℝ 2 uc y ∧
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        (fderiv ℝ (weightedMetricDual B ρ uc) y).toLinearMap ≤ ρ y * H (e.symm y) by
      filter_upwards [hregc] with y hy hyball
      have hyT := hballT (hsmall hyball)
      obtain ⟨huy, huH⟩ := hy hyT
      refine ⟨hscalar hyT huy, ?_⟩
      rw [← hdiv hyT huy]
      exact mul_le_mul_of_nonneg_left huH (pullbackJacobian_nonneg g e.symm y))
    hψ hsψ.1 hψball hψpos hHprod
  have hvsub : tsupport v ⊆ tsupport ψ :=
    (tsupport_trace_fderiv_subset _).trans (tsupport_weightedMetricDual_subset B ρ ψ)
  let a := fun y ↦ ψ y * (ρ y * H (e.symm y)) - uc y * v y
  have htransport := supported_calibrated_integral_transport g e.symm hec heci hρ.continuousOn
    (((hφ.continuous.measurable.mul hH).sub
      (hu.measurable.mul (continuous_laplacian D hφ2).measurable)).aestronglyMeasurable)
    (show ∀ q ∉ e.source, φ q * H q - u q * D.laplacian φ q = 0 by
      intro q hq
      have hqs : q ∉ tsupport φ := fun h ↦ hq (hsφ h)
      have hql : q ∉ tsupport (D.laplacian φ) := fun h ↦ hqs (tsupport_laplacian_subset D φ h)
      simp only [image_eq_zero_of_notMem_tsupport hqs, image_eq_zero_of_notMem_tsupport hql,
        zero_mul, mul_zero, sub_self])
    (hHprod.sub hweak.1)
    (show ∀ y ∉ e.target, a y = 0 by
      intro y hy
      have hys : y ∉ tsupport ψ := fun h ↦ hy (hsψ.2.2 h)
      have hyv : y ∉ tsupport v := fun h ↦ hys (hvsub h)
      simp only [a, image_eq_zero_of_notMem_tsupport hys, image_eq_zero_of_notMem_tsupport hyv,
        zero_mul, mul_zero, sub_self])
    (show ∀ y ∈ e.target, ρ y * (φ (e.symm y) * H (e.symm y) -
        u (e.symm y) * D.laplacian φ (e.symm y)) = a y by
      intro y hy
      have hψeq := chartSupportedTest_eventuallyEq e φ hy
      have hdual : weightedMetricDual B ρ ψ =ᶠ[𝓝 y] weightedMetricDual B ρ (φ ∘ e.symm) := by
        filter_upwards [hψeq.fderiv (𝕜 := ℝ)] with z hz
        simp only [weightedMetricDual, ψ, hz]
      have hv : v y = ρ y * D.laplacian φ (e.symm y) := by
        dsimp only [v]
        rw [hdual.fderiv_eq]
        exact (hdiv hy (hφ2 (e.symm y))).symm
      dsimp only [a, uc, Function.comp_apply]
      rw [hv, show ψ y = φ (e.symm y) from hψeq.eq_of_nhds]
      ring)
  refine ⟨htransport.1, ?_⟩
  have hint : (∫ q, φ q * H q - u q * D.laplacian φ q ∂calibratedMetricVolume g) = ∫ y, a y :=
    htransport.2
  rw [hint, integral_sub hHprod hweak.1]
  exact sub_nonneg.mpr hweak.2

end PoincareConjecture.M10
