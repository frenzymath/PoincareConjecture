import PoincareLib.Geometry.RicciFlow.Soliton.Flow.Generation
import PoincareLib.Geometry.RicciFlow.Soliton.Homothety
import PoincareLib.Geometry.RicciFlow.TimeTranslation
import PoincareLib.Geometry.RicciFlow.Rescaling.Positivity
import PoincareLib.Geometry.RicciFlow.AncientKappa.Basic
import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Measure
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Volume

/-!
# Ancient source for the noncompact shrinking-soliton limit

The generated flow is defined for negative times and need not extend through
zero. Translating it by one gives an actual ancient kappa-solution on `Iic 0`,
with the original normalized metric at time zero. All source properties are
transported from the static soliton by its homothetic diffeomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

noncomputable section

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

private theorem rescaled_norm (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (c : ℝ) (hc : 0 < c) (x : M) :
    (rescaledMetric_connection g D c hc).curvatureTensorNorm x =
      c⁻¹ * D.curvatureTensorNorm x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := (g.orthonormalBasis x).toBasis
  let G := Matrix.of (fun i j => g.inner x (b i) (b j))
  have hG : G = 1 := by
    ext i j
    exact (g.orthonormalBasis x).inner_eq_ite i j
  let D' := rescaledMetric_connection g D c hc
  obtain ⟨A, hA⟩ := D.curvatureTensor_multilinear x
  obtain ⟨A', hA'⟩ := D'.curvatureTensor_multilinear x
  rw [D'.curvatureTensorNorm_eq_tensorNormFromComponents x b A' hA',
    D.curvatureTensorNorm_eq_tensorNormFromComponents x b A hA]
  have hgram : Matrix.of (fun i j => (rescaledMetric g c hc).inner x (b i) (b j)) =
      c • G := rfl
  have hinv : (c • G)⁻¹ = c⁻¹ • G⁻¹ := by
    rw [hG]
    apply Matrix.inv_eq_right_inv
    simp [smul_smul, hc.ne']
  simp only [hgram, tensorNormFromComponents, hinv, Matrix.smul_apply, smul_eq_mul,
    D', rescaledMetric_curvatureTensor]
  have heq (i j : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      (∏ r, c⁻¹ * G⁻¹ (i r) (j r)) *
          (c * D.curvatureTensor x (b (i 0)) (b (i 1)) (b (i 2)) (b (i 3)) *
            (c * D.curvatureTensor x (b (j 0)) (b (j 1)) (b (j 2)) (b (j 3)))) =
        (c⁻¹) ^ 2 * ((∏ r, G⁻¹ (i r) (j r)) *
          (D.curvatureTensor x (b (i 0)) (b (i 1)) (b (i 2)) (b (i 3)) *
            D.curvatureTensor x (b (j 0)) (b (j 1)) (b (j 2)) (b (j 3)))) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  simp_rw [heq, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hc.le)]

namespace HomotheticMetricSlice

variable {g h : RiemannianMetric 3 M} {c : ℝ}

theorem curvatureNorm (E : HomotheticMetricSlice g h c) (hc : 0 < c)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) :
    D'.curvatureTensorNorm x = c⁻¹ * D.curvatureTensorNorm (E.map x) := by
  rw [← rescaled_norm g D c hc]
  exact D'.curvatureTensorNorm_eq_of_local_isometry
    (rescaledMetric_connection g D c hc) isOpen_univ
    E.map.contMDiff.contMDiffOn (fun y _ u v => E.inner_eq y u v) (mem_univ x)

theorem nonnegativeCurvatureOperator (E : HomotheticMetricSlice g h c) (hc : 0 < c)
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hD : ∀ x, D.NonnegativeCurvatureOperator x) (x : M) :
    D'.NonnegativeCurvatureOperator x := by
  apply (D'.nonnegativeCurvatureOperator_iff_of_local_isometry
    (rescaledMetric_connection g D c hc) isOpen_univ
    E.map.contMDiff.contMDiffOn (fun y _ u v => E.inner_eq y u v) (mem_univ x)).mpr
  exact rescaledMetric_nonnegativeCurvatureOperator g D c hc _ (hD _)

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem kappaNoncollapsed (E : HomotheticMetricSlice g h c) (hc : 0 < c)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {κ : ℝ}
    (hκ : MetricKappaNoncollapsed g D κ) : MetricKappaNoncollapsed h D' κ := by
  refine ⟨hκ.1, fun p r hr hbound => ?_⟩
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hb : E.map '' h.ball p r = g.ball (E.map p) (r / Real.sqrt c) := by
    rw [RiemannianMetric.image_ball_diffeomorph h (rescaledMetric g c hc)
      E.map (fun y u v => E.inner_eq y u v), rescaledMetric_ball]
  have hbase := hκ.2 (E.map p) (r / Real.sqrt c) (div_pos hr hs) (by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := hb.symm ▸ hq
    have h := hbound y hy
    rw [E.curvatureNorm hc D D', abs_mul, abs_of_pos (inv_pos.mpr hc)] at h
    have hpow : (r / Real.sqrt c)⁻¹ ^ 2 = c * r⁻¹ ^ 2 := by
      rw [inv_div, div_pow, Real.sq_sqrt hc.le]
      simp only [div_eq_mul_inv, inv_pow]
    rw [hpow]
    calc
      |D.curvatureTensorNorm (E.map y)| = c * (c⁻¹ * |D.curvatureTensorNorm (E.map y)|) := by
        rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
      _ ≤ c * r⁻¹ ^ 2 := mul_le_mul_of_nonneg_left h hc.le)
  have hvol : calibratedMetricVolume h (h.ball p r) =
      ENNReal.ofReal (Real.sqrt c) ^ 3 *
        calibratedMetricVolume g (g.ball (E.map p) (r / Real.sqrt c)) := by
    simp only [calibratedMetricVolume_eq_volumeMeasure]
    rw [RiemannianMetric.volumeMeasure_ball_diffeomorph h (rescaledMetric g c hc)
      E.map (fun y u v => E.inner_eq y u v), rescaledMetric_ball,
      rescaledMetric_volumeMeasure, Measure.smul_apply, smul_eq_mul]
  rw [hvol]
  calc
    ENNReal.ofReal (κ * r ^ 3) = ENNReal.ofReal (Real.sqrt c) ^ 3 *
        ENNReal.ofReal (κ * (r / Real.sqrt c) ^ 3) := by
      rw [← ENNReal.ofReal_pow hs.le, ← ENNReal.ofReal_mul (pow_nonneg hs.le _)]
      congr 1
      field_simp
    _ ≤ _ := by gcongr

end HomotheticMetricSlice

variable [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

namespace ShrinkingSolitonFlow

variable {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)

/-- Time zero is the regular normalized slice of the generated flow. -/
def ancientSourceFlow : RicciFlow 3 M (Iic 0) :=
  G.flow.translate (-1)
    (by rintro _ ⟨t, ht, rfl⟩; change t + -1 < 0; linarith [show t ≤ 0 from ht])
    ordConnected_Iic ⟨-1, by simp, 0, by simp, by norm_num⟩

theorem ancientSourceFlow_metric_zero : G.ancientSourceFlow.metric 0 = S.metric := by
  simpa only [ancientSourceFlow, RicciFlow.translate, zero_add] using G.at_minus_one

/-- The whole ancient source has the original static curvature bound. -/
theorem ancientSourceFlow_uniformCurvatureBound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, t ≤ 0 → ∀ x : M,
      |(G.ancientSourceFlow.connection t).curvatureTensorNorm x| ≤ B := by
  obtain ⟨B, hB, hbound⟩ := S.bounded_curvature
  refine ⟨B, hB, fun t ht x => ?_⟩
  have ht' : t + -1 < 0 := by linarith
  have hc : 0 < |t + -1| := abs_pos.mpr ht'.ne
  have hc1 : 1 ≤ |t + -1| := by rw [abs_of_neg ht']; linarith
  obtain ⟨E⟩ := G.self_similar (t + -1) ht'
  change |(G.flow.connection (t + -1)).curvatureTensorNorm x| ≤ B
  rw [E.curvatureNorm hc S.connection, abs_mul, abs_of_pos (inv_pos.mpr hc)]
  calc
    |t + -1|⁻¹ * |S.connection.curvatureTensorNorm (E.map x)| ≤
        |t + -1|⁻¹ * B := mul_le_mul_of_nonneg_left (hbound _) (inv_nonneg.mpr hc.le)
    _ ≤ B := by
      have hinv : |t + -1|⁻¹ ≤ 1 := (inv_le_one₀ hc).mpr hc1
      nlinarith

/-- The source is constructed from the frozen static soliton hypotheses. -/
def ancientSource : AncientKappaSolution 3 M where
  flow := G.ancientSourceFlow
  kappa := S.kappa
  kappa_pos := S.kappa_pos
  complete := by
    intro t ht
    obtain ⟨E⟩ := G.self_similar (t + -1) (by linarith)
    exact E.metricComplete (abs_pos.mpr (by linarith)) S.complete
  nonnegative_curvature_operator := by
    intro t ht x
    obtain ⟨E⟩ := G.self_similar (t + -1) (by linarith)
    exact E.nonnegativeCurvatureOperator (abs_pos.mpr (by linarith))
      S.connection (G.flow.connection (t + -1)) S.nonnegative_curvature x
  bounded_curvature := by
    intro t ht
    obtain ⟨B, hB, hbound⟩ := G.ancientSourceFlow_uniformCurvatureBound
    exact ⟨B, hB, hbound t ht⟩
  nonflat := by
    intro t ht
    obtain ⟨E⟩ := G.self_similar (t + -1) (by linarith)
    obtain ⟨x, hx⟩ := S.nonflat
    refine ⟨E.map.symm x, ?_⟩
    change (G.flow.connection (t + -1)).curvatureTensorNorm (E.map.symm x) ≠ 0
    rw [E.curvatureNorm (abs_pos.mpr (by linarith)) S.connection,
      E.map.apply_symm_apply]
    exact mul_ne_zero (inv_ne_zero (abs_pos.mpr (by linarith)).ne') hx
  noncollapsed := by
    intro r₀ hr₀ t ht p r hr hrr₀ hbound
    obtain ⟨E⟩ := G.self_similar (t + -1) (by linarith)
    have hκ := E.kappaNoncollapsed (abs_pos.mpr (by linarith)) S.connection
      (G.flow.connection (t + -1)) S.kappa_noncollapsed
    apply hκ.2 p r hr
    exact hbound t ⟨by nlinarith [sq_pos_of_pos hr], le_rfl⟩

theorem ancientSource_metric_zero : G.ancientSource.flow.metric 0 = S.metric :=
  G.ancientSourceFlow_metric_zero

end ShrinkingSolitonFlow

/-- No ancient flow or source compatibility hypothesis is required. -/
theorem GradientShrinkingSolitonData.exists_ancientSource
    (S : GradientShrinkingSolitonData 3 M) :
    ∃ K : AncientKappaSolution 3 M, K.flow.metric 0 = S.metric ∧ K.kappa = S.kappa := by
  obtain ⟨G⟩ := exists_shrinkingSolitonFlow S
  exact ⟨G.ancientSource, G.ancientSource_metric_zero, rfl⟩

end PoincareMT
