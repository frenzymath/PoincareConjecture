import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ProductRicciTraceBound












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff BigOperators

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}



theorem auxiliaryCircle_ricci_quadratic_abs_le
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (hn : 1 ≤ n) (time : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (q : Q.charts.Point)
    (hcurv : (F.connection time).curvatureTensorNorm q.1.1 ≤ K)
    (v : TangentSpace (𝓡 ((n + 1) + 1)) q) :
    |(Q.flow.connection time).ricci q v v| ≤
      ((n : ℝ) - 1) * K * (Q.flow.metric time).inner q v v := by
  have hbase := m64CircleProduct_ricci_quadratic_abs_le P hn time hK q.1
    hcurv (Q.charts.split q v).1
  have hmetric : (P.flow.metric time).inner q.1
      (Q.charts.split q v).1 (Q.charts.split q v).1 ≤
      (Q.flow.metric time).inner q v v := by
    rw [Q.metric_eq]
    exact le_add_of_nonneg_right
      ((Q.circle.metricOnPoints.toRiemannianMetric.toCore q.2).re_inner_nonneg _)
  have hcoef : 0 ≤ ((n : ℝ) - 1) * K := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (sub_nonneg.mpr hn') hK
  rw [M62.circleProduct_ricci (P.flow.metric time) (P.flow.connection time)
    Q.circle Q.charts (Q.flow.metric time) (Q.flow.connection time) (Q.metric_eq time)]
  exact hbase.trans (mul_le_mul_of_nonneg_left hmetric hcoef)



theorem auxiliaryCircle_annulus_ricciTraceDensity_abs_le
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (hn : 1 ≤ n) (time : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection time).curvatureTensorNorm x ≤ K)
    (f : LoopPlane → Q.charts.Point) (z : LoopPlane) :
    |m64AnnulusRicciTraceDensity (Q.flow.connection time) f z| ≤
      2 * ((n : ℝ) - 1) * K * m60AreaDensity (Q.flow.metric time) f z := by
  let : RiemannianBundle (TangentSpace (𝓡 ((n + 1) + 1)) : Q.charts.Point → Type _) :=
    ⟨(Q.flow.metric time).toRiemannianMetric⟩
  let x := f z
  let d := mfderiv (𝓡 2) (𝓡 ((n + 1) + 1)) f z
  let v := fun i : Fin 2 => d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let G := m60AreaGram (Q.flow.metric time) f z
  have harea := m60AreaDensity_nonneg (Q.flow.metric time) f z
  have hcoef : 0 ≤ ((n : ℝ) - 1) * K := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (sub_nonneg.mpr hn') hK
  by_cases hdeg : Matrix.det G = 0
  · rw [m64AnnulusRicciTraceDensity_eq_zero (Q.flow.connection time) f z hdeg, abs_zero]
    nlinarith [mul_nonneg hcoef harea]
  have hpos : 0 < Matrix.det (Matrix.gram ℝ v) := by
    change 0 < Matrix.det (m60AreaGram (Q.flow.metric time) f z)
    exact lt_of_le_of_ne (m60AreaGram_det_nonneg (Q.flow.metric time) f z) (Ne.symm hdeg)
  obtain ⟨B, hB⟩ := m60Ricci_exists_bilinear (Q.flow.connection time)
    (Q.flow.connection time).curvatureTensorCalculus x
  have hbound (w : TangentSpace (𝓡 ((n + 1) + 1)) x) :
      |B w w| ≤ ((n : ℝ) - 1) * K * inner ℝ w w := by
    rw [hB]
    exact auxiliaryCircle_ricci_quadratic_abs_le P Q hn time hK x (hcurv x.1.1) w
  have htrace :
      |∑ i : Fin 2, ∑ j : Fin 2,
        (m60AreaGram (Q.flow.metric time) f z)⁻¹ i j *
          (Q.flow.connection time).ricci x (v j) (v i)| ≤
        2 * (((n : ℝ) - 1) * K) := by
    have h := M60.abs_inverse_gram_contraction_le v B hbound hpos
    change |∑ i : Fin 2, ∑ j : Fin 2,
      (m60AreaGram (Q.flow.metric time) f z)⁻¹ i j * B (v j) (v i)| ≤
      2 * (((n : ℝ) - 1) * K) at h
    simp_rw [hB] at h
    exact h
  unfold m64AnnulusRicciTraceDensity
  rw [if_neg hdeg, abs_mul, abs_of_nonneg harea]
  exact (mul_le_mul_of_nonneg_right htrace harea).trans_eq (by ring)



theorem auxiliaryCircle_annulus_ricciTraceIntegral_abs_le
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (hn : 1 ≤ n) (time : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection time).curvatureTensorNorm x ≤ K)
    (f : LoopPlane → Q.charts.Point)
    (harea : IntegrableOn (m60AreaDensity (Q.flow.metric time) f) m64AnnulusDomain volume)
    (htrace : IntegrableOn (m64AnnulusRicciTraceDensity (Q.flow.connection time) f)
      m64AnnulusDomain volume) :
    |-(∫ z in m64AnnulusDomain, m64AnnulusRicciTraceDensity (Q.flow.connection time) f z)| ≤
      2 * ((n : ℝ) - 1) * K * m64AnnulusArea (Q.flow.metric time) f := by
  rw [abs_neg]
  calc
    _ ≤ ∫ z in m64AnnulusDomain,
        ‖m64AnnulusRicciTraceDensity (Q.flow.connection time) f z‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm
          (m64AnnulusRicciTraceDensity (Q.flow.connection time) f)
          (μ := volume.restrict m64AnnulusDomain)
    _ ≤ ∫ z in m64AnnulusDomain,
        2 * ((n : ℝ) - 1) * K * m60AreaDensity (Q.flow.metric time) f z :=
      integral_mono htrace.norm (harea.const_mul _) (fun z => by
        simpa only [Real.norm_eq_abs] using
          auxiliaryCircle_annulus_ricciTraceDensity_abs_le P Q hn time hK hcurv f z)
    _ = _ := integral_const_mul _ _

end PoincareConjecture.M64
