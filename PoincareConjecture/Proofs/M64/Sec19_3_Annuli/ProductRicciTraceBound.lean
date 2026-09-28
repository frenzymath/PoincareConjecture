import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FixedMapVariation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Bounds.Ricci
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductRicci

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

private theorem areaGram_det_eq_zero_of_dimension_lt_two
    (hn : n < 2) (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) :
    Matrix.det (m60AreaGram g f z) = 0 := by
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f z)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) (f z)
  by_contra hdet
  have hdim := ((m60AreaGram_det_ne_zero_iff g f z).mp hdet).fintype_card_le_finrank
  have hfinrank : Module.finrank ℝ (TangentSpace (𝓡 n) (f z)) = n := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simp
  rw [Fintype.card_fin, hfinrank] at hdim
  omega

variable [T2Space M] {a b : ℝ} {F : RicciFlow n M (Icc a b)}
  {circumference : ℝ}

theorem m64CircleProduct_ricci_quadratic_abs_le
    (P : M62.CircleProductData F circumference)
    (hn : 1 ≤ n) (t : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (q : P.charts.Point)
    (hcurv : (F.connection t).curvatureTensorNorm q.1 ≤ K)
    (v : TangentSpace (𝓡 (n + 1)) q) :
    |(P.flow.connection t).ricci q v v| ≤
      ((n : ℝ) - 1) * K * (P.flow.metric t).inner q v v := by
  have hsec (u w : TangentSpace (𝓡 n) q.1) :
      |(F.connection t).sectionalCurvature q.1 u w| ≤ K :=
    ((F.connection t).abs_sectionalCurvature_le_curvatureTensorNorm q.1 u w).trans hcurv
  have hbase := (F.connection t).abs_ricci_quadratic_le_of_abs_sectionalCurvature_le
    q.1 K hsec (P.charts.split q v).1
  have hmetric :
      (F.metric t).inner q.1 (P.charts.split q v).1 (P.charts.split q v).1 ≤
        (P.flow.metric t).inner q v v := by
    rw [P.metric_eq]
    exact le_add_of_nonneg_right
      ((P.circle.metricOnPoints.toRiemannianMetric.toCore q.2).re_inner_nonneg _)
  have hcoef : 0 ≤ ((n : ℝ) - 1) * K := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (sub_nonneg.mpr hn') hK
  rw [M62.circleProduct_ricci (F.metric t) (F.connection t) P.circle P.charts
    (P.flow.metric t) (P.flow.connection t) (P.metric_eq t)]
  exact hbase.trans (mul_le_mul_of_nonneg_left hmetric hcoef)

theorem m64CircleProductAnnulusRicciTraceDensity_abs_le
    (P : M62.CircleProductData F circumference)
    (t : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    (f : LoopPlane → P.charts.Point) (z : LoopPlane) :
    |m64AnnulusRicciTraceDensity (P.flow.connection t) f z| ≤
      2 * ((n : ℝ) - 1) * K * m60AreaDensity (P.flow.metric t) f z := by
  by_cases hn : n = 0
  · have hdim : n + 1 < 2 := by omega
    have hdeg := areaGram_det_eq_zero_of_dimension_lt_two hdim (P.flow.metric t) f z
    rw [m64AnnulusRicciTraceDensity_eq_zero (P.flow.connection t) f z hdeg,
      m60AreaDensity_eq_zero_of_det_eq_zero (P.flow.metric t) (P.flow.metric t) f z hdeg]
    simp
  have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
    ⟨(P.flow.metric t).toRiemannianMetric⟩
  let x := f z
  let d := mfderiv (𝓡 2) (𝓡 (n + 1)) f z
  let v := fun i : Fin 2 => d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let G := m60AreaGram (P.flow.metric t) f z
  have harea := m60AreaDensity_nonneg (P.flow.metric t) f z
  have hcoef : 0 ≤ ((n : ℝ) - 1) * K := by
    have hn'' : (1 : ℝ) ≤ n := by exact_mod_cast hn'
    exact mul_nonneg (sub_nonneg.mpr hn'') hK
  by_cases hdeg : Matrix.det G = 0
  · rw [m64AnnulusRicciTraceDensity_eq_zero (P.flow.connection t) f z hdeg, abs_zero]
    nlinarith [mul_nonneg hcoef harea]
  have hpos : 0 < Matrix.det (Matrix.gram ℝ v) := by
    change 0 < Matrix.det (m60AreaGram (P.flow.metric t) f z)
    exact lt_of_le_of_ne (m60AreaGram_det_nonneg (P.flow.metric t) f z) (Ne.symm hdeg)
  obtain ⟨B, hB⟩ := m60Ricci_exists_bilinear (P.flow.connection t)
    (P.flow.connection t).curvatureTensorCalculus x
  have hbound (w : TangentSpace (𝓡 (n + 1)) x) :
      |B w w| ≤ ((n : ℝ) - 1) * K * inner ℝ w w := by
    rw [hB]
    exact m64CircleProduct_ricci_quadratic_abs_le P hn' t hK x (hcurv x.1) w
  have htrace :
      |∑ i : Fin 2, ∑ j : Fin 2,
        (m60AreaGram (P.flow.metric t) f z)⁻¹ i j *
          (P.flow.connection t).ricci x (v j) (v i)| ≤
        2 * (((n : ℝ) - 1) * K) := by
    have h := M60.abs_inverse_gram_contraction_le v B hbound hpos
    change |∑ i : Fin 2, ∑ j : Fin 2,
      (m60AreaGram (P.flow.metric t) f z)⁻¹ i j * B (v j) (v i)| ≤
      2 * (((n : ℝ) - 1) * K) at h
    simp_rw [hB] at h
    exact h
  unfold m64AnnulusRicciTraceDensity
  rw [if_neg hdeg, abs_mul, abs_of_nonneg harea]
  exact (mul_le_mul_of_nonneg_right htrace harea).trans_eq (by ring)

theorem m64CircleProductAnnulusRicciTraceIntegral_abs_le
    (P : M62.CircleProductData F circumference)
    (t : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    (f : LoopPlane → P.charts.Point)
    (harea : IntegrableOn (m60AreaDensity (P.flow.metric t) f)
      m64AnnulusDomain volume)
    (htrace : IntegrableOn (m64AnnulusRicciTraceDensity (P.flow.connection t) f)
      m64AnnulusDomain volume) :
    |-(∫ z in m64AnnulusDomain, m64AnnulusRicciTraceDensity (P.flow.connection t) f z)| ≤
      2 * ((n : ℝ) - 1) * K * m64AnnulusArea (P.flow.metric t) f := by
  rw [abs_neg]
  calc
    _ ≤ ∫ z in m64AnnulusDomain,
        ‖m64AnnulusRicciTraceDensity (P.flow.connection t) f z‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm
          (m64AnnulusRicciTraceDensity (P.flow.connection t) f)
          (μ := volume.restrict m64AnnulusDomain)
    _ ≤ ∫ z in m64AnnulusDomain,
        2 * ((n : ℝ) - 1) * K * m60AreaDensity (P.flow.metric t) f z :=
      integral_mono htrace.norm (harea.const_mul _) (fun z => by
        simpa only [Real.norm_eq_abs] using
          m64CircleProductAnnulusRicciTraceDensity_abs_le P t hK hcurv f z)
    _ = _ := integral_const_mul _ _

theorem m64CircleProductAnnulusArea_variation_on_compact
    (hab : a < b) (hcompact : IsCompact (univ : Set M))
    (hcirc : 0 < circumference) (P : M62.CircleProductData F circumference)
    (f : LoopPlane → P.charts.Point) (hf : ContMDiff (𝓡 2) (𝓡 (n + 1)) 1 f) :
    ∀ t ∈ Icc a b,
      IntegrableOn (m64AnnulusRicciTraceDensity (P.flow.connection t) f)
        m64AnnulusDomain volume ∧
      HasDerivWithinAt (fun s => m64AnnulusArea (P.flow.metric s) f)
        (-(∫ z in m64AnnulusDomain,
          m64AnnulusRicciTraceDensity (P.flow.connection t) f z)) (Icc a b) t ∧
      |-(∫ z in m64AnnulusDomain,
          m64AnnulusRicciTraceDensity (P.flow.connection t) f z)| ≤
        2 * ((n : ℝ) - 1) * m64CurvatureSupremum F t *
          m64AnnulusArea (P.flow.metric t) f := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Fact (0 < circumference) := ⟨hcirc⟩
  have hcompactP : IsCompact (univ : Set P.charts.Point) := isCompact_univ
  intro t ht
  obtain ⟨htrace, hderiv, _⟩ :=
    m64AnnulusArea_variation_on_compact hab P.flow hcompactP f hf t ht
  have hbounded := m64CurvatureRange_bddAbove_of_compact (F := F) hcompact ht
  have harea : IntegrableOn (m60AreaDensity (P.flow.metric t) f)
      m64AnnulusDomain volume :=
    (m60AreaDensity_continuous (P.flow.metric t) hf).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact
  exact ⟨htrace, hderiv, m64CircleProductAnnulusRicciTraceIntegral_abs_le P t
    (m64CurvatureSupremum_nonneg hbounded) (m64Curvature_le_supremum hbounded)
    f harea htrace⟩

end PoincareConjecture
