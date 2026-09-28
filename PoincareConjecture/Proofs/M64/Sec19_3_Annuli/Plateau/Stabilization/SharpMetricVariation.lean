import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.ZeroDimensionalBase












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}



theorem auxiliaryCircle_annulus_ricciTraceDensity_supremum_le
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (hbounded : BddAbove (range (fun x : M => (F.connection time).curvatureTensorNorm x)))
    (f : LoopPlane → Q.charts.Point) (z : LoopPlane) :
    |m64AnnulusRicciTraceDensity (Q.flow.connection time) f z| ≤
      2 * ((n : ℝ) - 1) * m64CurvatureSupremum F time *
        m60AreaDensity (Q.flow.metric time) f z := by
  by_cases hn : n = 0
  · rw [auxiliaryCircle_annulus_ricciTraceDensity_eq_zero_of_dimension_zero P Q hn,
      curvatureSupremum_eq_zero_of_dimension_zero hn]
    simp
  · exact auxiliaryCircle_annulus_ricciTraceDensity_abs_le P Q
      (Nat.one_le_iff_ne_zero.mpr hn) time (m64CurvatureSupremum_nonneg hbounded)
      (m64Curvature_le_supremum hbounded) f z



theorem auxiliaryCircle_annulus_ricciTraceIntegral_supremum_le
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (hbounded : BddAbove (range (fun x : M => (F.connection time).curvatureTensorNorm x)))
    (f : LoopPlane → Q.charts.Point)
    (harea : IntegrableOn (m60AreaDensity (Q.flow.metric time) f) m64AnnulusDomain volume)
    (htrace : IntegrableOn (m64AnnulusRicciTraceDensity (Q.flow.connection time) f)
      m64AnnulusDomain volume) :
    |-(∫ z in m64AnnulusDomain, m64AnnulusRicciTraceDensity (Q.flow.connection time) f z)| ≤
      2 * ((n : ℝ) - 1) * m64CurvatureSupremum F time *
        m64AnnulusArea (Q.flow.metric time) f := by
  by_cases hn : n = 0
  · simp only [auxiliaryCircle_annulus_ricciTraceDensity_eq_zero_of_dimension_zero P Q hn,
      curvatureSupremum_eq_zero_of_dimension_zero hn, integral_zero, neg_zero, abs_zero,
      mul_zero, zero_mul, le_refl]
  · exact auxiliaryCircle_annulus_ricciTraceIntegral_abs_le P Q
      (Nat.one_le_iff_ne_zero.mpr hn) time (m64CurvatureSupremum_nonneg hbounded)
      (m64Curvature_le_supremum hbounded) f harea htrace



theorem auxiliaryCircle_annulus_area_variation_on_compact
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (hab : a < b) (hcompact : IsCompact (univ : Set M))
    (f : LoopPlane → Q.charts.Point)
    (hf : ContMDiff (𝓡 2) (𝓡 ((n + 1) + 1)) 1 f) :
    ∀ time ∈ Icc a b,
      IntegrableOn (m64AnnulusRicciTraceDensity (Q.flow.connection time) f)
        m64AnnulusDomain volume ∧
      HasDerivWithinAt (fun s => m64AnnulusArea (Q.flow.metric s) f)
        (-(∫ z in m64AnnulusDomain,
          m64AnnulusRicciTraceDensity (Q.flow.connection time) f z)) (Icc a b) time ∧
      |-(∫ z in m64AnnulusDomain,
          m64AnnulusRicciTraceDensity (Q.flow.connection time) f z)| ≤
        2 * ((n : ℝ) - 1) * m64CurvatureSupremum F time *
          m64AnnulusArea (Q.flow.metric time) f := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  have hcompactQ : IsCompact (univ : Set Q.charts.Point) := isCompact_univ
  intro time htime
  obtain ⟨htrace, hderiv, -⟩ :=
    m64AnnulusArea_variation_on_compact hab Q.flow hcompactQ f hf time htime
  have hbounded := m64CurvatureRange_bddAbove_of_compact (F := F) hcompact htime
  have harea : IntegrableOn (m60AreaDensity (Q.flow.metric time) f)
      m64AnnulusDomain volume :=
    (m60AreaDensity_continuous (Q.flow.metric time) hf).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact
  exact ⟨htrace, hderiv, auxiliaryCircle_annulus_ricciTraceIntegral_supremum_le P Q time
    hbounded f harea htrace⟩

end PoincareConjecture.M64
