import PoincareConjecture.Proofs.M62.Lemma0_4_RegularizationError
import PoincareConjecture.Proofs.M62.Mathlib.ParameterIntegral










set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)



theorem metric_pairing_continuousOn
    (hc : ContinuousOn (fun z : ℝ × ℝ ↦ c z.1 z.2) (Set.univ ×ˢ Set.Icc a b))
    (Y Z : ∀ z : ℝ × ℝ, TangentSpace (𝓡 n) (c z.1 z.2))
    (hY : ContinuousOn (fun z : ℝ × ℝ ↦
      (⟨c z.1 z.2, Y z⟩ : TangentBundle (𝓡 n) M)) (Set.univ ×ˢ Set.Icc a b))
    (hZ : ContinuousOn (fun z : ℝ × ℝ ↦
      (⟨c z.1 z.2, Z z⟩ : TangentBundle (𝓡 n) M)) (Set.univ ×ˢ Set.Icc a b)) :
    ContinuousOn (fun z : ℝ × ℝ ↦ (F.metric z.2).inner (c z.1 z.2) (Y z) (Z z))
      (Set.univ ×ˢ Set.Icc a b) := by
  have hg := F.smooth.continuousOn.comp
    (continuous_snd.continuousOn.prodMk hc) (fun z hz ↦ ⟨hz.2, Set.mem_univ _⟩)
  intro z hz
  have hp : ContinuousWithinAt
      (fun w : ℝ × ℝ ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
        (c w.1 w.2) ((F.metric w.2).inner (c w.1 w.2) (Y w) (Z w)))
      (Set.univ ×ˢ Set.Icc a b) z :=
    (hg z hz).clm_bundle_apply₂ (hY z hz) (hZ z hz)
  rw [FiberBundle.continuousWithinAt_totalSpace] at hp
  exact hp.2



theorem speed_continuousOn (hc : M62ShrinkingCurve F c) :
    ContinuousOn (fun z : ℝ × ℝ ↦ curveSpeed F c z.2 z.1)
      (Set.univ ×ˢ Set.Icc a b) := by
  exact (metric_pairing_continuousOn F c hc.continuous _ _
    hc.velocity_continuous hc.velocity_continuous).sqrt



theorem curvatureSquared_continuousOn (hc : M62ShrinkingCurve F c) :
    ContinuousOn (fun z : ℝ × ℝ ↦ m62CurvatureSquared F c z.2 z.1)
      (Set.univ ×ˢ Set.Icc a b) := by
  exact metric_pairing_continuousOn F c hc.continuous _ _
    hc.curvature_continuous hc.curvature_continuous


theorem curvature_continuousOn (hc : M62ShrinkingCurve F c) :
    ContinuousOn (fun z : ℝ × ℝ ↦ m62Curvature F c z.2 z.1)
      (Set.univ ×ˢ Set.Icc a b) :=
  (curvatureSquared_continuousOn F c hc).sqrt



theorem regularized_continuousOn (hc : M62ShrinkingCurve F c) (ε : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ ↦ m62RegularizedCurvature F c ε z.2 z.1)
      (Set.univ ×ˢ Set.Icc a b) :=
  ((curvatureSquared_continuousOn F c hc).add continuousOn_const).sqrt



theorem length_integrable (hc : M62ShrinkingCurve F c) {t : ℝ}
    (ht : t ∈ Set.Icc a b) :
    IntervalIntegrable (curveSpeed F c t) MeasureTheory.volume 0 curvePeriod := by
  have hcont : Continuous (curveSpeed F c t) :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ ↦ ⟨Set.mem_univ _, ht⟩)
  exact hcont.intervalIntegrable _ _



theorem total_curvature_integrable (hc : M62ShrinkingCurve F c) {t : ℝ}
    (ht : t ∈ Set.Icc a b) :
    IntervalIntegrable (fun x ↦ m62Curvature F c t x * curveSpeed F c t x)
      MeasureTheory.volume 0 curvePeriod := by
  have hcont : Continuous (fun x ↦ m62Curvature F c t x * curveSpeed F c t x) :=
    ((curvature_continuousOn F c hc).mul (speed_continuousOn F c hc)).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ ↦ ⟨Set.mem_univ _, ht⟩)
  exact hcont.intervalIntegrable _ _



theorem regularized_integrable (hc : M62ShrinkingCurve F c) (ε : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc a b) :
    IntervalIntegrable (fun x ↦ m62RegularizedCurvature F c ε t x * curveSpeed F c t x)
      MeasureTheory.volume 0 curvePeriod := by
  have hcont : Continuous
      (fun x ↦ m62RegularizedCurvature F c ε t x * curveSpeed F c t x) :=
    ((regularized_continuousOn F c hc ε).mul (speed_continuousOn F c hc)).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ ↦ ⟨Set.mem_univ _, ht⟩)
  exact hcont.intervalIntegrable _ _



theorem length_continuous (hc : M62ShrinkingCurve F c) :
    ContinuousOn (m62Length F c) (Set.Icc a b) :=
  (speed_continuousOn F c hc).intervalIntegral_prod_left 0 curvePeriod



theorem total_curvature_continuous (hc : M62ShrinkingCurve F c) :
    ContinuousOn (m62TotalCurvature F c) (Set.Icc a b) :=
  ((curvature_continuousOn F c hc).mul (speed_continuousOn F c hc)).intervalIntegral_prod_left
    0 curvePeriod



theorem regularized_total_continuous (hc : M62ShrinkingCurve F c) (ε : ℝ) :
    ContinuousOn (m62RegularizedTotalCurvature F c ε) (Set.Icc a b) :=
  ((regularized_continuousOn F c hc ε).mul (speed_continuousOn F c hc)).intervalIntegral_prod_left
    0 curvePeriod



theorem shrinkingCurve_regularization_error (hc : M62ShrinkingCurve F c)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc a b) :
    0 ≤ m62RegularizedTotalCurvature F c ε t - m62TotalCurvature F c t ∧
      m62RegularizedTotalCurvature F c ε t - m62TotalCurvature F c t ≤
        ε * m62Length F c t :=
  regularization_error F c hε (length_integrable F c hc ht)
    (total_curvature_integrable F c hc ht) (regularized_integrable F c hc ε ht)

end PoincareConjecture.M62
