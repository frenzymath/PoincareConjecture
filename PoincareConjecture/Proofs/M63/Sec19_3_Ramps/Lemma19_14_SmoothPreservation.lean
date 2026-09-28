import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Cor19_13_DegreePreservation
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Lemma19_14_RatioBound

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem m63SmoothRampPreservation
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hE : M62CurveEstimates P.flow c K0 K1 K2)
    (hramp : M63IsRampAt P (fun x => c x a) a) :
    M63RampPreservation P c b K0 K1 K2 := by
  have hpositive := m63SmoothRamp_preserved P c hc hBounds hramp
  have hu : ∀ t ∈ Set.Icc a b, ∀ x, 0 < m62Slope P c t x :=
    fun t ht => (m63IsRampAt_slice_iff P c t).mp (hpositive t ht)
  exact {
    positive := hpositive
    lower_slope := fun _ hm hinit => m63SmoothSlope_lower P c hc hBounds hm.le hinit
    degree_preserved := fun L _ ht => m63PositiveDegree_preserved P c hc.continuous
      hc.periodic hc.spatial_regular hpositive L ht
    ratio_time := fun _ hε _ ht x => m63RampRatio_differentiableAt_time P c hc hu hε ht x
    ratio_evolution := fun _ hε _ ht x =>
      m63SmoothRampRatio_evolution P c hc hBounds hE hu hε ht x
    ratio_bound := fun _ _ hm _ hinit hR =>
      m63SmoothRampRatio_bound P c hc h0 h1 h2 hBounds hE hm hinit hR
    curvature_bound := fun _ _ hm _ hinit hR =>
      m63SmoothRampCurvature_bound P c hc h0 h1 h2 hBounds hE hm hinit hR }

end PoincareConjecture
