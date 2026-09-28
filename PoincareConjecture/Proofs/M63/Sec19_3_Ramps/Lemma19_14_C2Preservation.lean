import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.C2RatioBound
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Cor19_13_DegreePreservation











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M63




theorem c2_rampPreservation
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b T : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (hlocal : M63LocalCurveTheory P.flow)
    (c : ℝ → ℝ → P.charts.Point) (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T))
    (hT : a < T) {K0 K1 K2 : ℝ} (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hE : M63C2CurveEstimates P.flow c T K0 K1 K2)
    (hramp : M63IsRampAt P (fun x => c x a) a) :
    M63RampPreservation P c T K0 K1 K2 := by
  have hpositive := c2_ramp_preserved P hlocal c hc hT hBounds hramp
  have hu : ∀ t ∈ Icc a T, ∀ x, 0 < m62Slope P c t x :=
    fun t ht => (m63IsRampAt_slice_iff P c t).mp (hpositive t ht)
  have hS := c2_slope_laws_of_local P hlocal hBounds c hc hT
  exact {
    positive := hpositive
    lower_slope := fun _ hm hinit => c2_slope_lower P hlocal c hc hT hBounds hm.le hinit
    degree_preserved := fun L _ ht => m63PositiveDegree_preserved P c hc.continuous
      hc.periodic hc.spatial_regular hpositive L ht
    ratio_time := fun _ hepsilon _ ht x => c2_rampRatio_differentiableAt_time P c hE hS
      hepsilon ht x (hu _ (Ioo_subset_Icc_self ht) x).ne'
    ratio_evolution := fun _ hepsilon _ ht x =>
      c2_rampRatio_evolution P hlocal c hc hT hBounds hE hu hepsilon ht x
    ratio_bound := fun _ _ hm _ hinit hR =>
      c2_rampRatio_bound P hlocal c hc hT h0 h1 h2 hBounds hE hm hinit hR
    curvature_bound := fun _ _ hm _ hinit hR =>
      c2_rampCurvature_bound P hlocal c hc hT h0 h1 h2 hBounds hE hm hinit hR }

end PoincareConjecture.M63
