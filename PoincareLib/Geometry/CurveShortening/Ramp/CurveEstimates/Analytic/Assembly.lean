import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.C2.EstimatesFromLocal
import PoincareLib.Geometry.CurveShortening.Ramp.Slope.Existence.FromLocal
import PoincareLib.Geometry.CurveShortening.Ramp.Slope.C2.Preservation
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Polygon.Estimates
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Sampled.PolygonLength
import PoincareLib.Geometry.CurveShortening.Ramp.Estimates

/-!
# Analytic assembly for one fixed ambient geometry

M62 and the proved C2, ramp and polygon helpers fill the analytic record
from actual local theories and actual uniform derivative estimates.
The supplied geometry and constants are retained. Claim 19.1,
Corollary 19.13, Lemma 19.14 and Claims 19.19/19.22, MT2007
pp. 437, 446-447, 450-453; corrected estimates, MT2015Correction
pp. 6-9. See `2026-09-21-analytic-assembly.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- For the exact supplied geometry, actual local theories and uniform
jets imply every frozen analytic field by the proved M62 and M63 helpers.
This is conditional assembly, not construction of those two inputs.
MT2007 pp. 437, 446-453; correction pp. 6-9. -/
theorem m63AnalyticConclusion_of_local_uniform
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    (hM62 : M62CurveEvolutionTheory.{u}) (G : M63AmbientGeometry F)
    (hbase : M63LocalCurveTheory F)
    (hproduct : ∀ circumference (h : 0 < circumference),
      M63LocalCurveTheory (G.product circumference h).flow)
    (huniform : ∀ L0 Theta0 : ℝ, 0 ≤ L0 → 0 ≤ Theta0 →
      Nonempty (M63UniformDerivativeEstimates G L0 Theta0)) :
    M63AnalyticConclusion F G := by
  let : CompactSpace M := ⟨hcompact⟩
  have hprod (circumference : ℝ) (h : 0 < circumference)
      (T : ℝ) (hT : a < T) (_hTb : T ≤ b)
      (c : ℝ → ℝ → (G.product circumference h).charts.Point)
      (hc : M63C2ShrinkingCurveOn (G.product circumference h).flow c (Icc a T)) :
      M63C2CurveEstimates (G.product circumference h).flow c T G.K0 G.K1 G.K2 := by
    let : Fact (0 < circumference) := ⟨h⟩
    exact M63.c2_estimates_of_local hM62 (G.product circumference h).flow isCompact_univ
      (hproduct circumference h) G.nonnegative.1 G.nonnegative.2.1 G.nonnegative.2.2
      (G.product_bounds circumference h) c hc hT
  exact
    { local_base := hbase
      local_product := hproduct
      base_estimates := fun _ hT _ c hc => M63.c2_estimates_of_local hM62 F hcompact
        hbase G.nonnegative.1 G.nonnegative.2.1 G.nonnegative.2.2 G.bounds c hc hT
      product_estimates := hprod
      slope := fun circumference h _ hT _ c hc =>
        M63.c2_slope_laws_of_local (G.product circumference h) (hproduct circumference h)
          (G.product_bounds circumference h) c hc hT
      positive_degree := fun circumference h gamma hper hreg _ _ hramp =>
        m63PositiveDegreeLift_nonempty (G.product circumference h) gamma hper hreg hramp
      preservation := fun circumference h T hT hTb c hc hramp =>
        M63.c2_rampPreservation (G.product circumference h) (hproduct circumference h)
          c hc hT G.nonnegative.1 G.nonnegative.2.1 G.nonnegative.2.2
          (G.product_bounds circumference h) (hprod circumference h T hT hTb c hc) hramp
      c2_ramp_existence := fun circumference h =>
        M63.c2_ramp_existence_of_local (G.product circumference h) (hproduct circumference h)
          G.nonnegative.1 G.nonnegative.2.1 G.nonnegative.2.2
          (G.product_bounds circumference h) (hprod circumference h)
      smooth_ramp_existence := fun circumference h =>
        M63.smooth_ramp_existence_of_local (G.product circumference h)
          (hproduct circumference h) G.nonnegative.1 G.nonnegative.2.1 G.nonnegative.2.2
          (G.product_bounds circumference h) (hprod circumference h)
      polygons := fun circumference h t _ _ hN polygon =>
        m63PolygonEstimates (G.product circumference h) t polygon hN
      sampled_length := m63SampledPolygonLengthComparison F
      uniform_derivatives := huniform }

end PoincareMT
