import PoincareLib.Geometry.CurveShortening.Deformation.SweptArea.FlowMetricScaling
import PoincareLib.Geometry.CurveShortening.Deformation.Analysis.RiemannianDistanceComparison

/-!
# Actual metric distance comparison for disk transport

Claim 19.23, Morgan--Tian pp. 453-454. The norm and distance factors
are the square root of the quadratic-form factor. No geodesic minimizer
or completeness assumption is used. See M65 derivation 14.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Tangent norms at included flow times have the square-root metric
comparison factor; Claim 19.23, pp. 453-454. -/
theorem m65FlowTangentNorm_comparison {a b : ℝ} (F : RicciFlow n M (Icc a b))
    {K0 K1 K2 : ℝ} (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (F.metric t).tangentNorm x v ≤
      Real.exp (K2 * |t - s|) * (F.metric s).tangentNorm x v := by
  unfold RiemannianMetric.tangentNorm
  calc
    _ ≤ Real.sqrt (Real.exp ((2 * K2) * |t - s|) * (F.metric s).inner x v v) :=
      Real.sqrt_le_sqrt (m65FlowMetric_comparison F bounds hs ht x v)
    _ = _ := by
      have hexp : Real.exp ((2 * K2) * |t - s|) = Real.exp (K2 * |t - s|) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [Real.sqrt_mul (Real.exp_nonneg _), hexp, Real.sqrt_sq (Real.exp_nonneg _)]

/-- The actual extended distances compare in either time order, through
the original endpoints; Claim 19.23, pp. 453-454. -/
theorem m65FlowEdist_comparison {a b : ℝ} (F : RicciFlow n M (Icc a b))
    {K0 K1 K2 : ℝ} (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x y : M) :
    (F.metric t).edist x y ≤
      ENNReal.ofReal (Real.exp (K2 * |t - s|)) * (F.metric s).edist x y :=
  m65Edist_le_of_tangentNorm_le (F.metric s) (F.metric t) (Real.exp_pos _)
    (m65FlowTangentNorm_comparison F bounds hs ht) x y

end PoincareMT
