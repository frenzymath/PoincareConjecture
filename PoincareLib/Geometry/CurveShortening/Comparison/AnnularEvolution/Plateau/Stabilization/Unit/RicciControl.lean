import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Modulus.UnitCurvatureBounds
import PoincareLib.Geometry.RicciFlow.Product.Circle.Bounds

/-!
# Original unit-input curvature control after two flat factors

The Ricci tensor drops both circle components before applying the original
base unit-input bound. The ambient M63 constant therefore retains the
coefficient `n - 1`; no full tensor norm is identified with that constant.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

/-- Bound the stabilized Ricci form directly by the original unit-input curvature constant.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem auxiliaryCircle_ricci_quadratic_abs_le_of_unit_bound
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (hn : 1 ≤ n)
    (t : ℝ) {K : ℝ} (hK : 0 ≤ K) (q : Q.charts.Point)
    (hunit : ∀ v : Fin 4 → TangentSpace (𝓡 n) q.1.1,
      (∀ i, (F.metric t).tangentNorm q.1.1 (v i) ≤ 1) →
        |(F.connection t).curvatureTensor q.1.1 (v 0) (v 1) (v 2) (v 3)| ≤ K)
    (v : TangentSpace (𝓡 ((n + 1) + 1)) q) :
    |(Q.flow.connection t).ricci q v v| ≤
      ((n : ℝ) - 1) * K * (Q.flow.metric t).inner q v v := by
  have hbase := m64CircleProduct_ricci_quadratic_abs_le_of_unit_bound
    P hn t hK q.1 hunit (Q.charts.split q v).1
  have hmetric : (P.flow.metric t).inner q.1
      (Q.charts.split q v).1 (Q.charts.split q v).1 ≤
      (Q.flow.metric t).inner q v v := by
    rw [Q.metric_eq]
    exact le_add_of_nonneg_right
      ((Q.circle.metricOnPoints.toRiemannianMetric.toCore q.2).re_inner_nonneg _)
  have hcoef : 0 ≤ ((n : ℝ) - 1) * K := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (sub_nonneg.mpr hn') hK
  rw [M62.circleProduct_ricci (P.flow.metric t) (P.flow.connection t)
    Q.circle Q.charts (Q.flow.metric t) (Q.flow.connection t) (Q.metric_eq t)]
  exact hbase.trans (mul_le_mul_of_nonneg_left hmetric hcoef)

omit [T2Space M] in
/-- Bound stabilized sectional curvature directly by the original ambient curvature
hypothesis. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem auxiliaryCircle_sectional_abs_le_of_ambient_bounds
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    {K0 K1 K2 : ℝ} (hK0 : 0 ≤ K0)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {t : ℝ} (ht : t ∈ Icc a b) (q : Q.charts.Point)
    (u v : TangentSpace (𝓡 ((n + 1) + 1)) q) :
    |(Q.flow.connection t).sectionalCurvature q u v| ≤ K0 :=
  m64Curvature_sectional_abs_le_of_unit_bound (Q.flow.connection t) q hK0
    ((Q.ambient_bounds (P.ambient_bounds hBounds)).riemann t ht q) u v

end PoincareMT.M64
