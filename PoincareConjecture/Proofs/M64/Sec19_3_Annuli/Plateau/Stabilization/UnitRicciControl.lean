import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusUnitCurvatureBounds
import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductBounds












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}



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

end PoincareConjecture.M64
