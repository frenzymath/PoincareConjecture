import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ProductRicciTraceBound
import PoincareConjecture.Proofs.M62.Cor0_3_PointwiseBounds













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}





theorem m64Curvature_pair_abs_le_of_unit_bound
    (D : LeviCivitaData g) (x : M) {K : ℝ}
    (hunit : ∀ v : Fin 4 → TangentSpace (𝓡 n) x,
      (∀ i, g.tangentNorm x (v i) ≤ 1) →
        |D.curvatureTensor x (v 0) (v 1) (v 2) (v 3)| ≤ K)
    (u v : TangentSpace (𝓡 n) x) :
    |D.curvatureTensor x u v u v| ≤ K * g.inner x u u * g.inner x v v := by
  have h := M62.tensor_abs_le_of_unit_bound g D.riemannEvaluation
    (M04.isSmoothCovariantTensor_riemannEvaluation D) x hunit ![u, v, u, v]
  have hnorm (w : TangentSpace (𝓡 n) x) : g.tangentNorm x w ^ 2 = g.inner x w w :=
    Real.sq_sqrt ((g.toRiemannianMetric.toCore x).re_inner_nonneg w)
  have hprod : (∏ i : Fin 4, g.tangentNorm x (![u, v, u, v] i)) =
      g.tangentNorm x u ^ 2 * g.tangentNorm x v ^ 2 := by
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.prod_univ_zero, mul_one]
    ring
  change |D.curvatureTensor x u v u v| ≤ _ at h
  rw [hprod, hnorm, hnorm] at h
  exact h.trans_eq (by ring)





theorem m64Curvature_sectional_abs_le_of_unit_bound
    (D : LeviCivitaData g) (x : M) {K : ℝ} (hK : 0 ≤ K)
    (hunit : ∀ v : Fin 4 → TangentSpace (𝓡 n) x,
      (∀ i, g.tangentNorm x (v i) ≤ 1) →
        |D.curvatureTensor x (v 0) (v 1) (v 2) (v 3)| ≤ K)
    (u v : TangentSpace (𝓡 n) x) : |D.sectionalCurvature x u v| ≤ K := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_cases hu : g.inner x u u = 0
  · have hu0 : u = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hu
    have hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 = 0 := by
      simp [hu0]
    rw [D.sectionalCurvature_eq_zero_of_gramDet_eq_zero x u v hgram, abs_zero]
    exact hK
  let c := g.inner x u v / g.inner x u u
  let w := v + (-c) • u
  have hnum : D.curvatureTensor x u w u w = D.curvatureTensor x u v u v := by
    simp only [w, D.curvatureTensor_add_second, D.curvatureTensor_add_last,
      D.curvatureTensor_smul_second, D.curvatureTensor_smul_last,
      D.curvatureTensor_zero_first, D.curvatureTensor_zero_last,
      mul_zero, add_zero]
  have hgram : g.inner x u u * g.inner x w w =
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
    change (inner ℝ u u) * inner ℝ w w =
      (inner ℝ u u) * inner ℝ v v - (inner ℝ u v) ^ 2
    simp only [w, inner_add_left, inner_add_right, real_inner_smul_right, real_inner_comm]
    change g.inner x u u *
      (g.inner x v v + -c * g.inner x u v +
        (-c * g.inner x u v + -c * (-c * g.inner x u u))) =
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2
    dsimp [c]
    field_simp [hu]
    ring
  have hbound := m64Curvature_pair_abs_le_of_unit_bound D x hunit u w
  rw [hnum, mul_assoc, hgram] at hbound
  have hnonneg : 0 ≤ g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
    rw [← hgram]
    exact mul_nonneg ((g.toRiemannianMetric.toCore x).re_inner_nonneg u)
      ((g.toRiemannianMetric.toCore x).re_inner_nonneg w)
  by_cases hz : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 = 0
  · rw [D.sectionalCurvature_eq_zero_of_gramDet_eq_zero x u v hz, abs_zero]
    exact hK
  have hpos := lt_of_le_of_ne hnonneg (Ne.symm hz)
  unfold LeviCivitaData.sectionalCurvature
  rw [abs_div, abs_of_pos hpos]
  exact (div_le_iff₀ hpos).mpr hbound

variable [T2Space M] {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}





theorem m64CircleProduct_ricci_quadratic_abs_le_of_unit_bound
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n)
    (t : ℝ) {K : ℝ} (hK : 0 ≤ K) (q : P.charts.Point)
    (hunit : ∀ v : Fin 4 → TangentSpace (𝓡 n) q.1,
      (∀ i, (F.metric t).tangentNorm q.1 (v i) ≤ 1) →
        |(F.connection t).curvatureTensor q.1 (v 0) (v 1) (v 2) (v 3)| ≤ K)
    (v : TangentSpace (𝓡 (n + 1)) q) :
    |(P.flow.connection t).ricci q v v| ≤
      ((n : ℝ) - 1) * K * (P.flow.metric t).inner q v v := by
  have hbase := (F.connection t).abs_ricci_quadratic_le_of_abs_sectionalCurvature_le
    q.1 K (m64Curvature_sectional_abs_le_of_unit_bound (F.connection t) q.1 hK hunit)
    (P.charts.split q v).1
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

end PoincareConjecture
