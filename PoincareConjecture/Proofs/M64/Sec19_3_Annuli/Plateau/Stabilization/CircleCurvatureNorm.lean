import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.DoubleProductRicci
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Norm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Bundle
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M64

private lemma sum_fin_tuple_succ {I : Type*} [Fintype I] {k : ℕ}
    (f : (Fin (k + 1) → I) → ℝ) :
    (∑ a : Fin (k + 1) → I, f a) = ∑ i : I, ∑ a : Fin k → I, f (Fin.cons i a) := by
  classical
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => I))
      (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)).symm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

set_option maxHeartbeats 800000 in

theorem auxiliaryCircle_curvatureTensorNorm_eq
    (P : M62.CircleProductData F circumference) (time : ℝ) (q : P.charts.Point) :
    (P.flow.connection time).curvatureTensorNorm q =
      (F.connection time).curvatureTensorNorm q.1 := by
  classical
  let := P.charts.chartedSpace
  let g := F.metric time
  let G := P.flow.metric time
  let D := F.connection time
  let DG := P.flow.connection time
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace (𝓡 1) : P.circle.Point → Type _) :=
    ⟨P.circle.metricOnPoints.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
    ⟨G.toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) q.1
  let H := TangentSpace (𝓡 1) q.2
  let L : TangentSpace (𝓡 (n + 1)) q ≃ₗ[ℝ] WithLp 2 (E × H) :=
    (P.charts.split q).toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (E × H)).symm
  have hL (u v : TangentSpace (𝓡 (n + 1)) q) :
      inner ℝ (L u) (L v) = inner ℝ u v := by
    change inner ℝ (WithLp.toLp 2 (P.charts.split q u))
      (WithLp.toLp 2 (P.charts.split q v)) = _
    rw [WithLp.prod_inner_apply]
    exact (P.metric_eq time q u v).symm
  let J := L.isometryOfInner hL
  let beta := g.orthonormalBasis q.1
  let eta := P.circle.metricOnPoints.orthonormalBasis q.2
  let B := (beta.prod eta).map J.symm
  have hb (i : Fin (Module.finrank ℝ E)) :
      P.charts.split q (B (Sum.inl i)) = (beta i, 0) := by
    change P.charts.split q (J.symm ((beta.prod eta) (Sum.inl i))) = _
    rw [OrthonormalBasis.prod_apply]
    exact (P.charts.split q).apply_symm_apply _
  have hc (i : Fin (Module.finrank ℝ H)) :
      P.charts.split q (B (Sum.inr i)) = (0, eta i) := by
    change P.charts.split q (J.symm ((beta.prod eta) (Sum.inr i))) = _
    rw [OrthonormalBasis.prod_apply]
    exact (P.charts.split q).apply_symm_apply _
  obtain ⟨A, hA⟩ := DG.curvatureTensorCalculus.1.1 q
  have hnorm : DG.curvatureTensorNorm q =
      Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
        (DG.curvatureTensor q (B i) (B j) (B k) (B l)) ^ 2) := by
    have heq := multilinear_sum_mul_orthonormalBasis_eq A A (G.orthonormalBasis q) B
    simp_rw [← hA, LeviCivitaData.riemannEvaluation, sum_fin_tuple_succ] at heq
    simp only [Fintype.sum_unique] at heq
    norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] at heq
    simpa only [LeviCivitaData.curvatureTensorNorm, pow_two,
      Fintype.sum_sum_type] using congrArg Real.sqrt heq
  have hz0 (u v w : TangentSpace (𝓡 n) q.1) : D.curvatureTensor q.1 0 u v w = 0 := by
    simpa using D.curvatureTensor_smul_first q.1 0 0 u v w
  have hz1 (u v w : TangentSpace (𝓡 n) q.1) : D.curvatureTensor q.1 u 0 v w = 0 := by
    simpa using D.curvatureTensor_smul_second q.1 0 u 0 v w
  have hz2 (u v w : TangentSpace (𝓡 n) q.1) : D.curvatureTensor q.1 u v 0 w = 0 := by
    simpa using D.curvatureTensor_smul_third q.1 0 u v 0 w
  have hz3 (u v w : TangentSpace (𝓡 n) q.1) : D.curvatureTensor q.1 u v w 0 = 0 := by
    simpa using D.curvatureTensor_smul_last q.1 0 u v w 0
  dsimp only [D] at hz0 hz1 hz2 hz3
  rw [hnorm]
  apply congrArg Real.sqrt
  simp only [Fintype.sum_sum_type]
  simp only [DG, M62.circleProduct_curvatureTensor (F.metric time) (F.connection time)
    P.circle P.charts (P.flow.metric time) (P.flow.connection time) (P.metric_eq time),
    hb, hc, hz0, hz1, hz2, hz3, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, add_zero]
  rfl

theorem auxiliaryCircle_double_curvatureTensorNorm_eq
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ) (q : Q.charts.Point) :
    (Q.flow.connection time).curvatureTensorNorm q =
      (F.connection time).curvatureTensorNorm q.1.1 := by
  rw [auxiliaryCircle_curvatureTensorNorm_eq Q, auxiliaryCircle_curvatureTensorNorm_eq P]

theorem auxiliaryCircle_sectional_abs_le
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ) (q : Q.charts.Point)
    (u v : TangentSpace (𝓡 ((n + 1) + 1)) q) :
    |(Q.flow.connection time).sectionalCurvature q u v| ≤
      (F.connection time).curvatureTensorNorm q.1.1 := by
  rw [← auxiliaryCircle_double_curvatureTensorNorm_eq P Q time q]
  exact (Q.flow.connection time).abs_sectionalCurvature_le_curvatureTensorNorm q u v

theorem auxiliaryCircle_curvatureSupremum_eq
    (P : M62.CircleProductData F circumference) (time : ℝ) :
    m64CurvatureSupremum P.flow time = m64CurvatureSupremum F time := by
  unfold m64CurvatureSupremum
  congr 1
  ext value
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, (auxiliaryCircle_curvatureTensorNorm_eq P time q).symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(q, P.circle.quotient 0), auxiliaryCircle_curvatureTensorNorm_eq P time _⟩

theorem auxiliaryCircle_double_curvatureSupremum_eq
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ) :
    m64CurvatureSupremum Q.flow time = m64CurvatureSupremum F time := by
  rw [auxiliaryCircle_curvatureSupremum_eq Q, auxiliaryCircle_curvatureSupremum_eq P]

theorem auxiliaryCircle_sectional_abs_le_supremum
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (hbounded : BddAbove (range (fun x : M => (F.connection time).curvatureTensorNorm x)))
    (q : Q.charts.Point) (u v : TangentSpace (𝓡 ((n + 1) + 1)) q) :
    |(Q.flow.connection time).sectionalCurvature q u v| ≤ m64CurvatureSupremum F time :=
  (auxiliaryCircle_sectional_abs_le P Q time q u v).trans
    (m64Curvature_le_supremum hbounded q.1.1)

end PoincareConjecture.M64
