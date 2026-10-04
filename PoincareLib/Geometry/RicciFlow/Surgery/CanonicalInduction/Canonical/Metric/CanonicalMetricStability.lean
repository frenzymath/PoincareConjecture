import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.QuadraticRicci
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Scalar.Coefficients
import PoincareLib.Geometry.RicciFlow.MetricComparison
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Metric.CalibratedMetricComparison
import Mathlib.Topology.Order.Compact

/-!
# Actual compact-slab metric and volume comparison

Morgan--Tian Proposition 9.79, pp. 232-234, and Lemma 17.2, pp. 396-397.
Compactness bounds the actual Ricci tensor on the closed ordinary slab.
One exponential factor then compares its actual tangent norms, distances,
and calibrated volumes, in either time order.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators ENNReal

universe u

namespace PoincareMT.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

private theorem ricci_tensorNorm_eq_sqrt {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (x : M) :
    g.tensorNorm D.ricciEvaluation x = Real.sqrt (D.ricciNormSq x) := by
  classical
  let d := Module.finrank ℝ (TangentSpace (𝓡 3) x)
  let b := g.orthonormalBasis x
  let e : (Fin 2 → Fin d) ≃ (Fin d × Fin d) :=
    { toFun := fun a => (a 0, a 1)
      invFun := fun p => ![p.1, p.2]
      left_inv := by intro a; funext i; fin_cases i <;> rfl
      right_inv := by rintro ⟨i, j⟩; rfl }
  change Real.sqrt (∑ a : Fin 2 → Fin d, (D.ricci x (b (a 0)) (b (a 1))) ^ 2) =
    Real.sqrt (∑ i, ∑ j, (D.ricci x (b i) (b j)) ^ 2)
  congr 1
  calc
    _ = ∑ p : Fin d × Fin d, (D.ricci x (b p.1) (b p.2)) ^ 2 := by
      apply Fintype.sum_equiv e
      intro a
      rfl
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      rfl

/-- The actual full squared Ricci norm bounds every quadratic-form
evaluation, as used in ordinary metric variation, Proposition 9.79. -/
theorem abs_ricci_le_sqrt_ricciNormSq {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (x : M) (v : TangentSpace (𝓡 3) x) :
    |D.ricci x v v| ≤ Real.sqrt (D.ricciNormSq x) * g.inner x v v := by
  have h := M04.tensorEvaluation_sq_le_tensorNorm g
    (M04.isSmoothCovariantTensor_ricciEvaluation D) x ![v, v]
  simp only [LeviCivitaData.ricciEvaluation, ricci_tensorNorm_eq_sqrt,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hV : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hN := Real.sqrt_nonneg (D.ricciNormSq x)
  have hproduct := mul_nonneg hN hV
  nlinarith [sq_abs (D.ricci x v v), abs_nonneg (D.ricci x v v)]

/-- Joint continuity gives a positive Ricci bound on the entire actual
compact slab, including its endpoints, Proposition 9.79, pp. 232-234. -/
theorem exists_compact_slab_ricci_bound [CompactSpace M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b)) :
    ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Icc a b, ∀ x : M,
      ∀ v : TangentSpace (𝓡 3) x,
        |(F.connection t).ricci x v v| ≤ K * (F.metric t).inner x v v := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set M))).bddAbove_image
    (M04.continuousOn_flow_ricciNormSq F)
  let K := Real.sqrt (max B 0 + 1)
  have hK : 0 < K := Real.sqrt_pos.mpr (by linarith [le_max_right B 0])
  refine ⟨K, hK, ?_⟩
  intro t ht x v
  have hsq : (F.connection t).ricciNormSq x ≤ max B 0 + 1 := by
    have h := hB ⟨(t, x), ⟨ht, mem_univ x⟩, rfl⟩
    exact h.trans ((le_max_left B 0).trans (by linarith))
  have hnorm : Real.sqrt ((F.connection t).ricciNormSq x) ≤ K := Real.sqrt_le_sqrt hsq
  have hv : 0 ≤ (F.metric t).inner x v v := by
    by_cases hzero : v = 0
    · simp [hzero]
    · exact ((F.metric t).pos x v hzero).le
  exact (abs_ricci_le_sqrt_ricciNormSq (F.connection t) x v).trans
    (mul_le_mul_of_nonneg_right hnorm hv)

/-- One positive constant compares the actual metrics, distances and
calibrated volumes in both time orders on the compact slab,
Proposition 9.79 and Lemma 17.2, pp. 232-234 and 396-397. -/
theorem exists_compact_slab_metric_volume_comparison
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      (∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
        (F.metric t).tangentNorm x v ≤
          Real.exp (K * |t - s|) * (F.metric s).tangentNorm x v) ∧
      (∀ x y : M, (F.metric t).edist x y ≤
        ENNReal.ofReal (Real.exp (K * |t - s|)) * (F.metric s).edist x y) ∧
      ∀ A : Set M, calibratedMetricVolume (F.metric t) A ≤
        ENNReal.ofReal (Real.exp (K * |t - s|)) ^ 3 *
          calibratedMetricVolume (F.metric s) A := by
  obtain ⟨K, hK, hRic⟩ := exists_compact_slab_ricci_bound F
  refine ⟨K, hK, ?_⟩
  intro s hs t ht
  have hnorm (x : M) (v : TangentSpace (𝓡 3) x) :
      (F.metric t).tangentNorm x v ≤
        Real.exp (K * |t - s|) * (F.metric s).tangentNorm x v :=
    F.tangentNorm_le_exp_of_ricci_bound (convex_Icc a b) Subset.rfl x v K
      (fun tau htau => hRic tau htau x v) hs ht
  exact ⟨hnorm,
    M34.edist_le_of_tangentNorm_le (F.metric s) (F.metric t) (Real.exp_pos _) hnorm,
    M34.calibratedMetricVolume_le_of_tangentNorm_le
      (F.metric s) (F.metric t) (Real.exp_pos _) hnorm⟩

end PoincareMT.Proofs.M47
