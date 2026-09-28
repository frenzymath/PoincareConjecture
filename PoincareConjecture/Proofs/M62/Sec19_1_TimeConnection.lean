import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeFrame
import PoincareConjecture.Proofs.M04.ScalarBracket
import PoincareConjecture.Proofs.M04.FixedExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M62.SpacetimeData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem time_covariant_vertical {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (q : G.charts.Point)
    (V : TangentSpace (𝓡 (n + 1)) q) :
    (G.charts.split q
      (G.connection.connection G.charts.timeVector q V)).2 = 0 := by
  let := G.charts.chartedSpace
  have hT := G.charts.timeVector_smooth
  have h := M04.metric_derivative_pairing G.connection
    (FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1))) V)
    ((hT q).mdifferentiableAt (by simp)) ((hT q).mdifferentiableAt (by simp))
  simp only [G.time_unit, mvfderiv_const, zero_apply,
    FiberBundle.extend_apply_self] at h
  rw [G.metric.symm q (G.charts.timeVector q)
    (G.connection.connection G.charts.timeVector q V)] at h
  simp only [G.inner_time] at h
  linarith

theorem time_parallel_time {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (q : G.charts.Point) :
    G.connection.connection G.charts.timeVector q (G.charts.timeVector q) = 0 := by
  let := G.charts.chartedSpace
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let I := 𝓡 (n + 1)
  let T := G.charts.timeVector
  let tau : G.charts.Point → ℝ := fun r => (r.2 : ℝ)
  let Z := G.connection.connection T q (T q)
  let Y := FiberBundle.extend E Z
  let e := trivializationAt E (TangentSpace I : G.charts.Point → Type _) q
  have hq : q ∈ e.baseSet := mem_baseSet_trivializationAt E _ q
  have hT : ContMDiff I I.tangent ∞ (T% T) := G.charts.timeVector_smooth
  have htau : ContMDiff I 𝓘(ℝ, ℝ) ∞ tau := G.charts.contMDiff_clock
  have hY : ContMDiffOn I I.tangent ∞ (T% Y) e.baseSet :=
    M04.contMDiffOn_extend_baseSet Z
  have hYq := (hY q hq).contMDiffAt (e.open_baseSet.mem_nhds hq)
  have hdual (r : G.charts.Point) (W : TangentSpace I r) :
      G.metric.inner r W (T r) = mvfderiv I tau r W := by
    rw [G.inner_time, G.charts.split_time]
    rfl
  have htime (r : G.charts.Point) : mvfderiv I tau r (T r) = 1 := by
    rw [← hdual]
    exact G.time_unit r
  have hbr := M04.mvfderiv_mlieBracket e.open_baseSet htau.contMDiffOn
    hT.contMDiffOn hY hq
  change mvfderiv I tau q (VectorField.mlieBracket I T Y q) =
    mvfderiv I (fun r => mvfderiv I tau r (Y r)) q (T q) -
      mvfderiv I (fun r => mvfderiv I tau r (T r)) q (Y q) at hbr
  simp only [htime, mvfderiv_const, zero_apply, sub_zero] at hbr
  have hk := M04.koszul_pairing G.connection
    ((hT q).mdifferentiableAt (by simp)) ((hT q).mdifferentiableAt (by simp))
    (hYq.mdifferentiableAt (by simp))
  have hpair : (fun r => G.metric.inner r (T r) (Y r)) =
      (fun r => mvfderiv I tau r (Y r)) := by
    funext r
    rw [G.metric.symm]
    exact hdual r (Y r)
  have hpair' : (fun r => G.metric.inner r (Y r) (T r)) =
      (fun r => mvfderiv I tau r (Y r)) := funext fun r => hdual r (Y r)
  have hunit : (fun r => G.metric.inner r (T r) (T r)) =
      (fun _ : G.charts.Point => (1 : ℝ)) := funext G.time_unit
  rw [hpair, hpair', hunit, mvfderiv_const] at hk
  simp only [zero_apply, VectorField.mlieBracket_self,
    Pi.zero_apply, map_zero, sub_zero, add_zero] at hk
  have hneg (W : TangentSpace I q) :
      G.metric.inner q (-W) (T q) = -G.metric.inner q W (T q) := by
    rw [G.metric.symm q (-W) (T q), G.metric.symm q W (T q)]
    exact (G.metric.inner q (T q)).map_neg W
  rw [VectorField.mlieBracket_swap_apply (V := Y) (W := T), hneg] at hk
  simp only [hdual] at hk
  have hYY : Y q = Z := FiberBundle.extend_apply_self _ _
  rw [hYY] at hk
  have hzero : G.metric.inner q Z Z = 0 := by
    change 2 * G.metric.inner q Z Z = _ at hk
    linarith
  by_contra hne
  exact (ne_of_gt (G.metric.pos q Z hne)) hzero

theorem time_spatial_vertical {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F)
    (B : ℝ → (p : M) → TangentSpace (𝓡 n) p)
    (hB : G.charts.IsSmoothField (G.charts.liftSpatialField B))
    (q : G.charts.Point) :
    (G.charts.split q
      (G.connection.connection (G.charts.liftSpatialField B)
        q (G.charts.timeVector q))).2 = 0 := by
  let := G.charts.chartedSpace
  have hT := G.charts.timeVector_smooth
  have hzero (r : G.charts.Point) :
      G.metric.inner r (G.charts.liftSpatialField B r) (G.charts.timeVector r) = 0 := by
    rw [G.inner_time]
    simp [SpacetimeCharts.liftSpatialField, SpacetimeCharts.horizontal]
  have h := M04.metric_derivative_pairing G.connection G.charts.timeVector
    ((hB q).mdifferentiableAt (by simp)) ((hT q).mdifferentiableAt (by simp))
  simp only [hzero, mvfderiv_const, zero_apply,
    G.time_parallel_time, map_zero, add_zero, G.inner_time] at h
  exact h.symm

end PoincareConjecture.M62.SpacetimeData
