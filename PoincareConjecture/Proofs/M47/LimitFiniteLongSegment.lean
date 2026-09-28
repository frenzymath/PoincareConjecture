import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem limitFinite_exists_long_terminal_segment
    {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [ConnectedSpace M] (g : RiemannianMetric 3 M) (hcomplete : MetricComplete g)
    (hnoncompact : ¬IsCompact (univ : Set M)) (o : M) {D : ℝ} (hD : 0 ≤ D) :
    ∃ (y z : M) (d : ℝ), 10 * (D + 1) < d ∧
      (g.edist o y).toReal = d ∧ (g.edist y z).toReal = d ∧
      (g.edist o z).toReal = 2 * d := by
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hcomplete
  have hfar : ∃ z : M, 20 * (D + 1) < dist o z := by
    by_contra! h
    apply hnoncompact
    apply (isCompact_closedBall o (20 * (D + 1))).of_isClosed_subset isClosed_univ
    intro x _
    simpa only [mem_closedBall, dist_comm] using h x
  obtain ⟨z, hz⟩ := hfar
  change 20 * (D + 1) < (g.edist o z).toReal at hz
  have hlength : 0 < (g.edist o z).toReal :=
    lt_trans (by positivity : 0 < 20 * (D + 1)) hz
  obtain ⟨gamma, hzero, hend, _, _, hmin⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hcomplete o z hlength
  let d := (g.edist o z).toReal / 2
  have hd : 0 < d := half_pos hlength
  have hmiddle : d ∈ Icc 0 (g.edist o z).toReal := by
    dsimp only [d]
    constructor <;> linarith
  have hstart : (0 : ℝ) ∈ Icc 0 (g.edist o z).toReal := ⟨le_rfl, hlength.le⟩
  have hfinish : (g.edist o z).toReal ∈ Icc 0 (g.edist o z).toReal :=
    ⟨hlength.le, le_rfl⟩
  refine ⟨gamma d, z, d, ?_, ?_, ?_, ?_⟩
  · change 10 * (D + 1) < (g.edist o z).toReal / 2
    linarith
  · rw [← hzero, hmin 0 hstart d hmiddle, ENNReal.toReal_ofReal (abs_nonneg _),
      zero_sub, abs_neg, abs_of_pos hd]
  · rw [← hend, hmin d hmiddle _ hfinish, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_nonpos (sub_nonpos.mpr hmiddle.2)]
    dsimp only [d]
    ring
  · dsimp only [d]
    ring

end PoincareConjecture.M47
