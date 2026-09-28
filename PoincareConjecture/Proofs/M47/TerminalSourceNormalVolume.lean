import PoincareConjecture.Proofs.M47.TerminalSourceNormalCharts
import PoincareConjecture.Proofs.M47.TerminalSourceNormalTransfer
import PoincareConjecture.Proofs.M15.Thm1_34_LocalVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]

theorem terminalSourceNormal_center_volume
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (p0 p : M)
    {A R r K v s : ℝ} (hK : 0 ≤ K) (hA : 0 < A) (hr : 0 < r) (hv : 0 < v)
    (hAR : A ≤ R) (hAr : A + r ≤ R) (hp : p ∈ g.ball p0 A)
    (hcompact : IsCompact (closure (g.ball p0 (5 * R))))
    (hcurv : ∀ x ∈ g.ball p0 (5 * R), D.curvatureTensorNorm x ≤ K)
    (hvol : ENNReal.ofReal v ≤ g.volumeMeasure (g.ball p0 r))
    (hs : 0 < s) (hsR : s ≤ R) :
    0 < RiemannianMetric.smallerBallVolumeBound 3 K R v s ∧
      ENNReal.ofReal (RiemannianMetric.smallerBallVolumeBound 3 K R v s) ≤
        calibratedMetricVolume g (g.ball p s) ∧
      calibratedMetricVolume g (g.ball p s) < ⊤ := by
  have hR : 0 < R := hA.trans_le hAR
  have hbase : g.ball p0 r ⊆ g.ball p R := by
    intro x hx
    have hpp0 : g.edist p p0 < ENNReal.ofReal A := by
      have hp' : g.edist p0 p < ENNReal.ofReal A := hp
      simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hp'
    calc
      g.edist p x ≤ g.edist p p0 + g.edist p0 x := M36.metric_edist_triangle g p p0 x
      _ < ENNReal.ofReal A + ENNReal.ofReal r := ENNReal.add_lt_add hpp0 hx
      _ = ENNReal.ofReal (A + r) := (ENNReal.ofReal_add hA.le hr.le).symm
      _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal hAr
  have hlarge : closure (g.ball p (2 * R)) ⊆ g.ball p0 (5 * R) :=
    g.closure_ball_subset_ball_of_margin hA.le (by positivity) (by linarith) hp
  have hc : IsCompact (closure (g.ball p (2 * R))) :=
    hcompact.of_isClosed_subset isClosed_closure (hlarge.trans subset_closure)
  have hb := g.smallerBall_volume_lower_bound_of_curvatureTensorNorm_le D p
    (by norm_num) hK hR hv hc (fun x hx => hcurv x (hlarge (subset_closure hx)))
    (hvol.trans (measure_mono hbase)) hs hsR
  have hcs : IsCompact (closure (g.ball p s)) :=
    hc.of_isClosed_subset isClosed_closure (closure_mono (fun x hx =>
      hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith : s ≤ 2 * R))))
  refine ⟨hb.1, ?_, Proofs.M15.calibratedMetricVolume_ball_lt_top_of_precompact g p s hcs⟩
  simpa only [Proofs.M15.calibratedMetricVolume_eq_volumeMeasure] using hb.2

end PoincareConjecture.M47
