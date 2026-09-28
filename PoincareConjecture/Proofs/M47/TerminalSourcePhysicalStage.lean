import PoincareConjecture.Proofs.M47.TerminalSourceNormalSurgery
import PoincareConjecture.Proofs.M47.TerminalSourceIndexedCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalSource_exists_physical_stage
    {A R r K v : ℝ} (hK : 0 ≤ K) (hA : 0 < A) (hr : 0 < r) (hv : 0 < v)
    (hAR : A ≤ R) (hAr : A + r ≤ R) :
    let Rchart := RiemannianMetric.localInjectivityRadius 3 K R v
    ∃ rho : ℝ, 0 < rho ∧ 2 * rho < Rchart ∧
      (∀ s : ℝ, |s| ≤ 2 * rho →
        (K * s ^ 2) * Real.exp (max 1 (K * s ^ 2)) ≤ 3) ∧
      ∀ (S : SurgeryFlowData.{u}) (C : GeneralizedSliceCarrier.{u})
        (b Q tau : ℝ) (U : TopologicalSpace.Opens C.carrier) (p0 : U)
        (e : SurgeryFlowCylinder S C b Q (Icc (-tau) 0) U)
        (h0 : (0 : ℝ) ∈ Icc (-tau) 0) (F : RicciFlow 3 U (Icc (-tau) 0)),
        (∀ (x : U) (w z : TangentSpace (𝓡 3) x),
          (F.metric 0).inner x w z = e.pullbackInner 0 h0 x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x z)) →
        (∀ x : U, (F.connection 0).curvatureTensorNorm x =
          (S.connection (b + 0 / Q)).curvatureTensorNorm (e.forward 0 h0 x.val) / Q) →
        (S.metric b).ball (terminalSourceNormal_terminalMap U p0 e h0 p0)
          (6 * R / Real.sqrt Q) ⊆
            range (fun x : U => terminalSourceNormal_terminalMap U p0 e h0 x) →
        (∀ z ∈ (S.metric b).ball (terminalSourceNormal_terminalMap U p0 e h0 p0)
            (5 * R / Real.sqrt Q),
          (S.connection b).curvatureTensorNorm z ≤ K * Q) →
        ENNReal.ofReal (v / Real.sqrt Q ^ 3) ≤ calibratedMetricVolume (S.metric b)
          ((S.metric b).ball (terminalSourceNormal_terminalMap U p0 e h0 p0)
            (r / Real.sqrt Q)) →
        ∃ cover : TerminalSourceIndexedChartCover (F.metric 0) p0 A Rchart rho
            (⌈RiemannianMetric.modelVolume 3 K (3 * A) /
              RiemannianMetric.modelVolume 3 K (min (A / 2) (rho / 4) / 2)⌉₊ + 1),
          ∀ i, ∀ x ∈ Metric.closedBall (0 : E) (2 * rho), ∀ w : E,
            (1 / 4 : ℝ) * ‖w‖ ^ 2 ≤
              (F.metric 0).pullbackCoefficients (cover.chart i).chart x w w ∧
            (F.metric 0).pullbackCoefficients (cover.chart i).chart x w w ≤
              (9 / 4 : ℝ) * ‖w‖ ^ 2 := by
  classical
  let Rchart := RiemannianMetric.localInjectivityRadius 3 K R v
  have hR : 0 < R := hA.trans_le hAR
  have hRchart : 0 < Rchart := RiemannianMetric.localInjectivityRadius_pos 3 K hR v
  have hRchartR : Rchart < R := RiemannianMetric.localInjectivityRadius_lt 3 K hR v
  obtain ⟨rho, hrho, hrhoR, hsmall⟩ :=
    RiemannianMetric.exists_uniform_radial_comparison_radius hRchart K
  refine ⟨rho, hrho, hrhoR, hsmall, ?_⟩
  intro S C b Q tau U p0 e h0 F hmetric hnorm hcover hcurv hvol
  let j := terminalSourceNormal_terminalMap U p0 e h0
  have hj := terminalSourceNormal_terminal_map U p0 e h0
  have hm := terminalSourceNormal_terminal_readouts U p0 e h0 F hmetric hnorm
  have hb : b ∈ S.time_domain := by
    simpa only [zero_div, add_zero] using e.time_subset ⟨0, h0, rfl⟩
  have buffers := terminalSourceNormal_physical_buffers (F.metric 0) (F.connection 0)
    (S.metric b) (S.connection b) j hj.1 e.scale_pos hR (by linarith : r ≤ R)
    hm.1 hm.2 p0 (S.slices_compact b hb) (hj.2.1.symm ▸ hcover) hcurv hvol
  have normal := terminalSourceNormal_surgery U p0 e h0 F hmetric hnorm
    hK hA hr hv hAR hAr hcover hcurv hvol
  have hball : (F.metric 0).ball p0 (5 * A) ⊆ (F.metric 0).ball p0 (5 * R) := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hcompact : IsCompact (closure ((F.metric 0).ball p0 (5 * A))) :=
    buffers.1.of_isClosed_subset isClosed_closure (closure_mono hball)
  obtain ⟨cover⟩ := terminalSourceNormal_nonempty_indexed_chart_cover
    (F.metric 0) (F.connection 0) p0 hA hrho (by linarith : rho / 4 < Rchart)
    hK hcompact (fun x hx => buffers.2.1 x (hball hx))
    (fun x hx => by obtain ⟨C, hC, _⟩ := normal.2.2 x hx; exact ⟨C, hC⟩)
  refine ⟨cover, ?_⟩
  intro i x hx w
  apply (cover.chart i).terminal_bounds (F.connection 0) hrhoR hsmall ?_ hx w
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hzTarget : (cover.chart i).chart z ∈
      (F.metric 0).ball (cover.chart i).centre Rchart := by
    rw [← (cover.chart i).target]
    exact (cover.chart i).chart.map_source ((cover.chart i).source.symm ▸ hz)
  apply buffers.2.1
  calc
    (F.metric 0).edist p0 ((cover.chart i).chart z) ≤
        (F.metric 0).edist p0 (cover.chart i).centre +
          (F.metric 0).edist (cover.chart i).centre ((cover.chart i).chart z) :=
      M36.metric_edist_triangle (F.metric 0) _ _ _
    _ < ENNReal.ofReal A + ENNReal.ofReal Rchart :=
      ENNReal.add_lt_add (cover.centre_mem i) hzTarget
    _ = ENNReal.ofReal (A + Rchart) := (ENNReal.ofReal_add hA.le hRchart.le).symm
    _ ≤ ENNReal.ofReal (5 * R) := ENNReal.ofReal_le_ofReal (by linarith)

end PoincareConjecture.M47
