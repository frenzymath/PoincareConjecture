import PoincareConjecture.Proofs.M47.TerminalSourceNormalMap
import PoincareConjecture.Proofs.M47.TerminalSourceNormalBuffers
import PoincareConjecture.Proofs.M47.TerminalSourceNormalVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

theorem terminalSourceNormal_surgery
    {S : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}} {b Q τ : ℝ}
    (U : TopologicalSpace.Opens C.carrier) (p0 : U)
    (e : SurgeryFlowCylinder S C b Q (Icc (-τ) 0) U)
    (h0 : (0 : ℝ) ∈ Icc (-τ) 0) (F : RicciFlow 3 U (Icc (-τ) 0))
    (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      (F.metric 0).inner x v w = e.pullbackInner 0 h0 x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    (hnorm : ∀ x : U, (F.connection 0).curvatureTensorNorm x =
      (S.connection (b + 0 / Q)).curvatureTensorNorm (e.forward 0 h0 x.val) / Q)
    {A R r K v : ℝ} (hK : 0 ≤ K) (hA : 0 < A) (hr : 0 < r) (hv : 0 < v)
    (hAR : A ≤ R) (hAr : A + r ≤ R) :
    let j := terminalSourceNormal_terminalMap U p0 e h0
    (S.metric b).ball (j p0) (6 * R / Real.sqrt Q) ⊆ range (fun x : U => j x) →
    (∀ z ∈ (S.metric b).ball (j p0) (5 * R / Real.sqrt Q),
      (S.connection b).curvatureTensorNorm z ≤ K * Q) →
    ENNReal.ofReal (v / Real.sqrt Q ^ 3) ≤
      calibratedMetricVolume (S.metric b) ((S.metric b).ball (j p0) (r / Real.sqrt Q)) →
    let ρ := RiemannianMetric.localInjectivityRadius 3 K R v
    0 < ρ ∧ ρ < R ∧ ∀ p ∈ (F.metric 0).ball p0 A,
      ∃ chart : TerminalSourceChart (F.metric 0) ρ, chart.centre = p ∧
        ∀ s : ℝ, 0 < s → s ≤ R →
          0 < RiemannianMetric.smallerBallVolumeBound 3 K R v s ∧
          ENNReal.ofReal (RiemannianMetric.smallerBallVolumeBound 3 K R v s) ≤
            calibratedMetricVolume (F.metric 0) ((F.metric 0).ball p s) ∧
          calibratedMetricVolume (F.metric 0) ((F.metric 0).ball p s) < ⊤ ∧
          calibratedMetricVolume (F.metric 0) ((F.metric 0).ball p s) =
            ENNReal.ofReal (Real.sqrt Q ^ 3) * calibratedMetricVolume (S.metric b)
              ((S.metric b).ball (j p) (s / Real.sqrt Q)) := by
  let j := terminalSourceNormal_terminalMap U p0 e h0
  change (S.metric b).ball (j p0) (6 * R / Real.sqrt Q) ⊆
      range (fun x : U => j x) →
    (∀ z ∈ (S.metric b).ball (j p0) (5 * R / Real.sqrt Q),
      (S.connection b).curvatureTensorNorm z ≤ K * Q) →
    ENNReal.ofReal (v / Real.sqrt Q ^ 3) ≤
      calibratedMetricVolume (S.metric b)
        ((S.metric b).ball (j p0) (r / Real.sqrt Q)) →
    let ρ := RiemannianMetric.localInjectivityRadius 3 K R v
    0 < ρ ∧ ρ < R ∧ ∀ p ∈ (F.metric 0).ball p0 A,
      ∃ chart : TerminalSourceChart (F.metric 0) ρ, chart.centre = p ∧
        ∀ s : ℝ, 0 < s → s ≤ R →
          0 < RiemannianMetric.smallerBallVolumeBound 3 K R v s ∧
          ENNReal.ofReal (RiemannianMetric.smallerBallVolumeBound 3 K R v s) ≤
            calibratedMetricVolume (F.metric 0) ((F.metric 0).ball p s) ∧
          calibratedMetricVolume (F.metric 0) ((F.metric 0).ball p s) < ⊤ ∧
          calibratedMetricVolume (F.metric 0) ((F.metric 0).ball p s) =
            ENNReal.ofReal (Real.sqrt Q ^ 3) * calibratedMetricVolume (S.metric b)
              ((S.metric b).ball (j p) (s / Real.sqrt Q))
  intro hcover hcurv hvol
  have hj := terminalSourceNormal_terminal_map U p0 e h0
  have hm := terminalSourceNormal_terminal_readouts U p0 e h0 F hmetric hnorm
  have hR : 0 < R := hA.trans_le hAR
  have hb : b ∈ S.time_domain := by
    simpa only [zero_div, add_zero] using e.time_subset ⟨0, h0, rfl⟩
  have hc := terminalSourceNormal_physical_buffers (F.metric 0) (F.connection 0)
    (S.metric b) (S.connection b) j hj.1 e.scale_pos hR (by linarith : r ≤ R)
    hm.1 hm.2 p0 (S.slices_compact b hb) (hj.2.1.symm ▸ hcover) hcurv hvol
  have hp0 : p0 ∈ (F.metric 0).ball p0 A := by
    change (F.metric 0).edist p0 p0 < ENNReal.ofReal A
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hA
  have hfirst := terminalSourceNormal_of_center (F.metric 0) (F.connection 0) p0 p0
    hK hA hr hv hAR hAr hp0 hc.1 hc.2.1 hc.2.2
  refine ⟨hfirst.1, hfirst.2.1, ?_⟩
  intro p hp
  obtain ⟨_, _, chart, hcentre⟩ :=
    terminalSourceNormal_of_center (F.metric 0) (F.connection 0) p0 p
      hK hA hr hv hAR hAr hp hc.1 hc.2.1 hc.2.2
  refine ⟨chart, hcentre, ?_⟩
  intro s hs hsR
  have hvolume := terminalSourceNormal_center_volume (F.metric 0) (F.connection 0) p0 p
    hK hA hr hv hAR hAr hp hc.1 hc.2.1 hc.2.2 hs hsR
  refine ⟨hvolume.1, hvolume.2.1, hvolume.2.2, ?_⟩
  let h : RiemannianMetric 3 (S.slice b).carrier := M13.scaleSmoothMetric (S.metric b) Q e.scale_pos
  have hm' (x : U) (v w : TangentSpace (𝓡 3) x) :
      (F.metric 0).inner x v w = h.inner (j x)
        (mfderiv (𝓡 3) (𝓡 3) j x v) (mfderiv (𝓡 3) (𝓡 3) j x w) := hm.1 x v w
  have hcover' : h.ball (j p0) (6 * R) ⊆ j.target := by
    rw [terminalSourceNormal_scaled_ball, hj.2.1]
    exact hcover
  apply terminalSourceNormal_physical_ball_volume (F.metric 0) (S.metric b) j hj.1
    e.scale_pos hm.1 p s
  rw [← terminalSourceNormal_scaled_ball (S.metric b) e.scale_pos (j p) s]
  intro z hz
  apply hcover'
  calc
    h.edist (j p0) z ≤ h.edist (j p0) (j p) + h.edist (j p) z :=
      M36.metric_edist_triangle h _ _ _
    _ < ENNReal.ofReal A + ENNReal.ofReal s := ENNReal.add_lt_add
      ((terminalSourceNormal_edist_le (F.metric 0) h j hj.1 hm' p0 p).trans_lt hp) hz
    _ = ENNReal.ofReal (A + s) := (ENNReal.ofReal_add hA.le hs.le).symm
    _ ≤ ENNReal.ofReal (6 * R) := ENNReal.ofReal_le_ofReal (by linarith)

end PoincareConjecture.M47
