import PoincareConjecture.Proofs.M47.GeneralizedBridgeGeometry
import PoincareConjecture.Proofs.M47.TerminalSourceNormalTransfer
import PoincareConjecture.Proofs.M47.BlowupControlsSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem terminalSource_regular_history_ball_buffer
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {base Q tau R r : ℝ}
    (hbase : base ∈ H.generalized.interval) (htau : 0 < tau)
    (x : (H.generalized.slice base).carrier) (hr : 0 ≤ r) (hrR : r < R)
    (e : SurgeryFlowCylinder F (F.slice base) base Q (Icc (-tau) 0)
      ((F.metric base).ball (H.history.forward base hbase x) R))
    (hbased : ∀ hs y, y ∈ (F.metric base).ball (H.history.forward base hbase x) R →
      HEq (e.forward 0 hs y) y) :
    (F.metric base).ball (H.history.forward base hbase x) R ⊆
        range (H.history.forward base hbase) ∧
      IsCompact (closure ((H.generalized.metric base).ball x r)) ∧
      calibratedMetricVolume (H.generalized.metric base)
          ((H.generalized.metric base).ball x r) =
        calibratedMetricVolume (F.metric base)
          ((F.metric base).ball (H.history.forward base hbase x) r) := by
  let h0 : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨neg_nonpos.mpr htau.le, le_rfl⟩
  have hregular := e.regular_image_of_earlier h0
    ⟨-tau, ⟨le_rfl, neg_nonpos.mpr htau.le⟩, neg_lt_zero.mpr htau⟩
  have hball : (F.metric base).ball (H.history.forward base hbase x) R ⊆
      range (H.history.forward base hbase) := by
    rw [H.regular_range]
    intro y hy
    have he : (⟨base + 0 / Q, e.forward 0 h0 y⟩ : Σ t, (F.slice t).carrier) =
        ⟨base, y⟩ := Sigma.ext (by simp) (hbased h0 y hy)
    exact (congrArg (fun p : Σ t, (F.slice t).carrier =>
      p.2 ∈ m33RegularRegion F p.1) he).mp (hregular ⟨y, hy, rfl⟩)
  let phi := regular_history_slice_chart H base hbase
  have hm (y : (H.generalized.slice base).carrier)
      (v w : TangentSpace (𝓡 3) y) :
      (H.generalized.metric base).inner y v w = (F.metric base).inner (phi y)
        (mfderiv (𝓡 3) (𝓡 3) phi y v) (mfderiv (𝓡 3) (𝓡 3) phi y w) :=
    (H.history.metric_pullback base hbase y v w).symm
  let a := (R - r) / 2
  have ha : 0 < a := by dsimp only [a]; linarith
  have hcenter : H.history.forward base hbase x ∈
      (F.metric base).ball (H.history.forward base hbase x) a := by
    change (F.metric base).edist _ _ < ENNReal.ofReal a
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr ha
  have hcl : closure ((F.metric base).ball (H.history.forward base hbase x) r) ⊆
      (F.metric base).ball (H.history.forward base hbase x) R :=
    (F.metric base).closure_ball_subset_ball_of_margin ha.le hr
      (by dsimp only [a]; linarith) hcenter
  have hcompact := F.slices_compact base (H.history.time_subset hbase)
  refine ⟨hball, ?_, ?_⟩
  · exact terminalSourceNormal_compact_ball (H.generalized.metric base) (F.metric base)
      phi rfl hm x r (hcompact.of_isClosed_subset isClosed_closure (subset_univ _))
      (hcl.trans hball)
  · apply H.ball_volume_of_subset base hbase x r
    rw [← H.regular_range base hbase]
    intro y hy
    exact hball (hy.trans_le (ENNReal.ofReal_le_ofReal hrR.le))

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ n, M33RegularHistoryWindow (F n))
  (H : ∀ n, M33RegularHistoryData (W n)) (t : ℕ → ℝ)
  (ht : ∀ n, t n ∈ (H n).generalized.interval)
  (x : ∀ n, ((H n).generalized.slice (t n)).carrier)
  (hPositive : ∀ n, 0 < ((F n).connection (t n)).scalarCurvature
    ((H n).history.forward (t n) (ht n) (x n)))
  (hDiverges : Tendsto (fun n => ((F n).connection (t n)).scalarCurvature
    ((H n).history.forward (t n) (ht n) (x n))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W H t ht x hPositive hDiverges

theorem terminalSource_blowup_base_balls_compact
    (A tau : ℕ → ℝ) (htau : ∀ j, 0 < tau j)
    (hA : ∀ a : ℝ, 0 < a → ∃ j, a < A j)
    (hstage : ∀ j, ∀ᶠ n in atTop,
      ∃ e : SurgeryFlowCylinder (F n) ((F n).slice (t n)) (t n) ((V).scale n)
          (Icc (-(tau j)) 0) (((F n).metric (t n)).ball
            ((H n).history.forward (t n) (ht n) (x n)) (A j / Real.sqrt ((V).scale n))),
        ∀ hs y, y ∈ ((F n).metric (t n)).ball
            ((H n).history.forward (t n) (ht n) (x n)) (A j / Real.sqrt ((V).scale n)) →
          HEq (e.forward 0 hs y) y) :
    BlowupBaseBallsCompact V := by
  intro a ha
  obtain ⟨j, hj⟩ := hA a ha
  filter_upwards [hstage j] with n hn
  obtain ⟨e, he⟩ := hn
  have hroot : 0 < Real.sqrt ((V).scale n) := Real.sqrt_pos.mpr ((V).base_scalar_pos n)
  exact (terminalSource_regular_history_ball_buffer (H n) (ht n) (htau j) (x n)
    (div_pos ha hroot).le (div_lt_div_of_pos_right hj hroot) e he).2.1

end PoincareConjecture.M47
