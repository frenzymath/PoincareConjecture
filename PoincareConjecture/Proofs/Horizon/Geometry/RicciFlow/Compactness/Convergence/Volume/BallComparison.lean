import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SourceBalls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

def BasedFlow.riemannianBallVolume {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    (F : BasedFlow n T' T C) (t r : ℝ) : ℝ≥0∞ :=
  (F.metricAt t).volumeMeasure (F.ballAt t r)

namespace PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem eventually_ball_volume_bounds
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    {t r C : ℝ} (ht : t ∈ Ioo T' T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k : ℕ in atTop,
      (S.flow (G.subsequence k)).riemannianBallVolume t r ≤
          ENNReal.ofReal C ^ n * G.limitFlow.riemannianBallVolume t (C * r) ∧
      G.limitFlow.riemannianBallVolume t (r / C) ≤
          ENNReal.ofReal C ^ n * (S.flow (G.subsequence k)).riemannianBallVolume t r := by
  let g := G.limitFlow.metricAt t
  let : EMetricSpace G.limitCarrier.carrier := G.limitCarrier.metricEMetricSpace g
  let p := G.limitFlow.base
  let R := C * r + 1
  let V := g.ball p R
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hcompact : IsCompact (closure V) :=
    g.isCompact_closure_ball_of_metricComplete hcomplete p R
  have hball (s : ℝ) : IsOpen (g.ball p s) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hV : IsOpen V := hball R
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [G.eventually_pullback_tangentNorm_bounds hcompact ht hC,
    G.eventually_source_ball_subset_image_ball hT ht hcomplete hr hC,
    eventually_ge_atTop j] with k hk hcover hjk
  let h := (S.flow (G.subsequence k)).metricAt t
  let e := (G.embedding k).spatialHomeomorph (G.exhaustion_open k) ht
  have hVe : V ⊆ e.source := subset_closure.trans (hj.trans (G.exhaustion_monotone hjk))
  have he : ∀ x ∈ e.source, ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x :=
    fun x hx => (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) ht hx
  have hei : ∀ y ∈ e.target, ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm y := by
    rintro _ ⟨x, hx, rfl⟩
    exact (G.embedding k).spatialInverse_contMDiffAt (G.exhaustion_open k) ht hx
  have hed : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨fun x hx => (he x hx).mdifferentiableAt (by simp) |>.mdifferentiableWithinAt,
      fun y hy => (hei y hy).mdifferentiableAt (by simp) |>.mdifferentiableWithinAt⟩
  have hf : ∀ x ∈ V, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ C * g.tangentNorm x v :=
    fun x hx v => (hk x (subset_closure hx) v).1
  have hb : ∀ x ∈ V, ∀ v : TangentSpace (𝓡 n) x,
      g.tangentNorm x v ≤ C * h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) :=
    fun x hx v => (hk x (subset_closure hx) v).2
  have hlarge : g.ball p (C * r) ⊆ V := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (by dsimp [R]; linarith))
  have hsmall : g.ball p (r / C) ⊆ V := by
    intro x hx
    apply hx.trans_le (ENNReal.ofReal_le_ofReal ?_)
    have hdiv : r / C ≤ r := (div_le_self hr.le hC.le)
    have hmul : r ≤ C * r := by nlinarith
    dsimp [R]
    linarith
  have hbase : e p = (S.flow (G.subsequence k)).base :=
    congrArg Prod.snd (G.base_preserving_at_time hT k ht)
  change h.volumeMeasure (h.ball (S.flow (G.subsequence k)).base r) ≤
      ENNReal.ofReal C ^ n * g.volumeMeasure (g.ball p (C * r)) ∧
    g.volumeMeasure (g.ball p (r / C)) ≤
      ENNReal.ofReal C ^ n * h.volumeMeasure (h.ball (S.flow (G.subsequence k)).base r)
  constructor
  · apply (measure_mono hcover).trans
    exact g.volumeMeasure_image_le_of_tangentNorm_le h e hV hVe
      (fun x hx => (he x hx).of_le (by simp) |>.contMDiffWithinAt) hCpos hf
      (hball (C * r)).measurableSet hlarge
  · have himage : IsOpen (e '' g.ball p (r / C)) :=
      e.isOpen_image_of_subset_source (hball (r / C)) (hsmall.trans hVe)
    have hinv := g.inverse_tangentNorm_le_of_le h e hed hVe hb
    have hvol := h.volumeMeasure_image_le_of_tangentNorm_le g e.symm
      (e.isOpen_image_of_subset_source hV hVe)
      (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hVe hx))
      (fun y hy => (hei y hy).of_le (by simp) |>.contMDiffWithinAt) hCpos hinv
      himage.measurableSet (image_mono hsmall)
    have hback : e.symm '' (e '' g.ball p (r / C)) = g.ball p (r / C) := by
      rw [image_image]
      exact Set.EqOn.image_eq_self (fun x hx => e.left_inv (hVe (hsmall hx)))
    rw [hback] at hvol
    apply hvol.trans (mul_le_mul' le_rfl (measure_mono ?_))
    have hi := g.image_ball_subset_ball_of_tangentNorm_le h e p hCpos
      (hsmall.trans hVe) (fun x hx => (he x hx).of_le (by simp))
      (fun x hx => hf x (hsmall hx))
    simpa only [hbase, mul_div_cancel₀ _ hCpos.ne'] using hi

end PointedGeometricConvergence
end PoincareConjecture
