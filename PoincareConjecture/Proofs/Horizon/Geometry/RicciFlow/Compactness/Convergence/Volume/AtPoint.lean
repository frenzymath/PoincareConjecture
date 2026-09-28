import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Convergence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
  (G : PointedGeometricConvergence S)

theorem eventually_source_ball_subset_image_ball_at
    {t r C : ℝ} (ht : t ∈ Ioo T' T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (p : G.limitCarrier.carrier) (hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k in atTop,
      ((S.flow (G.subsequence k)).metricAt t).ball ((G.embedding k).toFun (t, p)).2 r ⊆
        (fun x => ((G.embedding k).toFun (t, x)).2) '' (G.limitFlow.metricAt t).ball p (C * r) := by
  let g := G.limitFlow.metricAt t
  let R := C * r + 1
  have hCp : 0 < C := zero_lt_one.trans hC
  have hR : 0 < R := by dsimp [R]; positivity
  have hcompact : IsCompact (closure (g.ball p R)) :=
    g.isCompact_closure_ball_of_metricComplete hcomplete p R
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [G.eventually_pullback_tangentNorm_bounds hcompact ht hC,
    eventually_ge_atTop j] with k hk hjk
  let h := (S.flow (G.subsequence k)).metricAt t
  let e := (G.embedding k).spatialHomeomorph (G.exhaustion_open k) ht
  have hsource : closure (g.ball p R) ⊆ e.source := hj.trans (G.exhaustion_monotone hjk)
  have he : ∀ x ∈ e.source, ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x :=
    fun x hx => (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) ht hx
  have hei : ∀ y ∈ e.target, ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm y := by
    rintro _ ⟨x, hx, rfl⟩
    exact (G.embedding k).spatialInverse_contMDiffAt (G.exhaustion_open k) ht hx
  have hed : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨fun x hx => (he x hx).mdifferentiableAt (by simp) |>.mdifferentiableWithinAt,
      fun y hy => (hei y hy).mdifferentiableAt (by simp) |>.mdifferentiableWithinAt⟩
  have hbound := g.inverse_tangentNorm_le_of_le h e hed
    hsource (fun x hx v => (hk x hx v).2)
  exact g.ball_subset_image_ball_of_inverse_tangentNorm_le h e p hR hCp
    (by dsimp [R]; linarith) hcompact hsource
    (fun y hy => (hei y hy).of_le (by simp)) hbound

theorem eventually_ball_volume_bounds_at
    {t r C : ℝ} (ht : t ∈ Ioo T' T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (p : G.limitCarrier.carrier) (hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k in atTop,
      ((S.flow (G.subsequence k)).metricAt t).volumeMeasure
          (((S.flow (G.subsequence k)).metricAt t).ball ((G.embedding k).toFun (t, p)).2 r) ≤
        ENNReal.ofReal C ^ n * (G.limitFlow.metricAt t).volumeMeasure
          ((G.limitFlow.metricAt t).ball p (C * r)) ∧
      (G.limitFlow.metricAt t).volumeMeasure ((G.limitFlow.metricAt t).ball p (r / C)) ≤
        ENNReal.ofReal C ^ n * ((S.flow (G.subsequence k)).metricAt t).volumeMeasure
          (((S.flow (G.subsequence k)).metricAt t).ball ((G.embedding k).toFun (t, p)).2 r) := by
  let g := G.limitFlow.metricAt t
  let : EMetricSpace G.limitCarrier.carrier := G.limitCarrier.metricEMetricSpace g
  let R := C * r + 1
  let V := g.ball p R
  have hCp : 0 < C := zero_lt_one.trans hC
  have hcompact : IsCompact (closure V) :=
    g.isCompact_closure_ball_of_metricComplete hcomplete p R
  have hball (s : ℝ) : IsOpen (g.ball p s) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hV : IsOpen V := hball R
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [G.eventually_pullback_tangentNorm_bounds hcompact ht hC,
    G.eventually_source_ball_subset_image_ball_at ht hcomplete p hr hC,
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
  have hlarge : g.ball p (C * r) ⊆ V := fun x hx =>
    hx.trans_le (ENNReal.ofReal_le_ofReal (by dsimp [R]; linarith))
  have hsmall : g.ball p (r / C) ⊆ V := by
    intro x hx
    apply hx.trans_le (ENNReal.ofReal_le_ofReal ?_)
    have hdiv : r / C ≤ r := div_le_self hr.le hC.le
    have hmul : r ≤ C * r := by nlinarith
    dsimp [R]
    linarith
  constructor
  · apply (measure_mono hcover).trans
    exact g.volumeMeasure_image_le_of_tangentNorm_le h e hV hVe
      (fun x hx => (he x hx).of_le (by simp) |>.contMDiffWithinAt) hCp hf
      (hball (C * r)).measurableSet hlarge
  · have himage : IsOpen (e '' g.ball p (r / C)) :=
      e.isOpen_image_of_subset_source (hball (r / C)) (hsmall.trans hVe)
    have hinv := g.inverse_tangentNorm_le_of_le h e hed hVe hb
    have hvol := h.volumeMeasure_image_le_of_tangentNorm_le g e.symm
      (e.isOpen_image_of_subset_source hV hVe)
      (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hVe hx))
      (fun y hy => (hei y hy).of_le (by simp) |>.contMDiffWithinAt) hCp hinv
      himage.measurableSet (image_mono hsmall)
    have hback : e.symm '' (e '' g.ball p (r / C)) = g.ball p (r / C) := by
      rw [image_image]
      exact Set.EqOn.image_eq_self (fun x hx => e.left_inv (hVe (hsmall hx)))
    rw [hback] at hvol
    apply hvol.trans (mul_le_mul' le_rfl (measure_mono ?_))
    have hi := g.image_ball_subset_ball_of_tangentNorm_le h e p hCp
      (hsmall.trans hVe) (fun x hx => (he x hx).of_le (by simp))
      (fun x hx => hf x (hsmall hx))
    change e '' g.ball p (r / C) ⊆ h.ball (e p) r
    simpa only [mul_div_cancel₀ _ hCp.ne'] using hi

theorem tendsto_volumeMeasure_ball_at
    {t r : ℝ} (ht : t ∈ Ioo T' T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (p : G.limitCarrier.carrier) (hr : 0 < r) :
    Tendsto (fun k => ((S.flow (G.subsequence k)).metricAt t).volumeMeasure
      (((S.flow (G.subsequence k)).metricAt t).ball ((G.embedding k).toFun (t, p)).2 r))
      atTop (𝓝 ((G.limitFlow.metricAt t).volumeMeasure ((G.limitFlow.metricAt t).ball p r))) := by
  apply Poincare.tendsto_of_ball_volume_radius_squeeze (r := r)
    (V := fun ρ => (G.limitFlow.metricAt t).volumeMeasure ((G.limitFlow.metricAt t).ball p ρ)) n
  · exact (G.limitFlow.metricAt t).continuousAt_ball_volume_of_metricComplete
      hcomplete p hr
  · intro C hC
    exact (G.eventually_ball_volume_bounds_at ht hcomplete p hr hC).mono (fun _ h => h.1)
  · intro C hC
    exact (G.eventually_ball_volume_bounds_at ht hcomplete p hr hC).mono (fun _ h => h.2)

end PoincareConjecture.PointedGeometricConvergence
