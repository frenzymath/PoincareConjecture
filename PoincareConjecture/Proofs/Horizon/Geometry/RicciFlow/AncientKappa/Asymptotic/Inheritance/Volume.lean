import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Spatial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}
  (G : AncientCompactTimeConvergence S)

theorem eventually_source_ball_subset_image_ball
    {t r C : ℝ} (ht : t < 0) (p : G.limit.carrier.carrier) (hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k in atTop,
      ((S.rescaling (G.subsequence k)).flow.metric t).ball ((G.embedding k).toFun (t, p)).2 r ⊆
        (fun x ↦ ((G.embedding k).toFun (t, x)).2) '' (G.limit.flow.metric t).ball p (C * r) := by
  let g := G.limit.flow.metric t
  let R := C * r + 1
  have hCp : 0 < C := zero_lt_one.trans hC
  have hR : 0 < R := by dsimp [R]; positivity
  have hcompact : IsCompact (closure (g.ball p R)) :=
    g.isCompact_closure_ball_of_metricComplete (G.limit.complete t ht) p R
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [G.eventually_pullback_tangentNorm_bounds hcompact ht hC,
    eventually_timeWindow_mem_nhds ht, eventually_ge_atTop j] with k hk hkt hjk
  let h := (S.rescaling (G.subsequence k)).flow.metric t
  let e := (G.embedding k).spatialHomeomorph (G.exhaustion_open k) hkt
  have hsource : closure (g.ball p R) ⊆ e.source := hj.trans (G.exhaustion_monotone hjk)
  have hei : ∀ y ∈ e.target, ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm y := by
    rintro _ ⟨x, hx, rfl⟩
    exact (G.embedding k).spatialInverse_contMDiffAt (G.exhaustion_open k) hkt hx
  have hbound := g.inverse_tangentNorm_le_of_le h e
    ((G.embedding k).spatialHomeomorph_mdifferentiable (G.exhaustion_open k) hkt)
    hsource (fun x hx v ↦ (hk x hx v).2)
  exact g.ball_subset_image_ball_of_inverse_tangentNorm_le h e p hR hCp
    (by dsimp [R]; linarith) hcompact hsource
    (fun y hy ↦ (hei y hy).of_le (by simp)) hbound

theorem eventually_ball_volume_bounds
    {t r C : ℝ} (ht : t < 0) (p : G.limit.carrier.carrier) (hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k in atTop,
      ((S.rescaling (G.subsequence k)).flow.metric t).volumeMeasure
          (((S.rescaling (G.subsequence k)).flow.metric t).ball ((G.embedding k).toFun (t, p)).2 r) ≤
        ENNReal.ofReal C ^ n * (G.limit.flow.metric t).volumeMeasure ((G.limit.flow.metric t).ball p (C * r)) ∧
      (G.limit.flow.metric t).volumeMeasure ((G.limit.flow.metric t).ball p (r / C)) ≤
        ENNReal.ofReal C ^ n * ((S.rescaling (G.subsequence k)).flow.metric t).volumeMeasure
          (((S.rescaling (G.subsequence k)).flow.metric t).ball ((G.embedding k).toFun (t, p)).2 r) := by
  let g := G.limit.flow.metric t
  let : EMetricSpace G.limit.carrier.carrier := G.limit.carrier.metricEMetricSpace g
  let R := C * r + 1
  let V := g.ball p R
  have hCp : 0 < C := zero_lt_one.trans hC
  have hcompact : IsCompact (closure V) :=
    g.isCompact_closure_ball_of_metricComplete (G.limit.complete t ht) p R
  have hball (s : ℝ) : IsOpen (g.ball p s) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hV : IsOpen V := hball R
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [G.eventually_pullback_tangentNorm_bounds hcompact ht hC,
    G.eventually_source_ball_subset_image_ball ht p hr hC,
    eventually_timeWindow_mem_nhds ht, eventually_ge_atTop j] with k hk hcover hkt hjk
  let h := (S.rescaling (G.subsequence k)).flow.metric t
  let e := (G.embedding k).spatialHomeomorph (G.exhaustion_open k) hkt
  have hVe : V ⊆ e.source := subset_closure.trans (hj.trans (G.exhaustion_monotone hjk))
  have he : ∀ x ∈ e.source, ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x :=
    fun x hx ↦ (G.embedding k).spatialMap_contMDiffAt_of_time_nhds (G.exhaustion_open k) hkt hx
  have hei : ∀ y ∈ e.target, ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm y := by
    rintro _ ⟨x, hx, rfl⟩
    exact (G.embedding k).spatialInverse_contMDiffAt (G.exhaustion_open k) hkt hx
  have hf : ∀ x ∈ V, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ C * g.tangentNorm x v :=
    fun x hx v ↦ (hk x (subset_closure hx) v).1
  have hb : ∀ x ∈ V, ∀ v : TangentSpace (𝓡 n) x,
      g.tangentNorm x v ≤ C * h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) :=
    fun x hx v ↦ (hk x (subset_closure hx) v).2
  have hlarge : g.ball p (C * r) ⊆ V := fun x hx ↦
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
      (fun x hx ↦ (he x hx).of_le (by simp) |>.contMDiffWithinAt) hCp hf
      (hball (C * r)).measurableSet hlarge
  · have himage : IsOpen (e '' g.ball p (r / C)) :=
      e.isOpen_image_of_subset_source (hball (r / C)) (hsmall.trans hVe)
    have hinv := g.inverse_tangentNorm_le_of_le h e
      ((G.embedding k).spatialHomeomorph_mdifferentiable (G.exhaustion_open k) hkt) hVe hb
    have hvol := h.volumeMeasure_image_le_of_tangentNorm_le g e.symm
      (e.isOpen_image_of_subset_source hV hVe)
      (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hVe hx))
      (fun y hy ↦ (hei y hy).of_le (by simp) |>.contMDiffWithinAt) hCp hinv
      himage.measurableSet (image_mono hsmall)
    have hback : e.symm '' (e '' g.ball p (r / C)) = g.ball p (r / C) := by
      rw [image_image]
      exact Set.EqOn.image_eq_self (fun x hx ↦ e.left_inv (hVe (hsmall hx)))
    rw [hback] at hvol
    apply hvol.trans (mul_le_mul' le_rfl (measure_mono ?_))
    have hi := g.image_ball_subset_ball_of_tangentNorm_le h e p hCp
      (hsmall.trans hVe) (fun x hx ↦ (he x hx).of_le (by simp))
      (fun x hx ↦ hf x (hsmall hx))
    change e '' g.ball p (r / C) ⊆ h.ball (e p) r
    simpa only [mul_div_cancel₀ _ hCp.ne'] using hi

theorem tendsto_calibratedMetricVolume_ball
    {t r : ℝ} (ht : t < 0) (p : G.limit.carrier.carrier) (hr : 0 < r) :
    Tendsto (fun k ↦ calibratedMetricVolume ((S.rescaling (G.subsequence k)).flow.metric t)
      (((S.rescaling (G.subsequence k)).flow.metric t).ball ((G.embedding k).toFun (t, p)).2 r))
      atTop (𝓝 (calibratedMetricVolume (G.limit.flow.metric t)
        ((G.limit.flow.metric t).ball p r))) := by
  simp_rw [calibratedMetricVolume_eq_volumeMeasure]
  apply Poincare.tendsto_of_ball_volume_radius_squeeze (r := r)
    (V := fun ρ ↦ (G.limit.flow.metric t).volumeMeasure ((G.limit.flow.metric t).ball p ρ)) n
  · exact (G.limit.flow.metric t).continuousAt_ball_volume_of_metricComplete
      (G.limit.complete t ht) p hr
  · intro C hC
    exact (G.eventually_ball_volume_bounds ht p hr hC).mono (fun _ h ↦ h.1)
  · intro C hC
    exact (G.eventually_ball_volume_bounds ht p hr hC).mono (fun _ h ↦ h.2)

end PoincareConjecture.AncientCompactTimeConvergence
