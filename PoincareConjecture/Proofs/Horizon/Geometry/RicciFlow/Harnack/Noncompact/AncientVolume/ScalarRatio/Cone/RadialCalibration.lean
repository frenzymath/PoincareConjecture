import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SourceSegments
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.AnnularDistance

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]

theorem exists_radial_decrement_of_metricComplete
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p x : M)
    {r : ℝ} (hr : 0 < r) (hrd : r < (g.edist p x).toReal) :
    ∃ y : M, (g.edist x y).toReal = r ∧
      (g.edist p y).toReal = (g.edist p x).toReal - r := by
  let d := (g.edist p x).toReal
  have hd : 0 < d := hr.trans hrd
  have hsym : (g.edist x p).toReal = d := by
    let := g.toMetricSpace
    exact dist_comm x p
  obtain ⟨γ, hγ0, hγd, hγ⟩ :=
    g.exists_unit_speed_minimizing_segment_of_metricComplete hc x p (by rw [hsym]; exact hd)
  rw [hsym] at hγd hγ
  refine ⟨γ r, ?_, ?_⟩
  · have h := hγ 0 ⟨le_rfl, hd.le⟩ r ⟨hr.le, hrd.le⟩
    simpa only [hγ0, zero_sub, abs_neg, abs_of_pos hr] using h
  · have h := hγ d ⟨hd.le, le_rfl⟩ r ⟨hr.le, hrd.le⟩
    rw [hγd, abs_of_pos (show 0 < d - r from sub_pos.mpr hrd)] at h
    exact h

theorem exists_radial_calibration_of_normal_chart_limits
    (g : ℕ → RiemannianMetric n M) (hc : ∀ k, MetricComplete (g k))
    (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (p : M) (q : ℕ → M)
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {S R : ℝ} (hRS : R < S)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (htarget : ∀ k, (Φ k).target = (g k).ball (q k) S)
    (hradial : ∀ k x, x ∈ Metric.ball 0 S →
      (g k).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    {W : Set (EuclideanSpace ℝ (Fin n))}
    (hRW : Metric.closedBall 0 R ⊆ W)
    (hdist : TendstoUniformlyOn
      (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        ((g k).edist (Φ k z.1) (Φ k z.2)).toReal)
      (fun z => (h.edist z.1 z.2).toReal) atTop (W ×ˢ W))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContinuousOn f W)
    (hpotential : TendstoUniformlyOn
      (fun k x => ((g k).edist p (Φ k x)).toReal ^ 2 / 2) f atTop W)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ Metric.ball 0 (R / 4))
    {r : ℝ} (hr : 0 < r) (hrR : r < R / 4)
    (hrf : r < Real.sqrt (2 * f z)) :
    ∃ w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
      (h.edist z w).toReal = r ∧
        f w = (Real.sqrt (2 * f z) - r) ^ 2 / 2 ∧
        ∀ a : ℝ, r = (1 - a) * Real.sqrt (2 * f z) → f w = a ^ 2 * f z := by
  have hzR : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R :=
    ball_subset_closedBall ((Metric.ball_subset_ball (by linarith)) hz)
  have hzW := hRW hzR
  have hzS : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) S :=
    (Metric.ball_subset_ball (by linarith)) hz
  let d : ℕ → ℝ := fun k => ((g k).edist p (Φ k z)).toReal
  have hd : Tendsto d atTop (𝓝 (Real.sqrt (2 * f z))) := by
    have hsquare : Tendsto (fun k => d k ^ 2) atTop (𝓝 (2 * f z)) := by
      convert (hpotential.tendsto_at hzW).const_mul 2 using 1
      funext k
      dsimp [d]
      ring
    apply hsquare.sqrt.congr
    intro k
    exact Real.sqrt_sq ENNReal.toReal_nonneg
  have hlarge : ∀ᶠ k in atTop, r < d k := hd.eventually (eventually_gt_nhds hrf)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  have hpoints (k : ℕ) : ∃ y : M,
      ((g (k + N)).edist (Φ (k + N) z) y).toReal = r ∧
        ((g (k + N)).edist p y).toReal = d (k + N) - r :=
    (g (k + N)).exists_radial_decrement_of_metricComplete (hc _) p _ hr
      (hN (k + N) (Nat.le_add_left _ _))
  choose y hyDist hyRad using hpoints
  have hybound (k : ℕ) : ((g (k + N)).edist (q (k + N)) (y k)).toReal < R := by
    let := (g (k + N)).toMetricSpace
    have htri := dist_triangle (q (k + N)) (Φ (k + N) z) (y k)
    change ((g (k + N)).edist (q (k + N)) (y k)).toReal ≤
      ((g (k + N)).edist (q (k + N)) (Φ (k + N) z)).toReal +
        ((g (k + N)).edist (Φ (k + N) z) (y k)).toReal at htri
    rw [hradial _ _ hzS, ENNReal.toReal_ofReal (norm_nonneg _), hyDist] at htri
    have hzNorm : ‖z‖ < R / 4 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    linarith
  have hyTarget (k : ℕ) : y k ∈ (Φ (k + N)).target := by
    rw [htarget]
    exact (ENNReal.lt_ofReal_iff_toReal_lt ((g (k + N)).edist_ne_top _ _)).mpr
      ((hybound k).trans hRS)
  let v : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (Φ (k + N)).symm (y k)
  have hvBack (k : ℕ) : Φ (k + N) (v k) = y k :=
    (Φ (k + N)).right_inv (hyTarget k)
  have hvR (k : ℕ) : v k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    have h := hradial (k + N) (v k) (by
      rw [← hsource]
      exact (Φ (k + N)).map_target (hyTarget k))
    rw [hvBack] at h
    have hh := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hh
    have hb := hybound k
    rw [hh] at hb
    simpa only [Metric.mem_closedBall, dist_zero_right] using hb.le
  obtain ⟨w, hw, τ, hτ, hvlim⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).tendsto_subseq hvR
  let σ : ℕ → ℕ := fun k => τ k + N
  have hσ : StrictMono σ := fun i j hij => Nat.add_lt_add_right (hτ hij) N
  have hlimW : Tendsto (v ∘ τ) atTop (𝓝[W] w) :=
    tendsto_nhdsWithin_iff.mpr ⟨hvlim, Eventually.of_forall (fun k => hRW (hvR (τ k)))⟩
  have hdistσ : TendstoUniformlyOn
      (fun k y => ((g (σ k)).edist (Φ (σ k) z) (Φ (σ k) y)).toReal)
      (fun y => (h.edist z y).toReal) atTop W := by
    have hh := (hdist.comp (fun y : EuclideanSpace ℝ (Fin n) => (z, y))).mono
      (show W ⊆ (fun y => (z, y)) ⁻¹' (W ×ˢ W) from fun _ hy => ⟨hzW, hy⟩)
    intro A hA
    exact hσ.tendsto_atTop.eventually (hh A hA)
  have hdistLim := hdistσ.tendsto_comp
    (h.continuous_toReal_edist z).continuousAt.continuousWithinAt hlimW
  have hconstDist : Tendsto
      (fun k => ((g (σ k)).edist (Φ (σ k) z) (Φ (σ k) (v (τ k)))).toReal)
      atTop (𝓝 r) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)) using 1
    funext k
    change ((g (τ k + N)).edist (Φ (τ k + N) z) (Φ (τ k + N) (v (τ k)))).toReal = r
    rw [hvBack, hyDist]
  have hpotσ : TendstoUniformlyOn
      (fun k x => ((g (σ k)).edist p (Φ (σ k) x)).toReal ^ 2 / 2) f atTop W := by
    intro A hA
    exact hσ.tendsto_atTop.eventually (hpotential A hA)
  have hpotLim := hpotσ.tendsto_comp (hf w (hRW hw)) hlimW
  have hradLim : Tendsto
      (fun k => ((g (σ k)).edist p (Φ (σ k) (v (τ k)))).toReal ^ 2 / 2)
      atTop (𝓝 ((Real.sqrt (2 * f z) - r) ^ 2 / 2)) := by
    apply (((hd.comp hσ.tendsto_atTop).sub_const r).pow 2 |>.div_const 2).congr
    intro k
    change (d (τ k + N) - r) ^ 2 / 2 =
      ((g (τ k + N)).edist p (Φ (τ k + N) (v (τ k)))).toReal ^ 2 / 2
    rw [hvBack, hyRad]
  have hvalue := tendsto_nhds_unique hpotLim hradLim
  refine ⟨w, hw, tendsto_nhds_unique hdistLim hconstDist, hvalue, ?_⟩
  intro a ha
  have hnonneg : 0 ≤ 2 * f z := (Real.sqrt_pos.mp (hr.trans hrf)).le
  rw [hvalue, ha, show Real.sqrt (2 * f z) - (1 - a) * Real.sqrt (2 * f z) =
    a * Real.sqrt (2 * f z) by ring, mul_pow, Real.sq_sqrt hnonneg]
  ring

theorem radial_lipschitz_of_distance_and_potential_limits
    (g : ℕ → RiemannianMetric n M)
    (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (p : M)
    (Φ : ℕ → EuclideanSpace ℝ (Fin n) → M)
    {W : Set (EuclideanSpace ℝ (Fin n))} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hdist : ∀ x ∈ W, ∀ y ∈ W, Tendsto
      (fun k => ((g k).edist (Φ k x) (Φ k y)).toReal)
      atTop (𝓝 ((h.edist x y).toReal)))
    (hpotential : ∀ x ∈ W, Tendsto
      (fun k => ((g k).edist p (Φ k x)).toReal ^ 2 / 2) atTop (𝓝 (f x))) :
    ∀ x ∈ W, ∀ y ∈ W,
      |Real.sqrt (2 * f x) - Real.sqrt (2 * f y)| ≤ (h.edist x y).toReal := by
  have hrad (x) (hx : x ∈ W) : Tendsto
      (fun k => ((g k).edist p (Φ k x)).toReal) atTop (𝓝 (Real.sqrt (2 * f x))) := by
    have hs : Tendsto (fun k => ((g k).edist p (Φ k x)).toReal ^ 2)
        atTop (𝓝 (2 * f x)) := by
      convert (hpotential x hx).const_mul 2 using 1
      funext k
      ring
    apply hs.sqrt.congr
    intro k
    exact Real.sqrt_sq ENNReal.toReal_nonneg
  intro x hx y hy
  apply le_of_tendsto_of_tendsto ((hrad x hx).sub (hrad y hy) |>.abs) (hdist x hx y hy)
  exact Eventually.of_forall fun k => by
    let := (g k).toMetricSpace
    change |dist p (Φ k x) - dist p (Φ k y)| ≤ dist (Φ k x) (Φ k y)
    simpa only [dist_comm] using abs_dist_sub_le (Φ k x) (Φ k y) p

end PoincareConjecture.RiemannianMetric
