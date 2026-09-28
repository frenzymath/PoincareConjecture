import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.SourceVariation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.AnnularDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.AnnularPotential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.LocalDilation












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M]

private theorem exists_normal_chart_limit_of_bounded_source_points
    (g : ℕ → RiemannianMetric n M)
    (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (q : ℕ → M)
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
    (z : ℕ → M)
    (hz : ∀ᶠ k in atTop, ((g k).edist (q k) (z k)).toReal < R) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
      ∀ x ∈ W, Tendsto (fun k => ((g (σ k)).edist (Φ (σ k) x) (z (σ k))).toReal)
        atTop (𝓝 ((h.edist x w).toReal)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hz
  let v : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (Φ (k + N)).symm (z (k + N))
  have htargetZ (k : ℕ) : z (k + N) ∈ (Φ (k + N)).target := by
    rw [htarget]
    exact (ENNReal.lt_ofReal_iff_toReal_lt ((g (k + N)).edist_ne_top _ _)).mpr
      ((hN (k + N) (Nat.le_add_left _ _)).trans hRS)
  have hv (k : ℕ) : v k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    have h := hradial (k + N) (v k) (by
      rw [← hsource]
      exact (Φ (k + N)).map_target (htargetZ k))
    have hright : Φ (k + N) (v k) = z (k + N) :=
      (Φ (k + N)).right_inv (htargetZ k)
    rw [hright] at h
    have hreal := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
    have hb := hN (k + N) (Nat.le_add_left _ _)
    rw [hreal] at hb
    simpa only [Metric.mem_closedBall, dist_zero_right] using hb.le
  obtain ⟨w, hw, τ, hτ, hlim⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).tendsto_subseq hv
  let σ : ℕ → ℕ := fun k => τ k + N
  have hσ : StrictMono σ := fun i j hij => Nat.add_lt_add_right (hτ hij) N
  refine ⟨σ, hσ, w, hw, ?_⟩
  intro x hx
  have hfixed : TendstoUniformlyOn
      (fun k y => ((g (σ k)).edist (Φ (σ k) x) (Φ (σ k) y)).toReal)
      (fun y => (h.edist x y).toReal) atTop W := by
    have hh := (hdist.comp (fun y : EuclideanSpace ℝ (Fin n) => (x, y))).mono
      (show W ⊆ (fun y => (x, y)) ⁻¹' (W ×ˢ W) from fun y hy => ⟨hx, hy⟩)
    intro V hV
    exact hσ.tendsto_atTop.eventually (hh V hV)
  have hlimW : Tendsto (v ∘ τ) atTop (𝓝[W] w) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun k => hRW (hv (τ k)))⟩
  have hh := hfixed.tendsto_comp (h.continuous_toReal_edist x).continuousAt.continuousWithinAt hlimW
  apply hh.congr
  intro k
  have hright : Φ (σ k) (v (τ k)) = z (σ k) := (Φ (σ k)).right_inv (htargetZ (τ k))
  change ((g (σ k)).edist (Φ (σ k) x) (Φ (σ k) (v (τ k)))).toReal = _
  rw [hright]

private theorem local_variation_of_source_and_chart_limits
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M)
    (hcomparison : ∀ a b : ℝ, 0 < a → 0 < b → ∀ α β : ℝ → M,
      α 0 = p → β 0 = p →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
        g.edist (α s) (α t) = ENNReal.ofReal |s - t|) →
      (∀ s ∈ Icc (0 : ℝ) b, ∀ t ∈ Icc (0 : ℝ) b,
        g.edist (β s) (β t) = ENNReal.ofReal |s - t|) →
      ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) b,
        s ^ 2 + t ^ 2 - 2 * s * t *
          ((a ^ 2 + b ^ 2 - (g.edist (α a) (β b)).toReal ^ 2) / (2 * a * b)) ≤
            (g.edist (α s) (β t)).toReal ^ 2)
    (gs : ℕ → RiemannianMetric n M)
    (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (q : ℕ → M)
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (scale : ℕ → ℝ) (hscale : ∀ i, 0 < scale i)
    (hscalezero : Tendsto scale atTop (𝓝 0))
    (hscaleDist : ∀ k x y, ((gs k).edist x y).toReal = scale k * (g.edist x y).toReal)
    {S R : ℝ} (hR : 0 < R) (hRS : R < S)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (htarget : ∀ k, (Φ k).target = (gs k).ball (q k) S)
    (hradial : ∀ k x, x ∈ Metric.ball 0 S →
      (gs k).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    {W : Set (EuclideanSpace ℝ (Fin n))}
    (hRW : Metric.closedBall 0 R ⊆ W)
    (hdist : TendstoUniformlyOn
      (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        ((gs k).edist (Φ k z.1) (Φ k z.2)).toReal)
      (fun z => (h.edist z.1 z.2).toReal) atTop (W ×ˢ W))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hpotential : ∀ x ∈ W, Tendsto
      (fun k => ((gs k).edist p (Φ k x)).toReal ^ 2 / 2) atTop (𝓝 (f x)))
    (m : ℕ) (a : Fin (m + 1) → EuclideanSpace ℝ (Fin n))
    (ha : ∀ j, a j ∈ Metric.ball 0 (R / 4)) (hfpos : ∀ j, 0 < f (a j)) :
    ∀ᶠ c : ℝ in 𝓝 1, ∃ w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
      ∀ j : Fin m, (h.edist (a j.succ) w).toReal ^ 2 =
        2 * c ^ 2 * f (a 0) + 2 * f (a j.succ) -
          c * (2 * f (a 0) + 2 * f (a j.succ) - (h.edist (a j.succ) (a 0)).toReal ^ 2) := by
  have haW (j : Fin (m + 1)) : a j ∈ W :=
    hRW (ball_subset_closedBall ((Metric.ball_subset_ball (by linarith : R / 4 ≤ R)) (ha j)))
  let radius : Fin (m + 1) → ℝ := fun j => Real.sqrt (2 * f (a j))
  have hradpos (j : Fin (m + 1)) : 0 < radius j :=
    Real.sqrt_pos.mpr (mul_pos zero_lt_two (hfpos j))
  have hradlim (j : Fin (m + 1)) :
      Tendsto (fun i => scale i * (g.edist p (Φ i (a j))).toReal) atTop (𝓝 (radius j)) := by
    have hsquare : Tendsto (fun k => ((gs k).edist p (Φ k (a j))).toReal ^ 2)
        atTop (𝓝 (2 * f (a j))) := by
      convert! (hpotential (a j) (haW j)).const_mul 2 using 1
      funext k
      ring
    apply hsquare.sqrt.congr
    intro i
    rw [Real.sqrt_sq ENNReal.toReal_nonneg, hscaleDist]
  have hD (j : Fin m) : Tendsto
      (fun k => scale k * (g.edist (Φ k (a j.succ)) (Φ k (a 0))).toReal)
      atTop (𝓝 ((h.edist (a j.succ) (a 0)).toReal)) := by
    apply (hdist.tendsto_at (show (a j.succ, a 0) ∈ W ×ˢ W from ⟨haW _, haW _⟩)).congr
    intro k
    exact hscaleDist k _ _
  obtain ⟨σ, hσ, ray, hzero, hunit, herr, hvariation⟩ :=
    g.exists_source_radial_variation_of_normalized_distance_limits hc p hcomparison
      m (fun j k => Φ k (a j)) scale hscale hscalezero radius hradpos hradlim
      (fun j => (h.edist (a j.succ) (a 0)).toReal) hD
  have hnear : ∀ᶠ c : ℝ in 𝓝 1, 0 < c ∧ |c - 1| * radius 0 < R / 4 := by
    have hh : ContinuousAt (fun c : ℝ => |c - 1| * radius 0) 1 := by fun_prop
    have hsmall := hh.eventually_lt_const (show |(1 : ℝ) - 1| * radius 0 < R / 4 by
      simp only [sub_self, abs_zero, zero_mul]
      positivity)
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num), hsmall] with c hc hc'
    exact ⟨hc, hc'⟩
  filter_upwards [hnear] with c hc'
  let z : ℕ → M := fun i => ray (c * (g.edist p (Φ (σ i) (a 0))).toReal)
  have hbound : ∀ i, ((gs (σ i)).edist (q (σ i)) (z i)).toReal ≤
      ‖a 0‖ + scale (σ i) * (g.edist (Φ (σ i) (a 0))
        (ray ((g.edist p (Φ (σ i) (a 0))).toReal))).toReal +
        |c - 1| * (scale (σ i) * (g.edist p (Φ (σ i) (a 0))).toReal) := by
    intro i
    let := g.toMetricSpace
    let d := (g.edist p (Φ (σ i) (a 0))).toReal
    have hraydist : dist (ray d) (ray (c * d)) = |c - 1| * d := by
      change (g.edist (ray d) (ray (c * d))).toReal = _
      rw [hunit d ENNReal.toReal_nonneg (c * d) (mul_nonneg hc'.1.le ENNReal.toReal_nonneg),
        ENNReal.toReal_ofReal (abs_nonneg _)]
      rw [show d - c * d = (1 - c) * d by ring, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
        abs_sub_comm 1 c]
    have hq : scale (σ i) * dist (q (σ i)) (Φ (σ i) (a 0)) = ‖a 0‖ := by
      change scale (σ i) * (g.edist (q (σ i)) (Φ (σ i) (a 0))).toReal = _
      rw [← hscaleDist, hradial _ _
        ((Metric.ball_subset_ball (by linarith : R / 4 ≤ S)) (ha 0)),
        ENNReal.toReal_ofReal (norm_nonneg _)]
    have ht := (dist_triangle (q (σ i)) (Φ (σ i) (a 0)) (z i)).trans
      (add_le_add le_rfl (dist_triangle (Φ (σ i) (a 0)) (ray d) (z i)))
    have hm := mul_le_mul_of_nonneg_left ht (hscale (σ i)).le
    change scale (σ i) * dist (q (σ i)) (z i) ≤
      scale (σ i) * (dist (q (σ i)) (Φ (σ i) (a 0)) +
        (dist (Φ (σ i) (a 0)) (ray d) + dist (ray d) (ray (c * d)))) at hm
    rw [mul_add, hq, mul_add, hraydist] at hm
    rw [hscaleDist]
    change scale (σ i) * (g.edist (q (σ i)) (z i)).toReal ≤
      ‖a 0‖ + (scale (σ i) * (g.edist (Φ (σ i) (a 0))
        (ray ((g.edist p (Φ (σ i) (a 0))).toReal))).toReal +
        scale (σ i) * (|c - 1| * (g.edist p (Φ (σ i) (a 0))).toReal)) at hm
    nlinarith [hm]
  have hupper : Tendsto (fun i => ‖a 0‖ + scale (σ i) *
      (g.edist (Φ (σ i) (a 0)) (ray ((g.edist p (Φ (σ i) (a 0))).toReal))).toReal +
      |c - 1| * (scale (σ i) * (g.edist p (Φ (σ i) (a 0))).toReal))
      atTop (𝓝 (‖a 0‖ + |c - 1| * radius 0)) := by
    simpa only [add_zero, Function.comp_apply] using (tendsto_const_nhds.add herr).add
      ((hradlim 0).comp hσ.tendsto_atTop |>.const_mul |c - 1|)
  have hzbound : ∀ᶠ i in atTop, ((gs (σ i)).edist (q (σ i)) (z i)).toReal < R := by
    have hn : ‖a 0‖ < R / 4 := by simpa only [Metric.mem_ball, dist_zero_right] using ha 0
    filter_upwards [hupper.eventually_lt_const (show ‖a 0‖ + |c - 1| * radius 0 < R by
      linarith [hc'.2])] with i hi
    exact (hbound i).trans_lt hi
  have hdistσ : TendstoUniformlyOn
      (fun i (u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        ((gs (σ i)).edist (Φ (σ i) u.1) (Φ (σ i) u.2)).toReal)
      (fun u => (h.edist u.1 u.2).toReal) atTop (W ×ˢ W) := by
    intro U hU
    exact hσ.tendsto_atTop.eventually (hdist U hU)
  obtain ⟨τ, hτ, w, hw, hwlim⟩ := exists_normal_chart_limit_of_bounded_source_points
    (fun i => gs (σ i)) h (fun i => q (σ i)) (fun i => Φ (σ i)) hRS
    (fun i => hsource (σ i)) (fun i => htarget (σ i)) (fun i => hradial (σ i))
    hRW hdistσ z hzbound
  refine ⟨w, hw, ?_⟩
  intro j
  have hsourceLimit := (hvariation j c hc'.1).comp hτ.tendsto_atTop
  have hactual : Tendsto (fun i => ((gs (σ (τ i))).edist (Φ (σ (τ i)) (a j.succ))
      (z (τ i))).toReal ^ 2) atTop
      (𝓝 (c ^ 2 * radius 0 ^ 2 + radius j.succ ^ 2 -
        c * (radius 0 ^ 2 + radius j.succ ^ 2 - (h.edist (a j.succ) (a 0)).toReal ^ 2))) := by
    apply hsourceLimit.congr
    intro i
    rw [hscaleDist]
    rfl
  have heq := tendsto_nhds_unique ((hwlim (a j.succ) (haW _)).pow 2) hactual
  have hradSq (k : Fin (m + 1)) : radius k ^ 2 = 2 * f (a k) :=
    Real.sq_sqrt (mul_nonneg zero_le_two (hfpos k).le)
  rw [hradSq 0, hradSq j.succ] at heq
  convert heq using 1; ring








theorem exists_local_minimizing_identity_of_rescaled_normal_charts
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M)
    (hcomparison : ∀ a b : ℝ, 0 < a → 0 < b → ∀ α β : ℝ → M,
      α 0 = p → β 0 = p →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
        g.edist (α s) (α t) = ENNReal.ofReal |s - t|) →
      (∀ s ∈ Icc (0 : ℝ) b, ∀ t ∈ Icc (0 : ℝ) b,
        g.edist (β s) (β t) = ENNReal.ofReal |s - t|) →
      ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) b,
        s ^ 2 + t ^ 2 - 2 * s * t *
          ((a ^ 2 + b ^ 2 - (g.edist (α a) (β b)).toReal ^ 2) / (2 * a * b)) ≤
            (g.edist (α s) (β t)).toReal ^ 2)
    (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (q : ℕ → M)
    (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k)
    (hQzero : Tendsto (fun k => Real.sqrt (Q k)) atTop (𝓝 0))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {S : ℝ} (hS : 0 < S)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (htarget : ∀ k, (Φ k).target = (rescaledMetric g (Q k) (hQ k)).ball (q k) S)
    (hradial : ∀ k x, x ∈ Metric.ball 0 S →
      (rescaledMetric g (Q k) (hQ k)).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V) (hzeroV : 0 ∈ V)
    (hconv : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ V →
      TendstoUniformlyOn (fun k => (rescaledMetric g (Q k) (hQ k)).pullbackCoefficients (Φ k))
        h.euclideanCoefficients atTop K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfzero : 0 < f 0)
    (hpotential : TendstoUniformlyOn
      (fun k x => ((rescaledMetric g (Q k) (hQ k)).edist p (Φ k x)).toReal ^ 2 / 2)
      f atTop V) :
    ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ 0 ∈ U ∧ U ⊆ V ∧
      (∀ x ∈ U, 0 < f x) ∧
      ∀ x ∈ U, ∀ z ∈ U, ∀ y ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
        (h.edist x z).toReal = t * (h.edist x y).toReal →
        (h.edist z y).toReal = (1 - t) * (h.edist x y).toReal →
        f z = (1 - t) * f x + t * f y - t * (1 - t) * (h.edist x y).toReal ^ 2 / 2 := by
  let gs : ℕ → RiemannianMetric n M := fun k => rescaledMetric g (Q k) (hQ k)
  obtain ⟨W, hWo, hW0, hWV, hWS, hdist⟩ :=
    exists_uniform_distance_limit_of_normal_chart_coefficients gs h q Φ hS
      hsource htarget hradial hV hzeroV hconv
  have hcont : ContinuousOn f W := by
    apply (hpotential.mono hWV).continuousOn
    apply Frequently.of_forall
    intro k
    exact (((gs k).continuous_toReal_edist p).comp_continuousOn
      ((Φ k).contMDiffOn.continuousOn.mono (by simpa only [hsource k] using hWS))).pow 2 |>.div_const 2
  have hposnb : {x : EuclideanSpace ℝ (Fin n) | 0 < f x} ∈ 𝓝 0 := by
    have hh : Tendsto f (𝓝 0) (𝓝 (f 0)) := hcont.continuousAt (hWo.mem_nhds hW0)
    exact hh.eventually (eventually_gt_nhds hfzero)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hWo.mem_nhds hW0) hposnb)
  let R := min ρ S / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRρ : R < ρ := by
    have := min_le_left ρ S
    dsimp [R]
    linarith
  have hRS : R < S := by
    have := min_le_right ρ S
    dsimp [R]
    linarith
  have hRW : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ W :=
    fun x hx => (hρsub (closedBall_subset_ball hRρ hx)).1
  have hpos (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 (R / 4)) : 0 < f x :=
    (hρsub ((Metric.ball_subset_ball (by linarith : R / 4 ≤ ρ)) hx)).2
  have hUW : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 4) ⊆ W :=
    (fun x hx => hRW (ball_subset_closedBall
      ((Metric.ball_subset_ball (by linarith : R / 4 ≤ R)) hx)))
  refine ⟨Metric.ball 0 (R / 4), isOpen_ball, Metric.mem_ball_self (by positivity),
    hUW.trans hWV, hpos, ?_⟩
  intro x hx z hz y hy t ht hxz hzy
  apply @Poincare.AncientVolume.ScalarRatio.potential_interpolation_of_local_radial_variation
    _ h.toMetricSpace f x z y t ht hxz hzy
  intro _ _
  let a : Fin 3 → EuclideanSpace ℝ (Fin n) := ![z, x, y]
  have ha : ∀ j, a j ∈ Metric.ball 0 (R / 4) := by
    intro j
    fin_cases j
    · exact hz
    · exact hx
    · exact hy
  have hv := local_variation_of_source_and_chart_limits g hc p hcomparison gs h q Φ
    (fun k => Real.sqrt (Q k)) (fun k => Real.sqrt_pos.mpr (hQ k)) hQzero
    (fun k u v => by
      change ((rescaledMetric g (Q k) (hQ k)).edist u v).toReal = _
      rw [rescaledMetric_edist, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)])
    hR hRS hsource htarget hradial hRW hdist f
    (fun u hu => hpotential.tendsto_at (hWV hu)) 2 a ha (fun j => hpos _ (ha j))
  filter_upwards [hv] with c hc'
  obtain ⟨w, _, hw⟩ := hc'
  refine ⟨w, ?_, ?_⟩
  · simpa [a] using hw 0
  · simpa [a] using hw 1

end PoincareConjecture.RiemannianMetric
