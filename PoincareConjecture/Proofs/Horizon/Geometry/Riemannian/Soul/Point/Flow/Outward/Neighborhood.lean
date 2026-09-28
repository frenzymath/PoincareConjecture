import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.Outward.DistanceGap
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.Outward.BusemannGap
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.Outward.HessianSecant
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactHessian
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Extension











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem concave_increment_ge
    {f : ℝ → ℝ} {L s a : ℝ} (hL : 0 < L) (hs : 0 < s) (hsL : s ≤ L)
    (hf : ConcaveOn ℝ (Icc 0 L) f) (ha : a ≤ (f L - f 0) / L) :
    a * s ≤ f s - f 0 := by
  have h := hf.slope_anti (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL.le⟩)
    (show s ∈ Icc 0 L \ {0} from ⟨⟨hs.le, hsL⟩, ne_of_gt hs⟩)
    (show L ∈ Icc 0 L \ {0} from ⟨⟨hL.le, le_rfl⟩, ne_of_gt hL⟩) hsL
  simp only [slope_def_field, sub_zero] at h
  exact (le_div_iff₀ hs).mp (ha.trans h)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem exists_common_inward_potential_neighborhood_of_squared_distance_gap
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p q z : M)
    (hgap : 0 < (g.edist z p).toReal ^ 2 - (g.edist z q).toReal ^ 2 -
      (g.edist q p).toReal ^ 2) :
    ∃ (U : Set M) (rho : M → ℝ) (κ : ℝ), IsOpen U ∧ q ∈ U ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho ∧ 0 < κ ∧ p ∉ U ∧
      ∀ y ∈ U, ∀ γ : ℝ → M,
        g.IsGeodesicOn γ (Icc 0 (g.edist y p).toReal) → γ 0 = y →
        γ (g.edist y p).toReal = p →
        (∀ t ∈ Icc 0 (g.edist y p).toReal,
          g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) →
        (∀ s ∈ Icc 0 (g.edist y p).toReal, ∀ t ∈ Icc 0 (g.edist y p).toReal,
          g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) →
        κ ≤ mvfderiv (𝓡 n) rho y
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) := by
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hc
  have hqp : q ≠ p := by
    intro heq
    change 0 < dist z p ^ 2 - dist z q ^ 2 - dist q p ^ 2 at hgap
    simp [heq] at hgap
  have hLq : 0 < dist q p := dist_pos.mpr hqp
  obtain ⟨W, u, hW, hqW, hu, htouch, hupper, _, _⟩ :=
    g.exists_distance_upper_support_with_common_inward_derivative D hc hsec p q z hgap
  obtain ⟨rho, hrho, heq⟩ :=
    Poincare.Manifold.exists_contMDiff_eq_near hW (hu.pow 2) hqW
  have htouch' : rho q = dist z q ^ 2 := by
    calc
      rho q = u q ^ 2 := heq.self_of_nhds
      _ = dist z q ^ 2 := congrArg (fun b : ℝ => b ^ 2) htouch
  have hmajor : ∀ᶠ y in 𝓝 q, dist z y ^ 2 ≤ rho y := by
    filter_upwards [heq, hW.mem_nhds hqW] with y hy hyW
    rw [hy]
    have hb : dist z y ≤ u y := hupper y hyW
    exact (sq_le_sq₀ dist_nonneg (dist_nonneg.trans hb)).2 hb
  let A : M → ℝ := fun y => dist z p ^ 2 - dist z y ^ 2 - dist y p ^ 2
  let a : ℝ := (A q / dist q p) / 2
  have hAq : 0 < A q := hgap
  have ha : 0 < a := half_pos (div_pos hAq hLq)
  have hratio : ContinuousAt (fun y => A y / dist y p) q :=
    (continuous_const.sub ((continuous_const.dist continuous_id).pow 2) |>.sub
      ((continuous_id.dist continuous_const).pow 2)).continuousAt.div
      (continuous_id.dist continuous_const).continuousAt hLq.ne'
  have hnear : ∀ᶠ y in 𝓝 q, a < A y / dist y p ∧ dist q p / 2 < dist y p := by
    exact (hratio.eventually (eventually_gt_nhds
      (half_lt_self (div_pos hAq hLq)))).and
      ((continuous_id.dist continuous_const).continuousAt.eventually
        (eventually_gt_nhds (half_lt_self hLq)))
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff.mp (hmajor.and hnear)
  let r : ℝ := min r₁ 1
  have hr : 0 < r := lt_min hr₁ zero_lt_one
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrone : r ≤ 1 := min_le_right _ _
  obtain ⟨B, hB, hHess⟩ := D.exists_metric_hessian_bound_on_compact hrho
    (isCompact_closedBall q (1 : ℝ))
  let s : ℝ := min (r / 4) (min (dist q p / 4) (a / (4 * (B + 1))))
  have hs : 0 < s := by dsimp only [s]; positivity
  have hsr : s ≤ r / 4 := min_le_left _ _
  have hsL : s ≤ dist q p / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hsB : s ≤ a / (4 * (B + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hBs : B * s ≤ a / 4 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 4 * (B + 1))).mp hsB
    nlinarith only [hb, hs.le]
  have hdef : Continuous (fun y => rho y - dist z y ^ 2) :=
    hrho.continuous.sub ((continuous_const.dist continuous_id).pow 2)
  let U : Set M := Metric.ball q (r / 4) ∩
    {y | rho y - dist z y ^ 2 < a * s / 4}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt hdef continuous_const)
  have hqU : q ∈ U := by
    refine ⟨Metric.mem_ball_self (by positivity), ?_⟩
    change rho q - dist z q ^ 2 < a * s / 4
    rw [htouch', sub_self]
    positivity
  have hyball {y : M} (hy : y ∈ U) : y ∈ Metric.ball q r₁ := by
    exact Metric.ball_subset_ball (by linarith) hy.1
  have hpU : p ∉ U := by
    intro hp
    have hp' := (hball (hyball hp)).2.2
    simp only [dist_self] at hp'
    linarith
  refine ⟨U, rho, a / 2, hU, hqU, hrho, half_pos ha, hpU, ?_⟩
  intro y hy γ hγ hγ0 hγL hspeed hmin
  let L : ℝ := dist y p
  have hynear := (hball (hyball hy)).2
  have hL : 0 < L := (half_pos hLq).trans hynear.2
  have hsL' : s ≤ L := by dsimp only [L]; linarith [hynear.2]
  have hsub : Icc (0 : ℝ) s ⊆ Icc 0 L :=
    fun t ht => ⟨ht.1, ht.2.trans hsL'⟩
  have hdist (t : ℝ) (ht : t ∈ Icc 0 s) : dist y (γ t) = t := by
    change (g.edist y (γ t)).toReal = t
    have h := congrArg ENNReal.toReal
      (hmin 0 ⟨le_rfl, hL.le⟩ t (hsub ht))
    simpa only [hγ0, zero_sub, abs_neg, abs_of_nonneg ht.1,
      ENNReal.toReal_ofReal ht.1] using h
  have hcurveball (t : ℝ) (ht : t ∈ Icc 0 s) : γ t ∈ Metric.ball q r := by
    have hyq : dist y q < r / 4 := hy.1
    have htri := dist_triangle (γ t) y q
    rw [dist_comm (γ t) y, hdist t ht] at htri
    change dist (γ t) q < r
    linarith [ht.2]
  have hcurvesq (t : ℝ) (ht : t ∈ Icc 0 s) : dist z (γ t) ^ 2 ≤ rho (γ t) :=
    (hball (Metric.ball_subset_ball hrr₁ (hcurveball t ht))).1
  have hcurvehess (t : ℝ) (ht : t ∈ Ioo 0 s) :
      D.hessian rho (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) ≤ B := by
    have htcc : t ∈ Icc 0 s := ⟨ht.1.le, ht.2.le⟩
    have hmem : γ t ∈ Metric.closedBall q 1 :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hrone (hcurveball t htcc))
    have hunit := Real.sqrt_eq_one.mp (hspeed t (hsub htcc))
    have hb := hHess (γ t) hmem (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
    exact (le_abs_self _).trans (by simpa only [hunit, mul_one] using hb)
  have hquad := D.endpoint_value_sub_le_of_geodesic_hessian_le hs.le
    isOpen_univ hrho.contMDiffOn (fun t ht => hγ t (hsub ht))
    (fun _ _ => mem_univ _) (fun t ht => hspeed t (hsub ht)) hcurvehess
  rw [hγ0] at hquad
  have hconc := g.squared_distance_sub_sq_concave D hc hsec z hγ hspeed hmin
  change ConcaveOn ℝ (Icc 0 L) (fun t => dist z (γ t) ^ 2 - t ^ 2) at hconc
  have hγL' : γ L = p := hγL
  have hincr : a * s ≤ dist z (γ s) ^ 2 - s ^ 2 - dist z y ^ 2 := by
    have ha' : a ≤ (dist z (γ L) ^ 2 - L ^ 2 -
        (dist z (γ 0) ^ 2 - (0 : ℝ) ^ 2)) / L := by
      rw [hγ0, hγL']
      simp only [zero_pow (by decide : 2 ≠ 0), sub_zero]
      have heq : dist z p ^ 2 - L ^ 2 - dist z y ^ 2 = A y := by
        dsimp only [A, L]
        ring
      rw [heq]
      exact hynear.1.le
    have h := concave_increment_ge hL hs hsL' hconc ha'
    simpa only [hγ0, zero_pow (by decide : 2 ≠ 0), sub_zero] using h
  have hmaj := hcurvesq s ⟨hs.le, le_rfl⟩
  have hdeficit : rho y - dist z y ^ 2 < a * s / 4 := hy.2
  have hBss : B * s ^ 2 ≤ a * s / 4 := by
    nlinarith only [mul_le_mul_of_nonneg_right hBs hs.le]
  have hincrement : 3 * a * s / 4 < rho (γ s) - rho y := by
    nlinarith only [hincr, hmaj, hdeficit, sq_nonneg s]
  by_contra hfail
  have hbad := mul_lt_mul_of_pos_left (lt_of_not_ge hfail) hs
  have hquad' : rho (γ s) - rho y ≤
      s * mvfderiv (𝓡 n) rho y (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) +
        B * s ^ 2 / 2 := hquad
  have hupper' : rho (γ s) - rho y < 3 * a * s / 4 := by
    nlinarith only [hquad', hBss, hbad, mul_pos ha hs]
  exact (not_lt_of_ge hincrement.le) hupper'



theorem exists_common_inward_potential_neighborhood
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {o p : M} {c : ℝ}
    (hlevel : letI := g.toMetricSpace;
      Poincare.Riemannian.Soul.horoballIntersection o c = {p})
    {q : M} (hqp : q ≠ p) :
    ∃ (U : Set M) (rho : M → ℝ) (κ : ℝ), IsOpen U ∧ q ∈ U ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho ∧ 0 < κ ∧ p ∉ U ∧
      ∀ y ∈ U, ∀ γ : ℝ → M,
        g.IsGeodesicOn γ (Icc 0 (g.edist y p).toReal) → γ 0 = y →
        γ (g.edist y p).toReal = p →
        (∀ t ∈ Icc 0 (g.edist y p).toReal,
          g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) →
        (∀ s ∈ Icc 0 (g.edist y p).toReal, ∀ t ∈ Icc 0 (g.edist y p).toReal,
          g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) →
        κ ≤ mvfderiv (𝓡 n) rho y
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) := by
  let := g.toMetricSpace
  obtain ⟨z, hz⟩ :=
    Poincare.Riemannian.Soul.exists_squared_distance_gap_of_singleton_horoball hlevel hqp
  exact g.exists_common_inward_potential_neighborhood_of_squared_distance_gap D hc hsec
    p q z hz

end PoincareConjecture.RiemannianMetric
