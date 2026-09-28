import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CenterSelection
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.MovingRadiusConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.SpireCenters
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.LimitRankGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.LowerCurvature

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open Poincare.GromovHausdorff Poincare.Alexandrov Poincare.CurvatureIntegral
open scoped Manifold ContDiff Bundle
universe u
namespace PoincareConjecture.RiemannianMetric

private theorem pointConverges_base_of_tendsto_dist
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (S : VaryingRealizationSequence X Y) (u : ∀ j, (X j).carrier)
    (hu : Tendsto (fun j => dist (X j).base (u j)) atTop (𝓝 0)) :
    S.PointConverges u Y.base := by
  change Tendsto (fun j => dist (S.left j (u j)) (S.right j Y.base)) atTop (𝓝 0)
  simpa only [← S.base_agree, (S.left_isometry _).dist_eq, dist_comm] using hu

private theorem exists_metric_segment_of_complete
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (hc : PoincareConjecture.MetricComplete g)
    (x y : M) :
    letI := g.toMetricSpace
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y := by
  obtain ⟨_, _, γ, _, h0, h1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc x y
  refine ⟨γ, h0, h1, ?_⟩
  intro s hs t ht
  change (g.edist (γ s) (γ t)).toReal = |s - t| * (g.edist x y).toReal
  rw [hmin s hs t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

theorem tendsto_radius_and_dist_zero_of_selected_centers_at_scaled_spire
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p q : ∀ j, M j)
    {V : BasedMetricSpaceBundle.{u}} [ProperSpace V.carrier]
    (holdconv : PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V)
    {σ cminus c cplus b ρ cap : ℝ}
    (hσ : 0 < σ)
    (hc : 0 ≤ c)
    (hminus : cminus < c) (hplus : c < cplus)
    (hρ : 0 < ρ) (hρb : ρ < σ * b / 2) (hbcap : b ≤ cap)
    (hascent : ∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
      HasLocalDistanceAscent cplus V.base y)
    (B : V.carrier → ℝ)
    (hmax : ∀ x : V.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : V.carrier, 0 < dist x y → dist x y < 2 * a →
        HasLocalDistanceAscent cminus x y) → a ≤ B x)
    (hspire : ∀ y : V.carrier, y ≠ V.base → σ * B y ≤ dist y V.base)
    (hqball : ∀ j, ((g j).edist (p j) (q j)).toReal ≤ ρ)
    (hqref : ∀ j, letI := (g j).toMetricSpace
      badAscentRadius c b (q j) ≤ badAscentRadius c b (p j)) :
    Tendsto (fun j => letI := (g j).toMetricSpace; badAscentRadius c b (q j))
      atTop (𝓝 0) ∧
    Tendsto (fun j => ((g j).edist (p j) (q j)).toReal) atTop (𝓝 0) := by
  classical
  let (j : ℕ) : MetricSpace (M j) := (g j).toMetricSpace
  let (j : ℕ) : ProperSpace (M j) := (g j).properSpace_toMetricSpace (hcomplete j)
  have hb : 0 < b :=
    pos_of_mul_pos_right (by linarith only [hρ, hρb] : 0 < σ * b) hσ.le
  let L₀ : ℝ := ρ + 2 * b + 1
  have hL₀ : 0 < L₀ := by dsimp [L₀]; positivity
  have hρL : ρ < L₀ := by dsimp [L₀]; linarith only [hb]
  obtain ⟨δ₀, hδ₀, hpos₀, hconv₀⟩ := holdconv L₀ hL₀
  let A₀ : ℕ → FiniteDiameterBasedMetricSpace.{u} := fun j =>
    ballModel ((g j).toBasedMetricSpace (p j)) (L₀ + δ₀ j) (hpos₀ j)
  let V₀ : FiniteDiameterBasedMetricSpace.{u} := ballModel V L₀ hL₀
  let S₀ := realizationSequenceOfPointedGHConverges A₀ V₀ hconv₀
  have hpconv : S₀.PointConverges (fun j => (A₀ j).base) V₀.base :=
    pointConverges_base_of_tendsto_dist S₀ (fun j => (A₀ j).base)
      (by
        change Tendsto (fun j => dist (A₀ j).base (A₀ j).base) atTop (𝓝 0)
        simpa only [dist_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  have hroom₀ : dist V.base V₀.base.val + 2 * b < L₀ := by
    change dist V.base V.base + 2 * b < L₀
    simp only [dist_self, zero_add]
    dsimp [L₀]
    linarith only [hρ]
  have hpzero : Tendsto (fun j => badAscentRadius c b (p j)) atTop (𝓝 0) :=
    tendsto_badAscentRadius_zero_of_moving_centers g D hcomplete hsec p
      hL₀ δ₀ hδ₀ hpos₀ S₀ (fun j => (A₀ j).base) V₀.base hpconv hb hplus
      hroom₀ hascent
  have hqzero : Tendsto (fun j => badAscentRadius c b (q j)) atTop (𝓝 0) :=
    squeeze_zero (fun j => badAscentRadius_nonneg c b (q j)) hqref hpzero
  let q₀ : ∀ j, (A₀ j).carrier := fun j =>
    if h : dist (q j) (p j) < L₀ + δ₀ j then ⟨q j, h⟩ else (A₀ j).base
  have hq₀eq : ∀ᶠ j in atTop, (q₀ j).val = q j := by
    filter_upwards [hδ₀.eventually_const_lt (show ρ - L₀ < 0 by linarith)] with j hj
    have hinside : dist (q j) (p j) < L₀ + δ₀ j := by
      rw [dist_comm]
      change ((g j).edist (p j) (q j)).toReal < _
      linarith only [hqball j, hj]
    simp only [q₀, dif_pos hinside]
  have hq₀bound (j : ℕ) :
      dist ((g j).toBasedMetricSpace (p j)).base (q₀ j).val ≤ ρ := by
    dsimp only [q₀]
    split_ifs
    · exact hqball j
    · change dist (p j) (p j) ≤ ρ
      simpa only [dist_self] using hρ.le
  have hq₀zero : Tendsto (fun j => badAscentRadius c b (q₀ j).val) atTop (𝓝 0) :=
    hqzero.congr' (by filter_upwards [hq₀eq] with j hj; rw [hj])
  let : ∀ j, ProperSpace ((g j).toBasedMetricSpace (p j)).carrier :=
    fun j => (g j).properSpace_toMetricSpace (hcomplete j)
  have hpq₀ : Tendsto (fun j => dist (p j) (q₀ j).val) atTop (𝓝 0) :=
    tendsto_dist_base_zero_of_badAscentRadius_zero_at_scaled_spire hσ hL₀ hρ hρb hbcap
      (by dsimp [L₀]; linarith only [hb])
      δ₀ hδ₀ hpos₀ S₀ q₀ hq₀bound hc hminus B hmax hspire hq₀zero
  have hpq : Tendsto (fun j => dist (p j) (q j)) atTop (𝓝 0) :=
    hpq₀.congr' (by filter_upwards [hq₀eq] with j hj; rw [hj])
  exact ⟨hqzero, hpq⟩

theorem rank_growth_of_mul_near_min_badAscentRadius_at_scaled_spire
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p q : ∀ j, M j)
    {V Y : BasedMetricSpaceBundle.{u}} [ProperSpace V.carrier] [ProperSpace Y.carrier]
    (holdconv : PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V)
    {σ θ cminus c cplus b ρ cap : ℝ}
    (hσ : 0 < σ)
    (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2 * θ))
    (hminus : cminus < c) (hplus : c < cplus)
    (hρ : 0 < ρ) (hρb : ρ < σ * b / 2) (hbcap : b ≤ cap)
    (hascent : ∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
      HasLocalDistanceAscent cplus V.base y)
    (B : V.carrier → ℝ)
    (hmax : ∀ x : V.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : V.carrier, 0 < dist x y → dist x y < 2 * a →
        HasLocalDistanceAscent cminus x y) → a ≤ B x)
    (hspire : ∀ y : V.carrier, y ≠ V.base → σ * B y ≤ dist y V.base)
    (hqball : ∀ j, ((g j).edist (p j) (q j)).toReal ≤ ρ)
    (hqref : ∀ j, letI := (g j).toMetricSpace
      badAscentRadius c b (q j) ≤ badAscentRadius c b (p j))
    (hqmin : ∀ j, letI := (g j).toMetricSpace
      ∀ z : M j, dist (p j) z ≤ ρ →
        badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z)
    (κ : ℝ) (hκ : 0 < κ)
    (t : ℕ → ℝ)
    (ht : ∀ j, 0 < t j)
    (htactual : ∀ j, t j = κ * (letI := (g j).toMetricSpace; badAscentRadius c b (q j)))
    {Z : ℕ → BasedMetricSpaceBundle.{u}}
    (F : ∀ j, M j ≃ (Z j).carrier)
    (hFcenter : ∀ j, F j (q j) = (Z j).base)
    (hscale : ∀ j (x y : M j),
      ((g j).edist x y).toReal = t j * dist (F j x) (F j y))
    (hnewconv : PointedGHConvergesUnbounded Z Y) :
    Tendsto t atTop (𝓝 0) ∧ (∀ᶠ j in atTop, t j ≤ 1) ∧
    (∀ k : ℕ, HasSmallAngleConfiguration θ V.base k →
      ∀ y : Y.carrier, HasSmallAngleConfiguration θ y (k + 1)) ∧
    (∀ NV NY : ℕ, ComparisonAnglePackingBound V.carrier θ NV →
      ComparisonAnglePackingBound Y.carrier θ NY →
        minLocalAnglePackingRank V.carrier θ < minLocalAnglePackingRank Y.carrier θ) := by
  classical
  let (j : ℕ) : MetricSpace (M j) := (g j).toMetricSpace
  let (j : ℕ) : ProperSpace (M j) := (g j).properSpace_toMetricSpace (hcomplete j)
  have hb : 0 < b :=
    pos_of_mul_pos_right (by linarith only [hρ, hρb] : 0 < σ * b) hσ.le
  let L₀ : ℝ := ρ + 2 * b + 1
  have hL₀ : 0 < L₀ := by dsimp [L₀]; positivity
  obtain ⟨δ₀, hδ₀, hpos₀, hconv₀⟩ := holdconv L₀ hL₀
  let A₀ : ℕ → FiniteDiameterBasedMetricSpace.{u} := fun j =>
    ballModel ((g j).toBasedMetricSpace (p j)) (L₀ + δ₀ j) (hpos₀ j)
  let V₀ : FiniteDiameterBasedMetricSpace.{u} := ballModel V L₀ hL₀
  let S₀ := realizationSequenceOfPointedGHConverges A₀ V₀ hconv₀
  have hroom₀ : dist V.base V₀.base.val + 2 * b < L₀ := by
    change dist V.base V.base + 2 * b < L₀
    simp only [dist_self, zero_add]
    dsimp [L₀]
    linarith only [hρ]
  obtain ⟨hqzero, hpq⟩ := tendsto_radius_and_dist_zero_of_selected_centers_at_scaled_spire
    g D hcomplete hsec p q holdconv hσ hc hminus hplus hρ hρb hbcap
    hascent B hmax hspire hqball hqref
  change Tendsto (fun j => dist (p j) (q j)) atTop (𝓝 0) at hpq
  have htzero : Tendsto t atTop (𝓝 0) := by
    simpa only [← htactual, mul_zero] using hqzero.const_mul κ
  have hgrowth : ∀ k : ℕ, HasSmallAngleConfiguration θ V.base k →
      ∀ y : Y.carrier, HasSmallAngleConfiguration θ y (k + 1) := by
    intro k hold y₀
    let L : ℝ := dist Y.base y₀ + 1
    have hL : 0 < L := by dsimp [L]; positivity
    have hy₀L : y₀ ∈ Metric.ball Y.base L := by
      change dist y₀ Y.base < dist Y.base y₀ + 1
      rw [dist_comm]
      linarith
    let Y₀ : FiniteDiameterBasedMetricSpace.{u} := ballModel Y L hL
    let u₀ : Y₀.carrier := ⟨y₀, hy₀L⟩
    obtain ⟨δ, hδ, hpos, hconv⟩ := hnewconv L hL
    let A : ℕ → FiniteDiameterBasedMetricSpace.{u} := fun j =>
      ballModel (Z j) (L + δ j) (hpos j)
    let S := realizationSequenceOfPointedGHConverges A Y₀ hconv
    have hcompact : IsCompact (Metric.closedBall Y₀.base (L / 2)) :=
      isCompact_closedBall_ballModel Y hL Y₀.base
        (by change dist Y.base Y.base + L / 2 < L; simp only [dist_self, zero_add]; linarith)
    obtain ⟨f, hf, _⟩ := exists_approximating_maps_and_subseq_pointConverges S
      (ρ := 0) (σ := L / 2) (half_pos hL) hcompact
      (fun j => (A j).base) (fun j => by simp)
    let u : ∀ j, (A j).carrier := fun j => f j u₀
    have hu : S.PointConverges u u₀ := hf u₀
    let z : ∀ j, M j := fun j => (F j).symm (u j).val
    have hFz (j : ℕ) : F j (z j) = (u j).val := (F j).apply_symm_apply _
    have hqz : Tendsto (fun j => dist (q j) (z j)) atTop (𝓝 0) := by
      have hprod := htzero.mul (S.tendsto_dist_base u u₀ hu)
      simp only [zero_mul] at hprod
      convert hprod using 1
      funext j
      change ((g j).edist (q j) (z j)).toReal = t j * dist (Z j).base (u j).val
      rw [hscale, hFcenter, hFz]
    have hpz : Tendsto (fun j => dist (p j) (z j)) atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) (fun j => dist_triangle (p j) (q j) (z j))
        (by simpa only [add_zero] using hpq.add hqz)
    have hzselect : ∀ᶠ j in atTop, z j ∈ Metric.closedBall (p j) ρ :=
      eventually_mem_closedBall_of_tendsto_dist_zero p q z hρ hpq hqz
    have hzold : ∀ᶠ j in atTop, dist (z j) (p j) < L₀ + δ₀ j := by
      filter_upwards [hpz.eventually_lt_const (half_pos hL₀),
        hδ₀.eventually_const_lt (show -L₀ / 2 < 0 by linarith)] with j hj hk
      rw [dist_comm]
      linarith only [hj, hk]
    obtain ⟨φ, hφ, hφold⟩ := Filter.extraction_of_frequently_atTop hzold.frequently
    have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
    let v : ∀ j, (A₀ (φ j)).carrier := fun j => ⟨z (φ j), hφold j⟩
    have hv : (S₀.comp φ hφtop).PointConverges v V₀.base :=
      pointConverges_base_of_tendsto_dist (S₀.comp φ hφtop) v (hpz.comp hφtop)
    have hazero : Tendsto (fun j => badAscentRadius c b (z (φ j))) atTop (𝓝 0) :=
      tendsto_badAscentRadius_zero_of_moving_centers
        (fun j => g (φ j)) (fun j => D (φ j)) (fun j => hcomplete (φ j))
        (fun j => hsec (φ j)) (fun j => p (φ j))
        hL₀ (fun j => δ₀ (φ j)) (hδ₀.comp hφtop) (fun j => hpos₀ (φ j))
        (S₀.comp φ hφtop) v V₀.base hv hb hplus hroom₀ hascent
    have hnear : ∀ᶠ j in atTop,
        badAscentRadius c b (q (φ j)) ≤ 2 * badAscentRadius c b (z (φ j)) := by
      filter_upwards [hφtop.eventually hzselect] with j hj
      exact hqmin (φ j) (z (φ j)) (by simpa only [Metric.mem_closedBall, dist_comm] using hj)
    obtain ⟨w, _, hw, hwzero⟩ := exists_bad_points_of_near_min_badAscentRadius c b
      (fun j => q (φ j)) (fun j => z (φ j))
      (Eventually.of_forall (fun j => (mul_pos_iff_of_pos_left hκ).mp
        (by rw [← htactual]; exact ht (φ j)))) hnear hazero
    let X : ℕ → BasedMetricSpaceBundle.{u} := fun j =>
      (g (φ j)).toBasedMetricSpace (z (φ j))
    have hX (j : ℕ) : CurvatureGEnegOne (X j).carrier :=
      (g (φ j)).curvatureGEnegOne_of_sectional_lower_bound
        (D (φ j)) (hcomplete (φ j)) (hsec (φ j))
    have hgeo (j : ℕ) (x y : (X j).carrier) :
        ∃ γ : ℝ → (X j).carrier, γ 0 = x ∧ γ 1 = y ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (γ s) (γ t) = |s - t| * dist x y :=
      exists_metric_segment_of_complete (g (φ j)) (hcomplete (φ j)) x y
    apply hasSmallAngleConfiguration_succ_of_old_limit (X := X)
      (Z := fun j => Z (φ j)) hL₀ (S₀.comp φ hφtop)
      (fun _ a => a.val) (fun _ => by intro x y; rfl)
      v V₀.base hv (fun _ => rfl)
      hL (fun j => δ (φ j)) (hδ.comp hφtop) (fun j => hpos (φ j))
      (S.comp φ hφtop) (fun j => u (φ j)) u₀ (hu.comp φ hφtop)
      hX hgeo (fun j => t (φ j)) (fun j => ht (φ j)) (htzero.comp hφtop)
      (fun j => F (φ j)) (fun j => hFz (φ j))
      (fun j x y => hscale (φ j) x y)
      hθ hθpi hc hcθ (show 0 < 1 / (4 * κ) by positivity)
      hold w hwzero
    · filter_upwards [hw] with j hj
      change 1 / (4 * κ) * t (φ j) ≤ dist (z (φ j)) (w j)
      rw [htactual]
      have heq : 1 / (4 * κ) * (κ * badAscentRadius c b (q (φ j))) =
          badAscentRadius c b (q (φ j)) / 4 := by field_simp
      rw [heq]
      exact hj.1.le
    · filter_upwards [hw] with j hj
      exact hj.2.2
  refine ⟨htzero, ?_, hgrowth, ?_⟩
  · filter_upwards [htzero.eventually_lt_const zero_lt_one] with j hj
    exact hj.le
  · intro NV NY hpackV hpackY
    let : Nonempty V.carrier := ⟨V.base⟩
    let : Nonempty Y.carrier := ⟨Y.base⟩
    have hold := (localAnglePackingRank_spec hpackV V.base).1.mono
      ((minLocalAnglePackingRank_spec hpackV).2.1 V.base)
    obtain ⟨y, hy⟩ := (minLocalAnglePackingRank_spec hpackY).1
    have hlt := (hgrowth _ hold y).lt_localAnglePackingRank_of_succ hpackY
    rwa [hy] at hlt

theorem rank_growth_of_near_min_badAscentRadius_at_scaled_spire
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p q : ∀ j, M j)
    {V Y : BasedMetricSpaceBundle.{u}} [ProperSpace V.carrier] [ProperSpace Y.carrier]
    (holdconv : PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V)
    {σ θ cminus c cplus b ρ cap : ℝ}
    (hσ : 0 < σ)
    (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2 * θ))
    (hminus : cminus < c) (hplus : c < cplus)
    (hρ : 0 < ρ) (hρb : ρ < σ * b / 2) (hbcap : b ≤ cap)
    (hascent : ∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
      HasLocalDistanceAscent cplus V.base y)
    (B : V.carrier → ℝ)
    (hmax : ∀ x : V.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : V.carrier, 0 < dist x y → dist x y < 2 * a →
        HasLocalDistanceAscent cminus x y) → a ≤ B x)
    (hspire : ∀ y : V.carrier, y ≠ V.base → σ * B y ≤ dist y V.base)
    (hqball : ∀ j, ((g j).edist (p j) (q j)).toReal ≤ ρ)
    (hqref : ∀ j, letI := (g j).toMetricSpace
      badAscentRadius c b (q j) ≤ badAscentRadius c b (p j))
    (hqmin : ∀ j, letI := (g j).toMetricSpace
      ∀ z : M j, dist (p j) z ≤ ρ →
        badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z)
    (t : ℕ → ℝ)
    (ht : ∀ j, 0 < t j)
    (htactual : ∀ j, t j = (letI := (g j).toMetricSpace; badAscentRadius c b (q j)))
    {Z : ℕ → BasedMetricSpaceBundle.{u}}
    (F : ∀ j, M j ≃ (Z j).carrier)
    (hFcenter : ∀ j, F j (q j) = (Z j).base)
    (hscale : ∀ j (x y : M j),
      ((g j).edist x y).toReal = t j * dist (F j x) (F j y))
    (hnewconv : PointedGHConvergesUnbounded Z Y) :
    (∀ k : ℕ, HasSmallAngleConfiguration θ V.base k →
      ∀ y : Y.carrier, HasSmallAngleConfiguration θ y (k + 1)) ∧
    (∀ NV NY : ℕ, ComparisonAnglePackingBound V.carrier θ NV →
      ComparisonAnglePackingBound Y.carrier θ NY →
        minLocalAnglePackingRank V.carrier θ < minLocalAnglePackingRank Y.carrier θ) := by
  exact (rank_growth_of_mul_near_min_badAscentRadius_at_scaled_spire
    g D hcomplete hsec p q holdconv hσ hθ hθpi hc hcθ hminus hplus hρ hρb hbcap
    hascent B hmax hspire hqball hqref hqmin 1 zero_lt_one t ht
    (fun j => by simpa only [one_mul] using htactual j)
    F hFcenter hscale hnewconv).2.2

theorem tendsto_radius_and_dist_zero_of_selected_centers
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p q : ∀ j, M j)
    {V : BasedMetricSpaceBundle.{u}} [ProperSpace V.carrier]
    (holdconv : PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V)
    {cminus c cplus b ρ cap : ℝ}
    (hc : 0 ≤ c)
    (hminus : cminus < c) (hplus : c < cplus)
    (hρ : 0 < ρ) (hρb : ρ < b / 2) (hbcap : b ≤ cap)
    (hascent : ∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
      HasLocalDistanceAscent cplus V.base y)
    (B : V.carrier → ℝ)
    (hmax : ∀ x : V.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : V.carrier, 0 < dist x y → dist x y < 2 * a →
        HasLocalDistanceAscent cminus x y) → a ≤ B x)
    (hspire : ∀ y : V.carrier, y ≠ V.base → B y ≤ dist y V.base)
    (hqball : ∀ j, ((g j).edist (p j) (q j)).toReal ≤ ρ)
    (hqref : ∀ j, letI := (g j).toMetricSpace
      badAscentRadius c b (q j) ≤ badAscentRadius c b (p j)) :
    Tendsto (fun j => letI := (g j).toMetricSpace; badAscentRadius c b (q j))
      atTop (𝓝 0) ∧
    Tendsto (fun j => ((g j).edist (p j) (q j)).toReal) atTop (𝓝 0) := by
  exact tendsto_radius_and_dist_zero_of_selected_centers_at_scaled_spire
    (σ := 1) g D hcomplete hsec p q holdconv zero_lt_one hc hminus hplus
    hρ (by simpa only [one_mul] using hρb) hbcap hascent B hmax
    (fun y hy => by simpa only [one_mul] using hspire y hy) hqball hqref

theorem rank_growth_of_mul_near_min_badAscentRadius
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p q : ∀ j, M j)
    {V Y : BasedMetricSpaceBundle.{u}} [ProperSpace V.carrier] [ProperSpace Y.carrier]
    (holdconv : PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V)
    {θ cminus c cplus b ρ cap : ℝ}
    (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2 * θ))
    (hminus : cminus < c) (hplus : c < cplus)
    (hρ : 0 < ρ) (hρb : ρ < b / 2) (hbcap : b ≤ cap)
    (hascent : ∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
      HasLocalDistanceAscent cplus V.base y)
    (B : V.carrier → ℝ)
    (hmax : ∀ x : V.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : V.carrier, 0 < dist x y → dist x y < 2 * a →
        HasLocalDistanceAscent cminus x y) → a ≤ B x)
    (hspire : ∀ y : V.carrier, y ≠ V.base → B y ≤ dist y V.base)
    (hqball : ∀ j, ((g j).edist (p j) (q j)).toReal ≤ ρ)
    (hqref : ∀ j, letI := (g j).toMetricSpace
      badAscentRadius c b (q j) ≤ badAscentRadius c b (p j))
    (hqmin : ∀ j, letI := (g j).toMetricSpace
      ∀ z : M j, dist (p j) z ≤ ρ →
        badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z)
    (κ : ℝ) (hκ : 0 < κ)
    (t : ℕ → ℝ)
    (ht : ∀ j, 0 < t j)
    (htactual : ∀ j, t j = κ * (letI := (g j).toMetricSpace; badAscentRadius c b (q j)))
    {Z : ℕ → BasedMetricSpaceBundle.{u}}
    (F : ∀ j, M j ≃ (Z j).carrier)
    (hFcenter : ∀ j, F j (q j) = (Z j).base)
    (hscale : ∀ j (x y : M j),
      ((g j).edist x y).toReal = t j * dist (F j x) (F j y))
    (hnewconv : PointedGHConvergesUnbounded Z Y) :
    Tendsto t atTop (𝓝 0) ∧ (∀ᶠ j in atTop, t j ≤ 1) ∧
    (∀ k : ℕ, HasSmallAngleConfiguration θ V.base k →
      ∀ y : Y.carrier, HasSmallAngleConfiguration θ y (k + 1)) ∧
    (∀ NV NY : ℕ, ComparisonAnglePackingBound V.carrier θ NV →
      ComparisonAnglePackingBound Y.carrier θ NY →
        minLocalAnglePackingRank V.carrier θ < minLocalAnglePackingRank Y.carrier θ) := by
  exact rank_growth_of_mul_near_min_badAscentRadius_at_scaled_spire
    (σ := 1) g D hcomplete hsec p q holdconv zero_lt_one hθ hθpi hc hcθ hminus hplus
    hρ (by simpa only [one_mul] using hρb) hbcap hascent B hmax
    (fun y hy => by simpa only [one_mul] using hspire y hy)
    hqball hqref hqmin κ hκ t ht htactual F hFcenter hscale hnewconv

theorem rank_growth_of_near_min_badAscentRadius
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p q : ∀ j, M j)
    {V Y : BasedMetricSpaceBundle.{u}} [ProperSpace V.carrier] [ProperSpace Y.carrier]
    (holdconv : PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V)
    {θ cminus c cplus b ρ cap : ℝ}
    (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2 * θ))
    (hminus : cminus < c) (hplus : c < cplus)
    (hρ : 0 < ρ) (hρb : ρ < b / 2) (hbcap : b ≤ cap)
    (hascent : ∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
      HasLocalDistanceAscent cplus V.base y)
    (B : V.carrier → ℝ)
    (hmax : ∀ x : V.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : V.carrier, 0 < dist x y → dist x y < 2 * a →
        HasLocalDistanceAscent cminus x y) → a ≤ B x)
    (hspire : ∀ y : V.carrier, y ≠ V.base → B y ≤ dist y V.base)
    (hqball : ∀ j, ((g j).edist (p j) (q j)).toReal ≤ ρ)
    (hqref : ∀ j, letI := (g j).toMetricSpace
      badAscentRadius c b (q j) ≤ badAscentRadius c b (p j))
    (hqmin : ∀ j, letI := (g j).toMetricSpace
      ∀ z : M j, dist (p j) z ≤ ρ →
        badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z)
    (t : ℕ → ℝ)
    (ht : ∀ j, 0 < t j)
    (htactual : ∀ j, t j = (letI := (g j).toMetricSpace; badAscentRadius c b (q j)))
    {Z : ℕ → BasedMetricSpaceBundle.{u}}
    (F : ∀ j, M j ≃ (Z j).carrier)
    (hFcenter : ∀ j, F j (q j) = (Z j).base)
    (hscale : ∀ j (x y : M j),
      ((g j).edist x y).toReal = t j * dist (F j x) (F j y))
    (hnewconv : PointedGHConvergesUnbounded Z Y) :
    (∀ k : ℕ, HasSmallAngleConfiguration θ V.base k →
      ∀ y : Y.carrier, HasSmallAngleConfiguration θ y (k + 1)) ∧
    (∀ NV NY : ℕ, ComparisonAnglePackingBound V.carrier θ NV →
      ComparisonAnglePackingBound Y.carrier θ NY →
        minLocalAnglePackingRank V.carrier θ < minLocalAnglePackingRank Y.carrier θ) := by
  exact rank_growth_of_near_min_badAscentRadius_at_scaled_spire
    (σ := 1) g D hcomplete hsec p q holdconv zero_lt_one hθ hθpi hc hcθ hminus hplus
    hρ (by simpa only [one_mul] using hρb) hbcap hascent B hmax
    (fun y hy => by simpa only [one_mul] using hspire y hy)
    hqball hqref hqmin t ht htactual F hFcenter hscale hnewconv

end PoincareConjecture.RiemannianMetric
