import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.RankGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.SubsetRank
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.SuppliedRebase









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open Poincare.GromovHausdorff Poincare.Alexandrov Poincare.CurvatureIntegral
open scoped Manifold ContDiff Bundle
namespace PoincareConjecture.RiemannianMetric
private theorem pointConverges_base_of_radial_zero
    {X : ℕ → BasedMetricSpaceBundle.{0}} {Y : BasedMetricSpaceBundle.{0}}
    (S : VaryingRealizationSequence X Y) (u : ∀ j, (X j).carrier)
    (hu : Tendsto (fun j => dist (X j).base (u j)) atTop (𝓝 0)) :
    S.PointConverges u Y.base := by
  change Tendsto (fun j => dist (S.left j (u j)) (S.right j Y.base)) atTop (𝓝 0)
  have heq : (fun j => dist (S.left j (u j)) (S.right j Y.base)) =
      fun j => dist (X j).base (u j) := by
    funext j
    rw [← S.base_agree j, (S.left_isometry j).dist_eq, dist_comm]
  rw [heq]
  exact hu

private theorem growth_at_rebased_subset_lift
    {n : ℕ} {M : ℕ → Type} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p q z : ∀ j, M j)
    {V Y : BasedMetricSpaceBundle.{0}} [ProperSpace V.carrier] [ProperSpace Y.carrier]
    (holdconv : PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V)
    {θ c cplus b ρ : ℝ}
    (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2 * θ))
    (hplus : c < cplus) (hb : 0 < b) (hρ : 0 < ρ)
    (hascent : ∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
      HasLocalDistanceAscent cplus V.base y)
    (hpq : Tendsto (fun j => ((g j).edist (p j) (q j)).toReal) atTop (𝓝 0))
    (hqz : Tendsto (fun j => ((g j).edist (q j) (z j)).toReal) atTop (𝓝 0))
    (E : ∀ j, Set (M j)) (hzE : ∀ j, z j ∈ E j)
    (hqmin : ∀ j, letI := (g j).toMetricSpace
      ∀ w ∈ E j, dist (p j) w ≤ ρ →
        badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b w)
    (κ : ℝ) (hκ : 0 < κ)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (hazero : Tendsto a atTop (𝓝 0))
    (hactual : ∀ j, a j = κ * (letI := (g j).toMetricSpace; badAscentRadius c b (q j)))
    {Z : ℕ → BasedMetricSpaceBundle.{0}}
    (F : ∀ j, M j ≃ (Z j).carrier)
    (hFz : ∀ j, F j (z j) = (Z j).base)
    (hscale : ∀ j (x y : M j),
      ((g j).edist x y).toReal = a j * dist (F j x) (F j y))
    (hnewconv : PointedGHConvergesUnbounded Z Y)
    {k : ℕ} (hold : HasSmallAngleConfiguration θ V.base k) :
    HasSmallAngleConfiguration θ Y.base (k+1) := by
  classical
  let (j : ℕ) : MetricSpace (M j) := (g j).toMetricSpace
  let (j : ℕ) : ProperSpace (M j) := (g j).properSpace_toMetricSpace (hcomplete j)
  let L₀ : ℝ := ρ + 2*b + 1
  have hL₀ : 0 < L₀ := by dsimp [L₀]; positivity
  obtain ⟨δ₀, hδ₀, hpos₀, hconv₀⟩ := holdconv L₀ hL₀
  let A₀ := fun j => ballModel ((g j).toBasedMetricSpace (p j)) (L₀ + δ₀ j) (hpos₀ j)
  let V₀ := ballModel V L₀ hL₀
  let S₀ := realizationSequenceOfPointedGHConverges A₀ V₀ hconv₀
  have hroom₀ : dist V.base V₀.base.val + 2*b < L₀ := by
    change dist V.base V.base + 2*b < L₀
    simp only [dist_self, zero_add]
    dsimp [L₀]
    linarith only [hρ]
  change Tendsto (fun j => dist (p j) (q j)) atTop (𝓝 0) at hpq
  change Tendsto (fun j => dist (q j) (z j)) atTop (𝓝 0) at hqz
  have hpz : Tendsto (fun j => dist (p j) (z j)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun j => dist_triangle (p j) (q j) (z j))
      (by simpa only [add_zero] using hpq.add hqz)
  have hzselect : ∀ᶠ j in atTop, z j ∈ Metric.closedBall (p j) ρ :=
    eventually_mem_closedBall_of_tendsto_dist_zero p q z hρ hpq hqz
  have hzold : ∀ᶠ j in atTop, dist (z j) (p j) < L₀ + δ₀ j := by
    filter_upwards [hpz.eventually_lt_const (half_pos hL₀),
      hδ₀.eventually_const_lt (show -L₀/2 < 0 by linarith)] with j hj hk
    rw [dist_comm]
    linarith only [hj, hk]
  obtain ⟨φ, hφ, hφold⟩ := Filter.extraction_of_frequently_atTop hzold.frequently
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  let v : ∀ j, (A₀ (φ j)).carrier := fun j => ⟨z (φ j), hφold j⟩
  have hv : (S₀.comp φ hφtop).PointConverges v V₀.base :=
    pointConverges_base_of_radial_zero (S₀.comp φ hφtop) v (hpz.comp hφtop)
  have hradzero : Tendsto (fun j => badAscentRadius c b (z (φ j))) atTop (𝓝 0) :=
    tendsto_badAscentRadius_zero_of_moving_centers
      (fun j => g (φ j)) (fun j => D (φ j)) (fun j => hcomplete (φ j))
      (fun j => hsec (φ j)) (fun j => p (φ j))
      hL₀ (fun j => δ₀ (φ j)) (hδ₀.comp hφtop) (fun j => hpos₀ (φ j))
      (S₀.comp φ hφtop) v V₀.base hv hb hplus hroom₀ hascent
  have hnear : ∀ᶠ j in atTop,
      badAscentRadius c b (q (φ j)) ≤ 2 * badAscentRadius c b (z (φ j)) := by
    filter_upwards [hφtop.eventually hzselect] with j hj
    exact hqmin (φ j) (z (φ j)) (hzE (φ j))
      (by simpa only [Metric.mem_closedBall, dist_comm] using hj)
  obtain ⟨w, _, hw, hwzero⟩ := exists_bad_points_of_near_min_badAscentRadius c b
    (fun j => q (φ j)) (fun j => z (φ j))
    (Eventually.of_forall (fun j => (mul_pos_iff_of_pos_left hκ).mp
      (by rw [← hactual]; exact ha (φ j)))) hnear hradzero
  obtain ⟨δ, hδ, hpos, hnew⟩ := hnewconv 1 (by norm_num)
  let S := realizationSequenceOfPointedGHConverges
    (fun j => ballModel (Z j) (1 + δ j) (hpos j)) (ballModel Y 1 (by norm_num)) hnew
  let u := fun j => (ballModel (Z j) (1 + δ j) (hpos j)).base
  let u₀ := (ballModel Y 1 (by norm_num)).base
  have hu : S.PointConverges u u₀ :=
    pointConverges_base_of_radial_zero S u
      (by
        change Tendsto (fun j => dist (Z j).base (Z j).base) atTop (𝓝 0)
        simpa only [dist_self] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  let X := fun j => (g (φ j)).toBasedMetricSpace (z (φ j))
  have hX (j : ℕ) : CurvatureGEnegOne (X j).carrier :=
    (g (φ j)).curvatureGEnegOne_of_sectional_lower_bound
      (D (φ j)) (hcomplete (φ j)) (hsec (φ j))
  have hgeo (j : ℕ) (x y : (X j).carrier) :
      ∃ γ : ℝ → (X j).carrier, γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s-t| * dist x y := by
    obtain ⟨_, _, γ, _, h0, h1, hmin⟩ :=
      (g (φ j)).exists_minimizing_geodesic_of_metricComplete (hcomplete (φ j)) x y
    refine ⟨γ, h0, h1, ?_⟩
    intro s hs t ht
    change ((g (φ j)).edist (γ s) (γ t)).toReal =
      |s-t| * ((g (φ j)).edist x y).toReal
    rw [hmin s hs t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  apply hasSmallAngleConfiguration_succ_of_old_limit (X := X)
    (Z := fun j => Z (φ j)) hL₀ (S₀.comp φ hφtop)
    (fun _ x => x.val) (fun _ => by intro x y; rfl)
    v V₀.base hv (fun _ => rfl)
    (show (0 : ℝ) < 1 by norm_num) (fun j => δ (φ j)) (hδ.comp hφtop)
    (fun j => hpos (φ j)) (S.comp φ hφtop) (fun j => u (φ j)) u₀
    (hu.comp φ hφtop) hX hgeo (fun j => a (φ j)) (fun j => ha (φ j))
    (hazero.comp hφtop) (fun j => F (φ j)) (fun j => hFz (φ j))
    (fun j x y => hscale (φ j) x y)
    hθ hθpi hc hcθ (show 0 < 1 / (4*κ) by positivity) hold w hwzero
  · filter_upwards [hw] with j hj
    change 1/(4*κ) * a (φ j) ≤ dist (z (φ j)) (w j)
    rw [hactual]
    have heq : 1/(4*κ) * (κ * badAscentRadius c b (q (φ j))) =
        badAscentRadius c b (q (φ j))/4 := by field_simp
    rw [heq]
    exact hj.1.le
  · filter_upwards [hw] with j hj
    exact hj.2.2



theorem minLocalAnglePackingRankOn_lt_of_expanding_subset_near_min_badAscentRadius
    {n : ℕ} {M : ℕ → Type} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p q : ∀ j, M j)
    {V Y : BasedMetricSpaceBundle.{0}} [ProperSpace V.carrier] [ProperSpace Y.carrier]
    (holdconv : PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V)
    {θ c cplus b ρ : ℝ}
    (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2 * θ))
    (hplus : c < cplus) (hb : 0 < b) (hρ : 0 < ρ)
    (hascent : ∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
      HasLocalDistanceAscent cplus V.base y)
    (hpq : Tendsto (fun j => ((g j).edist (p j) (q j)).toReal) atTop (𝓝 0))
    (E : ∀ j, Set (M j))
    (hqmin : ∀ j, letI := (g j).toMetricSpace
      ∀ z ∈ E j, dist (p j) z ≤ ρ →
        badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z)
    (κ : ℝ) (hκ : 0 < κ)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (hazero : Tendsto a atTop (𝓝 0))
    (hactual : ∀ j, a j = κ * (letI := (g j).toMetricSpace; badAscentRadius c b (q j)))
    {Z : ℕ → BasedMetricSpaceBundle.{0}} [∀ j, ProperSpace (Z j).carrier]
    (F : ∀ j, M j ≃ (Z j).carrier)
    (hFcenter : ∀ j, F j (q j) = (Z j).base)
    (hscale : ∀ j (x y : M j),
      ((g j).edist x y).toReal = a j * dist (F j x) (F j y))
    (hZgeo : ∀ j, ∀ x y : (Z j).carrier,
      ∃ γ : ℝ → (Z j).carrier, γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    (hYgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier,
      γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    {R : ℝ} (hR : 0 ≤ R)
    {s t : ℕ → ℝ} (hs : ∀ j, 0 < s j) (ht : ∀ j, R < t j)
    (hsTop : Tendsto s atTop atTop) (htTop : Tendsto t atTop atTop)
    (Q : ∀ j, PointedGHRealization (ballModel (Z j) (s j) (hs j))
      (ballModel Y (t j) (hR.trans_lt (ht j))))
    (hQ : Tendsto (fun j => pointedHausdorffDist (Q j)) atTop (𝓝 0))
    (K : Set Y.carrier) (hK : K.Nonempty)
    (hKR : K ⊆ Metric.closedBall Y.base R)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hback : ∀ j (y : K), ∃ x : (ballModel (Z j) (s j) (hs j)).carrier,
      (F j).symm x.val ∈ E j ∧
      dist ((Q j).left x)
        ((Q j).right ⟨y.val, Metric.mem_ball'.mpr
          ((Metric.mem_closedBall'.mp (hKR y.property)).trans_lt (ht j))⟩) < ε j)
    (Kold : Set V.carrier) (hbase : V.base ∈ Kold)
    {NV NY : ℕ}
    (hpackV : ComparisonAnglePackingBound V.carrier θ NV)
    (hpackY : ComparisonAnglePackingBound Y.carrier θ NY) :
    minLocalAnglePackingRankOn θ Kold < minLocalAnglePackingRankOn θ K := by
  classical
  apply lt_minLocalAnglePackingRankOn_of_pointwise_growth hbase hK hpackV hpackY
  intro l hold y hy
  let yK : K := ⟨y, hy⟩
  choose x hxE hxy using fun j => hback j yK
  let yB (j : ℕ) : (ballModel Y (t j) (hR.trans_lt (ht j))).carrier :=
    ⟨y, Metric.mem_ball'.mpr
      ((Metric.mem_closedBall'.mp (hKR hy)).trans_lt (ht j))⟩
  have hcross : Tendsto (fun j => dist ((Q j).left (x j)) ((Q j).right (yB j)))
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun j => (hxy j).le) hε
  have hrad : Tendsto (fun j => dist (Z j).base (x j).val)
      atTop (𝓝 (dist Y.base y)) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hε.eventually_lt_const hη] with j hj
    have h := abs_dist_base_sub_dist_base_lt_of_corresponding (Q j) (x j) (yB j) (hxy j)
    change |dist (Z j).base (x j).val - dist Y.base y| < ε j at h
    simpa only [Real.dist_eq] using h.trans hj
  let z : ∀ j, M j := fun j => (F j).symm (x j).val
  have hFz (j : ℕ) : F j (z j) = (x j).val := (F j).apply_symm_apply _
  have hqz : Tendsto (fun j => ((g j).edist (q j) (z j)).toReal) atTop (𝓝 0) := by
    have hprod := hazero.mul hrad
    simp only [zero_mul] at hprod
    convert hprod using 1
    funext j
    rw [hscale, hFcenter, hFz]
  have hrebased := pointedGHConvergesUnbounded_rebase_of_expanding_realizations
    hZgeo hYgeo hs (fun j => hR.trans_lt (ht j)) hsTop htTop Q hQ x yB y
    (Eventually.of_forall (fun _ => rfl)) hcross
  let : ProperSpace (Y.rebase y).carrier :=
    show ProperSpace Y.carrier from inferInstance
  exact growth_at_rebased_subset_lift
    (Z := fun j => (Z j).rebase (x j).val) (Y := Y.rebase y)
    g D hcomplete hsec p q z holdconv hθ hθpi hc hcθ hplus hb hρ hascent hpq hqz
    E hxE hqmin κ hκ a ha hazero hactual (fun j => F j) hFz hscale hrebased hold


end PoincareConjecture.RiemannianMetric
