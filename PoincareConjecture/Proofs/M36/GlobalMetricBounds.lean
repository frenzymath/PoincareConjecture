import PoincareConjecture.Proofs.M36.SurgeryDistance
import PoincareConjecture.Proofs.M36.MetricSizeBounds
import PoincareConjecture.Proofs.M36.NeckMetricUpper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem adaptedClippedCollapse_quadratic_end (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : z.2 < 4) (v : StandardCylinderCoordinates) :
    g₀.metric.inner (adaptedClippedCollapse g₀ (surgeryCapRadius g₀) z)
      (mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀)) z v)
      (mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀)) z v) =
      RoundCylinderMetric z v v := by
  let T : StandardCylinderSpace → StandardCylinderSpace :=
    fun w => (w.1, surgeryCapRadius g₀ - w.2)
  have hT : ContMDiff IC IC ∞ T :=
    contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
  have hs : z.2 < surgeryCapRadius g₀ := by
    dsimp [surgeryCapRadius]
    linarith [g₀.cylindrical_end.radius_pos]
  have heq : adaptedClippedCollapse g₀ (surgeryCapRadius g₀)
      =ᶠ[nhds z] adaptedPolarPoint g₀ ∘ T := by
    filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hs] with w hw
    exact adaptedClippedCollapse_of_lt g₀ _ w hw
  have hd := heq.mfderiv_eq (I := IC) (I' := 𝓡 3)
  rw [mfderiv_comp z ((adaptedPolarPoint_contMDiff g₀ (T z)).mdifferentiableAt (by simp))
    ((hT z).mdifferentiableAt (by simp))] at hd
  have hdv := congrArg (fun L => L v) hd
  change mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀)) z v =
    mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) (T z) (mfderiv IC IC T z v) at hdv
  rw [show mfderiv IC IC T z v = (v.1, -v.2) from
    cylinder_height_reversal_mfderiv _ z v] at hdv
  rw [hdv, adaptedClippedCollapse_of_lt g₀ _ z hs]
  have h := adaptedPolarPoint_quadratic_end g₀ (T z)
    (by dsimp [T, surgeryCapRadius]; linarith) (v.1, -v.2)
  convert! h using 1
  change 2 * (1 - (0 : ℝ)) * _ + v.2 * v.2 =
    2 * (1 - (0 : ℝ)) * _ + (-v.2) * (-v.2)
  ring

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem surgeryBackground_collapse_eq (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) (hs : (N.coordinate_inverse x).2 < 4)
    (v : TangentSpace (𝓡 3) x) :
    metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) (surgeryCollapse g₀ N x)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v) =
      RoundCylinderMetric (N.coordinate_inverse x)
        (mfderiv (𝓡 3) IC N.coordinate_inverse x v)
        (mfderiv (𝓡 3) IC N.coordinate_inverse x v) := by
  have hs' : (N.coordinate_inverse x).2 < surgeryCapRadius g₀ := by
    dsimp [surgeryCapRadius]
    linarith [g₀.cylindrical_end.radius_pos]
  have hc := (surgeryCollapse_contMDiffAt_before_tip g₀ N hx hs').mdifferentiableAt (by simp)
  have hj := (surgeryBallInclusion_contMDiff g₀ _ (surgeryCollapse g₀ N x)).mdifferentiableAt
    (by simp)
  have hi := (neck_inverse_contMDiffAt N hx).mdifferentiableAt (by simp)
  have hp := ((adaptedClippedCollapse_contMDiffOn g₀ _ _ hs').contMDiffAt
    ((isOpen_lt continuous_snd continuous_const).mem_nhds hs')).mdifferentiableAt (by simp)
  have heq : surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) ∘ surgeryCollapse g₀ N
      =ᶠ[nhds x] adaptedClippedCollapse g₀ (surgeryCapRadius g₀) ∘ N.coordinate_inverse := by
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    exact surgeryCollapse_inclusion g₀ N hy
  have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x hj hc, mfderiv_comp x hp hi] at hd
  have hdv := congrArg (fun L => L v) hd
  change mfderiv (𝓡 3) (𝓡 3) (surgeryBallInclusion g₀ _) (surgeryCollapse g₀ N x)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v) =
    mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀))
      (N.coordinate_inverse x) (mfderiv (𝓡 3) IC N.coordinate_inverse x v) at hdv
  rw [metricPullbackForm_apply, surgeryCollapse_inclusion g₀ N hx]
  erw [hdv]
  exact adaptedClippedCollapse_quadratic_end g₀ _ hs _

theorem neck_inverse_cylinder_upper (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x) :
    N.connection.scalarCurvature N.center * g.inner x v v ≤
      (1 + 6 * N.epsilon) * RoundCylinderMetric (N.coordinate_inverse x)
        (mfderiv (𝓡 3) IC N.coordinate_inverse x v)
        (mfderiv (𝓡 3) IC N.coordinate_inverse x v) := by
  have h := normalizedNeck_bounded_above N (N.coordinate_inverse x)
    (N.coordinate_inverse_mem x hx).2 (mfderiv (𝓡 3) IC N.coordinate_inverse x v)
  unfold roundCylinderPullback at h
  rw [neck_coordinate_inverse_comp_mfderiv N hx, neck_coordinate_inverse N hx] at h
  exact h

theorem surgeryCollapse_comp_mfderiv_inverse (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y ≠ 0)
    (v : TangentSpace (𝓡 3) y) :
    mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) (surgeryRetainedInverse g₀ N y)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y v) = v := by
  have hF := (surgeryRetainedInverse_contMDiffAt g₀ N hcut hy).mdifferentiableAt (by simp)
  have hs : (N.coordinate_inverse (surgeryRetainedInverse g₀ N y)).2 < surgeryCapRadius g₀ := by
    rw [surgeryRetainedInverse_height g₀ N hcut]
    have hR := radialArclength_pos g₀ (norm_pos_iff.mpr hy)
    linarith
  have hC := (surgeryCollapse_contMDiffAt_before_tip g₀ N
    (surgeryRetainedInverse_mem g₀ N hcut y) hs).mdifferentiableAt (by simp)
  have hinv : surgeryCollapse g₀ N ∘ surgeryRetainedInverse g₀ N =ᶠ[nhds y] id :=
    Filter.Eventually.of_forall (surgeryCollapse_right_inverse g₀ N hcut)
  have hd := hinv.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp y hC hF, mfderiv_id] at hd
  exact congrArg (fun L => L v) hd

theorem surgeryNeck_quadratic_bounds (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : y ∈ surgeryTransitionDomain g₀ N) (v : TangentSpace (𝓡 3) y) :
    (1 - 6 * N.epsilon) * metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) y v v ≤
      N.connection.scalarCurvature N.center *
        metricPullbackForm g (surgeryRetainedInverse g₀ N) y v v ∧
      N.connection.scalarCurvature N.center *
        metricPullbackForm g (surgeryRetainedInverse g₀ N) y v v ≤
      (1 + 6 * N.epsilon) * metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) y v v := by
  have hx := surgeryRetainedInverse_mem g₀ N hcut y
  have hs : (N.coordinate_inverse (surgeryRetainedInverse g₀ N y)).2 < 4 := by
    rw [surgeryRetainedInverse_height g₀ N hcut]
    change g₀.cylindrical_end.radius + 2 <
      radialArclength g₀ ‖surgeryBallInclusion g₀ _ y‖ at hy
    dsimp [surgeryCapRadius]
    linarith
  have hb := surgeryBackground_collapse_eq g₀ N hx hs
    (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y v)
  rw [surgeryCollapse_comp_mfderiv_inverse g₀ N hcut
    (surgeryTransitionDomain_ne_zero g₀ N hy), surgeryCollapse_right_inverse g₀ N hcut] at hb
  rw [metricPullbackForm_apply (g := g), hb]
  exact ⟨neck_inverse_cylinder_bound N hx _, neck_inverse_cylinder_upper N hx _⟩

theorem surgeryMetric_global_bounds (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (hsmall : N.epsilon < 1 / 200) {C : ℝ} (hC : 0 ≤ C) (q : ℝ)
    {r : ℝ} (hr : 0 < r) (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon))
    (v : TangentSpace (𝓡 3) y) :
    ((1 - 6 * N.epsilon) * Real.exp (-2 * C * N.epsilon)) *
        metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) y v v ≤
      N.connection.scalarCurvature N.center *
        (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r N.scalar_center_pos
          (neck_contraction_coefficient_pos N hsmall) hr).inner y v v ∧
      N.connection.scalarCurvature N.center *
        (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r N.scalar_center_pos
          (neck_contraction_coefficient_pos N hsmall) hr).inner y v v ≤
      (1 + 6 * N.epsilon) * metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) y v v := by
  let a := surgeryNeckWeight g₀ N y
  let b := metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) y v v
  let n := metricPullbackForm g (surgeryRetainedInverse g₀ N) y v v
  let m := surgeryConformalMultiplier g₀ N C q r y
  let lam := N.connection.scalarCurvature N.center
  let eta := 1 - 6 * N.epsilon
  let blend := a * (lam * n) + (1 - a) * (eta * b)
  have ha : 0 ≤ a ∧ a ≤ 1 := radialNeckWeight_bounds g₀ _
  have hb : 0 ≤ b := metric_inner_nonneg g₀.metric _ _
  have heta : 0 < eta := neck_contraction_coefficient_pos N hsmall
  have hmlo : Real.exp (-2 * C * N.epsilon) ≤ m :=
    radialConformalMultiplier_ge_exp g₀ hC N.epsilon_pos.le q r _
  have hmhi : m ≤ 1 := radialConformalMultiplier_le_one g₀ hC q N.epsilon_pos.le r _
  have hmpos : 0 ≤ m := (radialConformalMultiplier_pos g₀ C q N.epsilon r _).le
  have hblend : eta * b ≤ blend ∧ blend ≤ (1 + 6 * N.epsilon) * b := by
    by_cases ha0 : a = 0
    · dsimp [blend]
      rw [ha0]
      constructor
      · simp
      · simp only [zero_mul, zero_add, sub_zero, one_mul]
        dsimp [eta]
        nlinarith [mul_nonneg N.epsilon_pos.le hb]
    · have hy : y ∈ surgeryTransitionDomain g₀ N :=
        surgeryNeckWeight_tsupport g₀ N (subset_tsupport _ (show a ≠ 0 from ha0))
      have hn := surgeryNeck_quadratic_bounds g₀ N hcut hy v
      change eta * b ≤ lam * n ∧ lam * n ≤ (1 + 6 * N.epsilon) * b at hn
      have hnlo := mul_le_mul_of_nonneg_left hn.1 ha.1
      have hnhi := mul_le_mul_of_nonneg_left hn.2 ha.1
      have hetahi : eta * b ≤ (1 + 6 * N.epsilon) * b := by
        dsimp [eta]
        nlinarith [mul_nonneg N.epsilon_pos.le hb]
      have hback := mul_le_mul_of_nonneg_left hetahi (sub_nonneg.mpr ha.2)
      dsimp [blend]
      constructor <;> nlinarith only [hnlo, hnhi, hback]
  have hvalue : N.connection.scalarCurvature N.center *
      (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r N.scalar_center_pos
        (neck_contraction_coefficient_pos N hsmall) hr).inner y v v = m * blend := by
    rw [surgeryMetric_inner]
    dsimp [m, blend, a, b, n, lam, eta]
    field_simp [ne_of_gt N.scalar_center_pos]
  rw [hvalue]
  constructor
  · calc
      _ = Real.exp (-2 * C * N.epsilon) * (eta * b) := by dsimp [eta, b]; ring
      _ ≤ m * (eta * b) := mul_le_mul_of_nonneg_right hmlo (mul_nonneg heta.le hb)
      _ ≤ m * blend := mul_le_mul_of_nonneg_left hblend.1 hmpos
  · calc
      _ ≤ m * ((1 + 6 * N.epsilon) * b) := mul_le_mul_of_nonneg_left hblend.2 hmpos
      _ ≤ 1 * ((1 + 6 * N.epsilon) * b) :=
        mul_le_mul_of_nonneg_right hmhi (mul_nonneg (by have := N.epsilon_pos; positivity) hb)
      _ = _ := one_mul _

end PoincareConjecture.M36
