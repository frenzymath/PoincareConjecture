import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Standard.Cylindrical.CylindricalBoundary









set_option autoImplicit false

open scoped Manifold ContDiff ENNReal Topology

namespace PoincareConjecture.MetricSurgery

theorem cylindrical_coordinate_ne_zero (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 ≤ z.2) :
    g₀.cylindrical_end.coordinate z ≠ 0 := by
  intro hzero
  have hge := cylindrical_coordinate_radial_ge g₀ z hz
  rw [hzero, norm_zero, radialArclength_zero] at hge
  exact (not_le_of_gt g₀.cylindrical_end.radius_pos) hge

theorem cylindrical_vertical_contMDiffAt (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) {s : ℝ} (hs : 0 ≤ s) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞
      (fun t : ℝ => g₀.cylindrical_end.coordinate (theta, t)) s :=
  (cylindrical_coordinate_contMDiffAt g₀ (theta, s)
    (lt_of_lt_of_le (neg_lt_zero.mpr g₀.cylindrical_end.collar_pos) hs)).comp s
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt

theorem cylindrical_vertical_speed (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) {s : ℝ} (hs : 0 ≤ s) :
    metricPathSpeed g₀.metric
      (fun t : ℝ => g₀.cylindrical_end.coordinate (theta, t)) s = 1 := by
  have hC := (cylindrical_coordinate_contMDiffAt g₀ (theta, s)
    (lt_of_lt_of_le (neg_lt_zero.mpr g₀.cylindrical_end.collar_pos) hs)).mdifferentiableAt
      (by simp)
  have hm : mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
      (fun t : ℝ => g₀.cylindrical_end.coordinate (theta, t)) s 1 =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) g₀.cylindrical_end.coordinate
        (theta, s) (0, 1) := by
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
      (g₀.cylindrical_end.coordinate ∘ fun t : ℝ => (theta, t)) s 1 = _
    rw [mfderiv_comp s hC (mdifferentiableAt_const.prodMk mdifferentiableAt_id),
      ContinuousLinearMap.comp_apply, mfderiv_prod_right]
    rfl
  unfold metricPathSpeed RiemannianMetric.tangentNorm
  rw [hm]
  calc
    _ = Real.sqrt (standardCylinderInner 0 (theta, s) (0, 1) (0, 1)) :=
      congrArg Real.sqrt (g₀.cylindrical_end.metric_pullback (theta, s) hs (0, 1) (0, 1))
    _ = 1 := by
      let S : EuclideanSpace ℝ (Fin 2) →L[ℝ] StandardCapSpace :=
        mfderiv (𝓡 2) (𝓡 3) (fun theta : UnitTwoSphere => theta.1) theta
      change Real.sqrt (2 * (1 - 0) * inner ℝ (S 0) (S 0) + (1 : ℝ) * 1) = 1
      simp

theorem cylindrical_radial_height_upper (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) {t : ℝ} (ht : 0 ≤ t) :
    radialArclength g₀ ‖g₀.cylindrical_end.coordinate (theta, t)‖ ≤
      g₀.cylindrical_end.radius + t := by
  let gamma : ℝ → StandardCapSpace := fun s => g₀.cylindrical_end.coordinate (theta, s)
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ gamma (Set.Icc 0 t) :=
    fun s hs => (cylindrical_vertical_contMDiffAt g₀ theta hs.1).contMDiffWithinAt
  have hdiff : ∀ s, 0 ≤ s → DifferentiableAt ℝ gamma s := fun s hs =>
    (cylindrical_vertical_contMDiffAt g₀ theta hs).contDiffAt.differentiableAt (by simp)
  have hbound := norm_sub_le_integral_of_norm_deriv_le_of_le ht
    ((radialArclength_contDiff g₀).continuous.comp_continuousOn hgamma.continuousOn.norm)
    (show DifferentiableOn ℝ (fun s => radialArclength g₀ ‖gamma s‖)
        (Set.Ioo 0 t) from fun s hs =>
      (radial_path_hasDerivAt g₀ (hdiff s hs.1.le).hasDerivAt
        (cylindrical_coordinate_ne_zero g₀ (theta, s) hs.1.le)).differentiableAt
          |>.differentiableWithinAt)
    (Filter.Eventually.of_forall fun s hs => (radial_path_deriv_bound g₀
      (hdiff s hs.1.le) (cylindrical_coordinate_ne_zero g₀ (theta, s) hs.1.le)).trans_eq
        (cylindrical_vertical_speed g₀ theta hs.1.le))
    (intervalIntegrable_const (c := (1 : ℝ)))
  simp only [Function.comp_apply, gamma, cylindrical_zero_radial, Real.norm_eq_abs,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hbound
  linarith [le_abs_self (radialArclength g₀
    ‖g₀.cylindrical_end.coordinate (theta, t)‖ - g₀.cylindrical_end.radius)]

theorem cylindrical_inverse_contMDiffAt (g₀ : StandardInitialMetric)
    {x : StandardCapSpace}
    (hx : g₀.cylindrical_end.radius < radialArclength g₀ ‖x‖) :
    ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ g₀.cylindrical_end.inverse x := by
  have hmem : x ∈ g₀.cylindrical_end.carrier := by
    rw [cylindrical_carrier_eq]
    exact hx.le
  exact (g₀.cylindrical_end.inverse_smooth x hmem).contMDiffAt
    (cylindrical_carrier_mem_nhds g₀ hx)

theorem cylindrical_inverse_boundary (g₀ : StandardInitialMetric)
    {x : StandardCapSpace}
    (hx : radialArclength g₀ ‖x‖ = g₀.cylindrical_end.radius) :
    (g₀.cylindrical_end.inverse x).2 = 0 := by
  have hmem : x ∈ g₀.cylindrical_end.carrier := by
    rw [cylindrical_carrier_eq]
    exact hx.ge
  apply (cylindrical_boundary_iff g₀ _ (g₀.cylindrical_end.inverse_domain x hmem)).mp
  rw [g₀.cylindrical_end.coordinate_right_inverse hmem]
  exact hx

theorem cylindrical_coordinate_inverse_mfderiv (g₀ : StandardInitialMetric)
    {x : StandardCapSpace}
    (hx : g₀.cylindrical_end.radius < radialArclength g₀ ‖x‖)
    (v : StandardCapSpace) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) g₀.cylindrical_end.coordinate
        (g₀.cylindrical_end.inverse x)
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) g₀.cylindrical_end.inverse x v) = v := by
  have hmem : x ∈ g₀.cylindrical_end.carrier := by
    rw [cylindrical_carrier_eq]
    exact hx.le
  have hC := (cylindrical_coordinate_contMDiffAt g₀ (g₀.cylindrical_end.inverse x)
    (lt_of_lt_of_le (neg_lt_zero.mpr g₀.cylindrical_end.collar_pos)
      (g₀.cylindrical_end.inverse_domain x hmem))).mdifferentiableAt (by simp)
  have hJ := (cylindrical_inverse_contMDiffAt g₀ hx).mdifferentiableAt (by simp)
  have heq : g₀.cylindrical_end.coordinate ∘ g₀.cylindrical_end.inverse =ᶠ[nhds x] id := by
    filter_upwards [cylindrical_carrier_mem_nhds g₀ hx] with y hy
    exact g₀.cylindrical_end.coordinate_right_inverse hy
  have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x hC hJ, mfderiv_id] at hd
  exact congrArg (fun L => L v) hd

set_option backward.isDefEq.respectTransparency false in
theorem cylindrical_inverse_height_differential_bound (g₀ : StandardInitialMetric)
    {x : StandardCapSpace}
    (hx : g₀.cylindrical_end.radius < radialArclength g₀ ‖x‖)
    (v : StandardCapSpace) :
    |fderiv ℝ (fun y : StandardCapSpace => (g₀.cylindrical_end.inverse y).2) x v| ≤
      g₀.metric.tangentNorm x v := by
  let z := g₀.cylindrical_end.inverse x
  let w : StandardCylinderCoordinates :=
    mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) g₀.cylindrical_end.inverse x v
  let S : EuclideanSpace ℝ (Fin 2) →L[ℝ] StandardCapSpace :=
    mfderiv (𝓡 2) (𝓡 3) (fun theta : UnitTwoSphere => theta.1) z.1
  have hmem : x ∈ g₀.cylindrical_end.carrier := by
    rw [cylindrical_carrier_eq]
    exact hx.le
  have hm := g₀.cylindrical_end.metric_pullback z
    (g₀.cylindrical_end.inverse_domain x hmem) w w
  rw [cylindrical_coordinate_inverse_mfderiv g₀ hx,
    g₀.cylindrical_end.coordinate_right_inverse hmem] at hm
  change g₀.metric.inner x v v =
    2 * (1 - 0) * inner ℝ (S w.1) (S w.1) + w.2 * w.2 at hm
  have hm' : g₀.metric.inner x v v = 2 * inner ℝ (S w.1) (S w.1) + w.2 * w.2 := by
    simpa only [sub_zero, mul_one] using hm
  have hsq : w.2 ^ 2 ≤ g₀.metric.inner x v v := by
    rw [real_inner_self_eq_norm_sq] at hm'
    nlinarith [sq_nonneg ‖S w.1‖]
  have hderiv : fderiv ℝ (fun y : StandardCapSpace =>
      (g₀.cylindrical_end.inverse y).2) x v = w.2 := by
    have hcomp := mfderiv_comp_apply x mdifferentiableAt_snd
      ((cylindrical_inverse_contMDiffAt g₀ hx).mdifferentiableAt (by simp)) v
    simpa only [mfderiv_eq_fderiv, mfderiv_snd, ContinuousLinearMap.coe_snd',
      TangentSpace, Function.comp_def, w] using hcomp
  rw [hderiv]
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  change |w.2| ^ 2 ≤ (Real.sqrt (g₀.metric.inner x v v)) ^ 2
  rw [sq_abs, Real.sq_sqrt (metric_inner_nonneg g₀.metric x v)]
  exact hsq

end PoincareConjecture.MetricSurgery
