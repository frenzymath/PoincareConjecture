import PoincareConjecture.Proofs.M36.CylindricalHeight

set_option autoImplicit false

open scoped Manifold ContDiff ENNReal Topology

namespace PoincareConjecture.M36

theorem cylindrical_inverse_height_ray_bound (g₀ : StandardInitialMetric)
    {u : StandardCapSpace} (hu : ‖u‖ = 1) {q : ℝ}
    (hq : g₀.cylindrical_end.radius < radialArclength g₀ ‖q • u‖) :
    ‖deriv (fun s : ℝ => (g₀.cylindrical_end.inverse (s • u)).2) q‖ ≤
      radialSpeed g₀ q := by
  have hheight : DifferentiableAt ℝ
      (fun x : StandardCapSpace => (g₀.cylindrical_end.inverse x).2) (q • u) :=
    (cylindrical_inverse_contMDiffAt g₀ hq).snd.contDiffAt.differentiableAt (by simp)
  have hgamma : HasDerivAt (fun s : ℝ => s • u) u q := by
    convert! (hasDerivAt_id q).smul_const u using 1
    simp
  have hderiv := hheight.hasFDerivAt.comp_hasDerivAt q hgamma
  simp only [Function.comp_def] at hderiv
  rw [hderiv.deriv, Real.norm_eq_abs]
  apply (cylindrical_inverse_height_differential_bound g₀ hq u).trans_eq
  unfold RiemannianMetric.tangentNorm
  rw [unit_ray_metric g₀ u hu]
  rfl

theorem cylindrical_radial_height_lower (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) {t : ℝ} (ht : 0 ≤ t) :
    g₀.cylindrical_end.radius + t ≤
      radialArclength g₀ ‖g₀.cylindrical_end.coordinate (theta, t)‖ := by
  let x := g₀.cylindrical_end.coordinate (theta, t)
  let a := radialEuclideanRadius g₀ g₀.cylindrical_end.radius
  let b := ‖x‖
  let u := ‖x‖⁻¹ • x
  let H : ℝ → ℝ := fun q => (g₀.cylindrical_end.inverse (q • u)).2
  have hx : x ≠ 0 := cylindrical_coordinate_ne_zero g₀ (theta, t) ht
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, norm_ne_zero_iff.mpr hx]
  have ha : 0 < a :=
    (radialEuclideanRadius_pos_iff g₀ _).mpr g₀.cylindrical_end.radius_pos
  have hFa : radialArclength g₀ a = g₀.cylindrical_end.radius :=
    radialArclength_euclideanRadius g₀ _
  have hab : a ≤ b := (radialArclength_strictMono g₀).le_iff_le.mp (by
    rw [hFa]
    exact cylindrical_coordinate_radial_ge g₀ (theta, t) ht)
  have hnorm : ∀ q, a ≤ q → ‖q • u‖ = q := by
    intro q hq
    simp [norm_smul, hu, abs_of_nonneg (ha.le.trans hq)]
  have hcarrier : ∀ q, a ≤ q → q • u ∈ g₀.cylindrical_end.carrier := by
    intro q hq
    rw [cylindrical_carrier_eq, Set.mem_ofPred_eq, hnorm q hq, ← hFa]
    exact (radialArclength_strictMono g₀).monotone hq
  have hstrict : ∀ q, a < q →
      g₀.cylindrical_end.radius < radialArclength g₀ ‖q • u‖ := by
    intro q hq
    rw [hnorm q hq.le, ← hFa]
    exact radialArclength_strictMono g₀ hq
  have hstart : H a = 0 := cylindrical_inverse_boundary g₀ (by
    rw [hnorm a le_rfl, hFa])
  have hend : H b = t := by
    have hbu : b • u = x := by simp [b, u, smul_smul, norm_ne_zero_iff.mpr hx]
    change (g₀.cylindrical_end.inverse (b • u)).2 = t
    rw [hbu]
    exact congrArg Prod.snd
      (g₀.cylindrical_end.coordinate_left_inverse (x := (theta, t)) ⟨Set.mem_univ _, ht⟩)
  have hcont : ContinuousOn H (Set.Icc a b) :=
    g₀.cylindrical_end.inverse_smooth.continuousOn.snd.comp
      (continuous_id.smul continuous_const).continuousOn
      (fun q hq => hcarrier q hq.1)
  have hdiff : DifferentiableOn ℝ H (Set.Ioo a b) := by
    intro q hq
    exact (((cylindrical_inverse_contMDiffAt g₀ (hstrict q hq.1)).comp q
      (contDiff_id.smul contDiff_const).contMDiff.contMDiffAt).snd.contDiffAt
        |>.differentiableAt (by simp)).differentiableWithinAt
  have hbound := norm_sub_le_integral_of_norm_deriv_le_of_le hab hcont hdiff
    (Filter.Eventually.of_forall fun q hq =>
      cylindrical_inverse_height_ray_bound g₀ hu (hstrict q hq.1))
    ((radialSpeed_contDiff g₀).continuous.intervalIntegrable a b)
  have hintegral : (∫ q in a..b, radialSpeed g₀ q) =
      radialArclength g₀ b - radialArclength g₀ a := by
    exact (intervalIntegral.integral_interval_sub_left
      ((radialSpeed_contDiff g₀).continuous.intervalIntegrable 0 b)
      ((radialSpeed_contDiff g₀).continuous.intervalIntegrable 0 a)).symm
  rw [hend, hstart, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht,
    hintegral, hFa] at hbound
  linarith

theorem cylindrical_radial_height (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 ≤ z.2) :
    radialArclength g₀ ‖g₀.cylindrical_end.coordinate z‖ =
      g₀.cylindrical_end.radius + z.2 :=
  le_antisymm (cylindrical_radial_height_upper g₀ z.1 hz)
    (cylindrical_radial_height_lower g₀ z.1 hz)

theorem cylindrical_coordinate_norm (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 ≤ z.2) :
    ‖g₀.cylindrical_end.coordinate z‖ =
      radialEuclideanRadius g₀ (g₀.cylindrical_end.radius + z.2) := by
  apply (radialArclength_strictMono g₀).injective
  rw [cylindrical_radial_height g₀ z hz, radialArclength_euclideanRadius]

end PoincareConjecture.M36
