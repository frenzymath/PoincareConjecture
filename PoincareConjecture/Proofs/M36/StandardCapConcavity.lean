import PoincareConjecture.Proofs.M36.StandardCapSectional
import PoincareConjecture.Proofs.M36.RadialCompleteness
import PoincareConjecture.Proofs.M04.RiemannRegularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle
open Filter Set Topology

namespace PoincareConjecture.M36

private theorem warp_axis_norm {r : ℝ} (hr : 0 < r) : ‖axisPoint r‖ = r := by
  rw [axisPoint_eq_smul]
  simp [axisBasis, norm_smul, abs_of_pos hr]

private theorem warp_axis_ne_zero {r : ℝ} (hr : 0 < r) : axisPoint r ≠ 0 :=
  norm_ne_zero_iff.mp ((warp_axis_norm hr).trans_ne hr.ne')

private theorem warp_basis_inner (i j : Fin 3) :
    inner ℝ (axisBasis i) (axisBasis j) = if i = j then 1 else 0 := by
  simp [axisBasis, EuclideanSpace.inner_single_left]

private theorem warp_axis_inner (r : ℝ) (i : Fin 3) :
    inner ℝ (axisPoint r) (axisBasis i) = r * (if 0 = i then 1 else 0) := by
  rw [axisPoint_eq_smul, real_inner_smul_left, warp_basis_inner]

private theorem warp_excess_smooth (g₀ : StandardInitialMetric) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (fun t =>
      (axisRadialCoefficient g₀ t - axisTangentialCoefficient g₀ t) / t ^ 2) r :=
  ((axisRadialCoefficient_contDiff g₀).contDiffAt.sub
    (axisTangentialCoefficient_contDiff g₀).contDiffAt).div
      (contDiffAt_id.pow 2) (pow_ne_zero 2 hr)

private theorem warp_excess_deriv (g₀ : StandardInitialMetric) {r : ℝ} (hr : r ≠ 0) :
    deriv (fun t => (axisRadialCoefficient g₀ t - axisTangentialCoefficient g₀ t) /
      t ^ 2) r =
      ((deriv (axisRadialCoefficient g₀) r - deriv (axisTangentialCoefficient g₀) r) *
        r ^ 2 - (axisRadialCoefficient g₀ r - axisTangentialCoefficient g₀ r) *
          (2 * r)) / (r ^ 2) ^ 2 := by
  have ha := ((axisRadialCoefficient_contDiff g₀).differentiable (by simp) r).hasDerivAt
  have hc := ((axisTangentialCoefficient_contDiff g₀).differentiable (by simp) r).hasDerivAt
  simpa only [Pi.div_def, Pi.sub_def, Pi.pow_def, id_eq,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using
    ((ha.sub hc).div ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr)).deriv

private theorem warp_fderiv_inner (x v w : StandardCapSpace) :
    fderiv ℝ (fun y : StandardCapSpace => inner ℝ y w) x v = inner ℝ v w := by
  change fderiv ℝ ((innerSL ℝ).flip w) x v = _
  rw [ContinuousLinearMap.fderiv]
  rfl

private theorem warp_fderiv_linear {f : ℝ → ℝ} {x : StandardCapSpace}
    (hf : DifferentiableAt ℝ f ‖x‖) (hx : x ≠ 0) (v z : StandardCapSpace) :
    fderiv ℝ (fun y : StandardCapSpace => f ‖y‖ * inner ℝ y v) x z =
      deriv f ‖x‖ * (inner ℝ x z / ‖x‖) * inner ℝ x v +
        f ‖x‖ * inner ℝ z v := by
  erw [fderiv_fun_mul (hf.comp x ((differentiableAt_id (𝕜 := ℝ)).norm ℝ hx))
    (differentiableAt_id.inner ℝ (differentiableAt_const v))]
  simp only [Function.comp_def, id_eq]
  simp only [add_apply, smul_apply, smul_eq_mul,
    standardCap_fderiv_radial hf hx, warp_fderiv_inner]
  ring

private theorem warp_fderiv_cubic {f : ℝ → ℝ} {x : StandardCapSpace}
    (hf : DifferentiableAt ℝ f ‖x‖) (hx : x ≠ 0) (v w z : StandardCapSpace) :
    fderiv ℝ (fun y : StandardCapSpace =>
      f ‖y‖ * (inner ℝ y w) ^ 2 * inner ℝ y v) x z =
      deriv f ‖x‖ * (inner ℝ x z / ‖x‖) * (inner ℝ x w) ^ 2 * inner ℝ x v +
        2 * f ‖x‖ * inner ℝ x w * inner ℝ z w * inner ℝ x v +
          f ‖x‖ * (inner ℝ x w) ^ 2 * inner ℝ z v := by
  have hv : DifferentiableAt ℝ (fun y : StandardCapSpace => inner ℝ y v) x :=
    differentiableAt_id.inner ℝ (differentiableAt_const v)
  have hw : DifferentiableAt ℝ (fun y : StandardCapSpace => inner ℝ y w) x :=
    differentiableAt_id.inner ℝ (differentiableAt_const w)
  have hf' := hf.comp x ((differentiableAt_id (𝕜 := ℝ)).norm ℝ hx)
  erw [fderiv_fun_mul (hf'.mul (hw.pow 2)) hv,
    fderiv_fun_mul hf' (hw.pow 2), fderiv_fun_pow 2 hw]
  simp only [Function.comp_def, Pi.mul_def, Pi.pow_def]
  simp only [add_apply, smul_apply, smul_eq_mul,
    standardCap_fderiv_radial hf hx, warp_fderiv_inner,
    Nat.reduceSub, pow_one]
  ring

private theorem warp_metric_ext (g₀ : StandardInitialMetric) (x : StandardCapSpace)
    {v w : StandardCapSpace}
    (h : ∀ z : StandardCapSpace, g₀.metric.inner x v z = g₀.metric.inner x w z) :
    v = w := by
  by_contra hne
  have hpos := g₀.metric.pos x _ (sub_ne_zero.mpr hne)
  let G : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := g₀.metric.inner x
  have hz : G v (v - w) = G w (v - w) := h (v - w)
  have hzero : g₀.metric.inner x (v - w) (v - w) = 0 := by
    change G (v - w) (v - w) = 0
    rw [map_sub G, sub_apply, hz, sub_self]
  exact hpos.ne' hzero

private theorem warp_connection_axis_radial (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) :
    g₀.connection.connection (fun _ : StandardCapSpace => axisBasis 0)
      (axisPoint r) (axisBasis 0) =
        (deriv (axisRadialCoefficient g₀) r / (2 * axisRadialCoefficient g₀ r)) •
          axisBasis 0 := by
  apply warp_metric_ext g₀ (axisPoint r)
  intro z
  rw [standardCap_connection_inner g₀ (warp_axis_ne_zero hr), warp_axis_norm hr,
    warp_excess_deriv g₀ hr.ne', axis_metric_formula]
  simp [axisPoint_eq_smul, real_inner_smul_left, axisBasis,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  field_simp [hr.ne', (axisRadialCoefficient_pos g₀ r).ne']
  ring

private theorem warp_connection_axis_mixed (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) :
    g₀.connection.connection (fun _ : StandardCapSpace => axisBasis 0)
      (axisPoint r) (axisBasis 1) =
        (deriv (axisTangentialCoefficient g₀) r /
          (2 * axisTangentialCoefficient g₀ r)) • axisBasis 1 := by
  apply warp_metric_ext g₀ (axisPoint r)
  intro z
  rw [standardCap_connection_inner g₀ (warp_axis_ne_zero hr), warp_axis_norm hr,
    axis_metric_formula]
  simp [axisPoint_eq_smul, real_inner_smul_left, axisBasis,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  field_simp [hr.ne', (axisTangentialCoefficient_pos g₀ r).ne']

private theorem warp_constant_smooth (v : StandardCapSpace) :
    ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
      (fun x : StandardCapSpace => (⟨x, v⟩ : TangentBundle (𝓡 3) StandardCapSpace)) :=
  contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const

private theorem warp_constant_bracket (v w : StandardCapSpace) :
    VectorField.mlieBracket (𝓡 3) (fun _ : StandardCapSpace => v)
      (fun _ : StandardCapSpace => w) = 0 := by
  unfold VectorField.mlieBracket
  erw [VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin_univ]
  simp [VectorField.lieBracket]
  rfl

private theorem warp_radial_numerator (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    g₀.metric.inner (axisPoint r)
      (g₀.connection.curvature (axisPoint r) (axisBasis 0) (axisBasis 1) (axisBasis 1))
      (axisBasis 0) =
      deriv (axisRadialCoefficient g₀) r / (2 * r) -
        deriv (axisTangentialCoefficient g₀) r / r -
        deriv (deriv (axisTangentialCoefficient g₀)) r / 2 -
        ((axisRadialCoefficient g₀ r - axisTangentialCoefficient g₀ r) / r ^ 2 -
          deriv (axisTangentialCoefficient g₀) r / (2 * r)) * r *
            (deriv (axisRadialCoefficient g₀) r / (2 * axisRadialCoefficient g₀ r)) +
        (deriv (axisTangentialCoefficient g₀) r) ^ 2 /
          (4 * axisTangentialCoefficient g₀ r) := by
  let x := axisPoint r
  let v := axisBasis 0
  let w := axisBasis 1
  let b : ℝ → ℝ := fun t =>
    (axisRadialCoefficient g₀ t - axisTangentialCoefficient g₀ t) / t ^ 2
  let d : ℝ → ℝ := fun t => deriv (axisTangentialCoefficient g₀) t / (2 * t)
  let e : ℝ → ℝ := fun t => deriv b t / (2 * t)
  let X := fun _ : StandardCapSpace => v
  let Y := fun _ : StandardCapSpace => w
  let W := fun y => g₀.connection.connection Y y w
  let V := fun y => g₀.connection.connection Y y v
  have hx : x ≠ 0 := warp_axis_ne_zero hr
  have hnorm : ‖x‖ = r := warp_axis_norm hr
  have hvv : inner ℝ v v = 1 := by dsimp only [v]; rw [warp_basis_inner, if_pos rfl]
  have hww : inner ℝ w w = 1 := by dsimp only [w]; rw [warp_basis_inner, if_pos rfl]
  have hvw : inner ℝ v w = 0 := by simp [v, w, warp_basis_inner]
  have hwv : inner ℝ w v = 0 := by rw [real_inner_comm, hvw]
  have hxv : inner ℝ x v = r := by simp [x, v, warp_axis_inner]
  have hxw : inner ℝ x w = 0 := by simp [x, w, warp_axis_inner]
  have hb : ContDiffAt ℝ ∞ b ‖x‖ := warp_excess_smooth g₀ (norm_ne_zero_iff.mpr hx)
  have hc' := (contDiff_infty_iff_deriv.mp (axisTangentialCoefficient_contDiff g₀)).2
  have hd : DifferentiableAt ℝ d ‖x‖ :=
    (hc'.contDiffAt.div (contDiffAt_const.mul contDiffAt_id)
      (mul_ne_zero (by norm_num) (norm_ne_zero_iff.mpr hx))).differentiableAt (by simp)
  have he : DifferentiableAt ℝ e ‖x‖ :=
    ((hb.derivWithin (m := ∞) (by simp)).div (contDiffAt_const.mul contDiffAt_id)
      (mul_ne_zero (by norm_num) (norm_ne_zero_iff.mpr hx))).differentiableAt (by simp)
  have hbd : DifferentiableAt ℝ (fun t => b t - d t) ‖x‖ :=
    (hb.differentiableAt (by simp)).sub hd
  have hS : (fun y => g₀.metric.inner y (W y) v) =ᶠ[𝓝 x]
      (fun y => (b ‖y‖ - d ‖y‖) * inner ℝ y v +
        e ‖y‖ * (inner ℝ y w) ^ 2 * inner ℝ y v) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [show W y = g₀.connection.connection (fun _ => w) y w from rfl,
      standardCap_connection_inner g₀ hy]
    simp only [hwv, hww, mul_zero, add_zero, mul_one, zero_add]
    dsimp only [b, d, e]
    ring
  have hT : (fun y => g₀.metric.inner y (V y) v) =ᶠ[𝓝 x]
      (fun y => d ‖y‖ * inner ℝ y w + e ‖y‖ * (inner ℝ y v) ^ 2 * inner ℝ y w) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [show V y = g₀.connection.connection (fun _ => w) y v from rfl,
      standardCap_connection_inner g₀ hy]
    simp only [hwv, hvw, hvv, mul_zero, mul_one, zero_add]
    dsimp only [b, d, e]
    ring
  have hn := (differentiableAt_id (𝕜 := ℝ) (x := x)).norm ℝ hx
  have hl (z : StandardCapSpace) :
      DifferentiableAt ℝ (fun y : StandardCapSpace => inner ℝ y z) x :=
    differentiableAt_id.inner ℝ (differentiableAt_const z)
  have hSd : fderiv ℝ (fun y => g₀.metric.inner y (W y) v) x v =
      (deriv b r - deriv d r) * r + b r - d r := by
    rw [hS.fderiv_eq]
    erw [fderiv_fun_add ((hbd.comp x hn).mul (hl v))
      (((he.comp x hn).mul ((hl w).pow 2)).mul (hl v))]
    simp only [Function.comp_def, Pi.mul_def, Pi.pow_def, add_apply,
      warp_fderiv_linear hbd hx, warp_fderiv_cubic he hx,
      hxv, hxw, hvv, hvw, hnorm]
    rw [deriv_fun_sub (by simpa [hnorm] using hb.differentiableAt (by simp))
      (by simpa [hnorm] using hd)]
    field_simp
    ring
  have hTd : fderiv ℝ (fun y => g₀.metric.inner y (V y) v) x w = d r + e r * r ^ 2 := by
    rw [hT.fderiv_eq]
    erw [fderiv_fun_add ((hd.comp x hn).mul (hl w))
      (((he.comp x hn).mul ((hl v).pow 2)).mul (hl w))]
    simp only [Function.comp_def, Pi.mul_def, Pi.pow_def, add_apply,
      warp_fderiv_linear hd hx, warp_fderiv_cubic he hx,
      hxv, hxw, hwv, hww, hnorm]
    ring
  have hX := warp_constant_smooth v
  have hY := warp_constant_smooth w
  have hW := g₀.connection.contMDiffOn_connection_apply isOpen_univ Y Y
    hY.contMDiffOn hY.contMDiffOn
  have hV := g₀.connection.contMDiffOn_connection_apply isOpen_univ X Y
    hX.contMDiffOn hY.contMDiffOn
  have hDW := g₀.connection.mvfderiv_inner X W X
    ((hW.contMDiffAt (x := x) (by simp)).mdifferentiableAt (by simp))
    ((hX x).mdifferentiableAt (by simp))
  have hDV := g₀.connection.mvfderiv_inner Y V X
    ((hV.contMDiffAt (x := x) (by simp)).mdifferentiableAt (by simp))
    ((hX x).mdifferentiableAt (by simp))
  simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
    NormedSpace.fromTangentSpace] at hDW hDV
  change fderiv ℝ (fun y => g₀.metric.inner y (W y) v) x v =
    g₀.metric.inner x (g₀.connection.connection W x v) v +
      g₀.metric.inner x (W x) (g₀.connection.connection X x v) at hDW
  change fderiv ℝ (fun y => g₀.metric.inner y (V y) v) x w =
    g₀.metric.inner x (g₀.connection.connection V x w) v +
      g₀.metric.inner x (V x) (g₀.connection.connection X x w) at hDV
  rw [hSd, warp_connection_axis_radial g₀ hr] at hDW
  rw [hTd, warp_connection_axis_mixed g₀ hr] at hDV
  simp only [map_smul, smul_eq_mul] at hDW hDV
  have hWv : g₀.metric.inner x (W x) v = (b r - d r) * r := by
    rw [hS.eq_of_nhds]
    simp [hxv, hxw, hnorm]
  have hVw : g₀.metric.inner x (V x) w = d r * r := by
    rw [show V x = g₀.connection.connection (fun _ => w) x v from rfl,
      standardCap_connection_inner g₀ hx]
    simp only [hww, hvw, hxv, hxw, hnorm, mul_zero, mul_one, add_zero]
    dsimp only [d]
  rw [hWv] at hDW
  rw [hVw] at hDV
  rw [← M04.curvatureOnFields_eq_curvature g₀.connection isOpen_univ
    hX.contMDiffOn hY.contMDiffOn hY.contMDiffOn (mem_univ x)]
  change g₀.metric.inner x (g₀.connection.connection W x v -
    g₀.connection.connection V x w -
    g₀.connection.connection Y x (VectorField.mlieBracket (𝓡 3) X Y x)) v = _
  rw [show VectorField.mlieBracket (𝓡 3) X Y x = 0 by
    exact congrFun (warp_constant_bracket v w) x, map_zero, sub_zero]
  simp only [map_sub, sub_apply]
  have hd' : deriv d r =
      (deriv (deriv (axisTangentialCoefficient g₀)) r * (2 * r) -
        deriv (axisTangentialCoefficient g₀) r * 2) / (2 * r) ^ 2 := by
    simpa only [d, Pi.div_def, id_eq, mul_one] using
      (((hc'.differentiable (by simp) r).hasDerivAt).div
      ((hasDerivAt_id r).const_mul 2) (mul_ne_zero (by norm_num) hr.ne')).deriv
  have hb' : deriv b r =
      ((deriv (axisRadialCoefficient g₀) r - deriv (axisTangentialCoefficient g₀) r) *
        r ^ 2 - (axisRadialCoefficient g₀ r - axisTangentialCoefficient g₀ r) *
          (2 * r)) / (r ^ 2) ^ 2 := warp_excess_deriv g₀ hr.ne'
  have halg : (deriv b r - deriv d r) * r + b r - d r -
      deriv (axisRadialCoefficient g₀) r / (2 * axisRadialCoefficient g₀ r) *
        ((b r - d r) * r) -
      (d r + e r * r ^ 2 - deriv (axisTangentialCoefficient g₀) r /
        (2 * axisTangentialCoefficient g₀ r) * (d r * r)) =
      deriv (axisRadialCoefficient g₀) r / (2 * r) -
        deriv (axisTangentialCoefficient g₀) r / r -
        deriv (deriv (axisTangentialCoefficient g₀)) r / 2 -
        (b r - d r) * r *
          (deriv (axisRadialCoefficient g₀) r / (2 * axisRadialCoefficient g₀ r)) +
        (deriv (axisTangentialCoefficient g₀) r) ^ 2 /
          (4 * axisTangentialCoefficient g₀ r) := by
    dsimp only [e]
    rw [hb', hd']
    dsimp only [b, d]
    field_simp [hr.ne', (axisRadialCoefficient_pos g₀ r).ne',
      (axisTangentialCoefficient_pos g₀ r).ne']
    ring
  dsimp only [b, d] at halg
  linarith only [hDW, hDV, halg]




theorem standardCap_sectional_radial (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    g₀.connection.sectionalCurvature (axisPoint r) (axisBasis 0) (axisBasis 1) =
      -deriv (deriv (axisTangentialCoefficient g₀)) r /
          (2 * axisRadialCoefficient g₀ r * axisTangentialCoefficient g₀ r) -
        deriv (axisTangentialCoefficient g₀) r /
          (axisRadialCoefficient g₀ r * r * axisTangentialCoefficient g₀ r) +
        (deriv (axisTangentialCoefficient g₀) r) ^ 2 /
          (4 * axisRadialCoefficient g₀ r * (axisTangentialCoefficient g₀ r) ^ 2) +
        deriv (axisRadialCoefficient g₀) r / (2 * (axisRadialCoefficient g₀ r) ^ 2 * r) +
        deriv (axisRadialCoefficient g₀) r * deriv (axisTangentialCoefficient g₀) r /
          (4 * (axisRadialCoefficient g₀ r) ^ 2 * axisTangentialCoefficient g₀ r) := by
  unfold LeviCivitaData.sectionalCurvature LeviCivitaData.curvatureTensor
  rw [warp_radial_numerator g₀ hr, axis_metric_zero_one]
  change _ / (axisRadialCoefficient g₀ r * axisTangentialCoefficient g₀ r - 0 ^ 2) = _
  field_simp [hr.ne', (axisRadialCoefficient_pos g₀ r).ne',
    (axisTangentialCoefficient_pos g₀ r).ne']
  ring


noncomputable def angularRadiusSlope (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  deriv (euclideanWarpRadius g₀) r / radialSpeed g₀ r

theorem angularRadiusSlope_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (angularRadiusSlope g₀) :=
  ((contDiff_infty_iff_deriv.mp (euclideanWarpRadius_contDiff g₀)).2).div
    (radialSpeed_contDiff g₀) (fun r => (radialSpeed_pos g₀ r).ne')

private theorem warp_radius_deriv (g₀ : StandardInitialMetric) (r : ℝ) :
    deriv (euclideanWarpRadius g₀) r = Real.sqrt (axisTangentialCoefficient g₀ r) +
      r * (deriv (axisTangentialCoefficient g₀) r /
        (2 * Real.sqrt (axisTangentialCoefficient g₀ r))) := by
  have hc := ((axisTangentialCoefficient_contDiff g₀).differentiable (by simp) r).hasDerivAt
  change deriv (fun t => t * Real.sqrt (axisTangentialCoefficient g₀ t)) r = _
  simpa only [Pi.mul_def, id_eq, one_mul] using
    ((hasDerivAt_id r).mul (hc.sqrt (axisTangentialCoefficient_pos g₀ r).ne')).deriv

theorem angularRadiusSlope_eq (g₀ : StandardInitialMetric) (r : ℝ) :
    angularRadiusSlope g₀ r =
      (2 * axisTangentialCoefficient g₀ r + r * deriv (axisTangentialCoefficient g₀) r) /
        (2 * radialSpeed g₀ r * Real.sqrt (axisTangentialCoefficient g₀ r)) := by
  rw [angularRadiusSlope, warp_radius_deriv]
  have hs := Real.sq_sqrt (axisTangentialCoefficient_pos g₀ r).le
  have hs0 := (Real.sqrt_pos.mpr (axisTangentialCoefficient_pos g₀ r)).ne'
  field_simp [(radialSpeed_pos g₀ r).ne', hs0]
  nlinarith only [hs]

private theorem warp_radius_deriv_two (g₀ : StandardInitialMetric) (r : ℝ) :
    deriv (deriv (euclideanWarpRadius g₀)) r =
      deriv (axisTangentialCoefficient g₀) r / Real.sqrt (axisTangentialCoefficient g₀ r) +
        r * deriv (deriv (axisTangentialCoefficient g₀)) r /
          (2 * Real.sqrt (axisTangentialCoefficient g₀ r)) -
        r * (deriv (axisTangentialCoefficient g₀) r) ^ 2 /
          (4 * (Real.sqrt (axisTangentialCoefficient g₀ r)) ^ 3) := by
  have hc := ((axisTangentialCoefficient_contDiff g₀).differentiable (by simp) r).hasDerivAt
  have hc' := ((contDiff_infty_iff_deriv.mp
    (axisTangentialCoefficient_contDiff g₀)).2.differentiable (by simp) r).hasDerivAt
  have hs0 := (Real.sqrt_pos.mpr (axisTangentialCoefficient_pos g₀ r)).ne'
  have hs := hc.sqrt (axisTangentialCoefficient_pos g₀ r).ne'
  have h := (hs.add ((hasDerivAt_id r).mul (hc'.div (hs.const_mul 2)
    (mul_ne_zero (by norm_num) hs0)))).deriv
  have he : deriv (euclideanWarpRadius g₀) = fun t =>
      Real.sqrt (axisTangentialCoefficient g₀ t) + t *
        (deriv (axisTangentialCoefficient g₀) t /
          (2 * Real.sqrt (axisTangentialCoefficient g₀ t))) := funext (warp_radius_deriv g₀)
  rw [he]
  simp only [Pi.mul_def, Pi.div_def, Pi.add_def, id_eq, one_mul] at h
  rw [h]
  field_simp [hs0]
  ring

private theorem warp_speed_deriv (g₀ : StandardInitialMetric) (r : ℝ) :
    deriv (radialSpeed g₀) r =
      deriv (axisRadialCoefficient g₀) r / (2 * radialSpeed g₀ r) :=
  (((axisRadialCoefficient_contDiff g₀).differentiable (by simp) r).hasDerivAt.sqrt
    (axisRadialCoefficient_pos g₀ r).ne').deriv

private theorem warp_slope_deriv (g₀ : StandardInitialMetric) (r : ℝ) :
    deriv (angularRadiusSlope g₀) r =
      (deriv (deriv (euclideanWarpRadius g₀)) r * radialSpeed g₀ r -
        deriv (euclideanWarpRadius g₀) r *
          (deriv (axisRadialCoefficient g₀) r / (2 * radialSpeed g₀ r))) /
            (radialSpeed g₀ r) ^ 2 := by
  have hp := ((contDiff_infty_iff_deriv.mp
    (euclideanWarpRadius_contDiff g₀)).2.differentiable (by simp) r).hasDerivAt
  have hl := ((radialSpeed_contDiff g₀).differentiable (by simp) r).hasDerivAt
  change deriv (fun t => deriv (euclideanWarpRadius g₀) t / radialSpeed g₀ t) r = _
  simpa only [Pi.div_def, warp_speed_deriv] using
    (hp.div hl (radialSpeed_pos g₀ r).ne').deriv



theorem standardCap_sectional_radial_slope (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) :
    g₀.connection.sectionalCurvature (axisPoint r) (axisBasis 0) (axisBasis 1) =
      -deriv (angularRadiusSlope g₀) r / (radialSpeed g₀ r * euclideanWarpRadius g₀ r) := by
  rw [standardCap_sectional_radial g₀ hr, warp_slope_deriv,
    warp_radius_deriv_two, warp_radius_deriv]
  have hl0 := (radialSpeed_pos g₀ r).ne'
  have hs0 := (Real.sqrt_pos.mpr (axisTangentialCoefficient_pos g₀ r)).ne'
  have hl2 : (radialSpeed g₀ r) ^ 2 = axisRadialCoefficient g₀ r :=
    Real.sq_sqrt (axisRadialCoefficient_pos g₀ r).le
  have hs2 := Real.sq_sqrt (axisTangentialCoefficient_pos g₀ r).le
  dsimp only [euclideanWarpRadius]
  generalize hsdef : Real.sqrt (axisTangentialCoefficient g₀ r) = s at *
  generalize hldef : radialSpeed g₀ r = l at *
  rw [← hl2, ← hs2]
  field_simp [hr.ne', hl0, hs0]
  ring

theorem angularRadiusSlope_deriv_nonpos (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) : deriv (angularRadiusSlope g₀) r ≤ 0 := by
  have hK : 0 ≤ g₀.connection.sectionalCurvature (axisPoint r)
      (axisBasis 0) (axisBasis 1) := by
    unfold LeviCivitaData.sectionalCurvature
    apply div_nonneg (g₀.nonnegative_sectional _ _ _)
    rw [axis_metric_zero_one]
    change 0 ≤ axisRadialCoefficient g₀ r * axisTangentialCoefficient g₀ r - 0 ^ 2
    have ha := axisRadialCoefficient_pos g₀ r
    have hc := axisTangentialCoefficient_pos g₀ r
    simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero] using mul_nonneg ha.le hc.le
  rw [standardCap_sectional_radial_slope g₀ hr] at hK
  have hden := mul_pos (radialSpeed_pos g₀ r) (euclideanWarpRadius_pos g₀ hr)
  have h := (le_div_iff₀ hden).mp hK
  linarith only [h]

theorem angularRadiusSlope_antitoneOn (g₀ : StandardInitialMetric) :
    AntitoneOn (angularRadiusSlope g₀) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (angularRadiusSlope_contDiff g₀).continuous.continuousOn
    ((angularRadiusSlope_contDiff g₀).differentiable (by simp)).differentiableOn
  intro r hr
  exact angularRadiusSlope_deriv_nonpos g₀ (by simpa only [interior_Ioi, mem_Ioi] using hr)


theorem angularRadiusSlope_nonneg (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    0 ≤ angularRadiusSlope g₀ r := by
  by_contra h
  have hq : angularRadiusSlope g₀ r < 0 := lt_of_not_ge h
  let H : ℝ → ℝ := fun t => euclideanWarpRadius g₀ t -
    angularRadiusSlope g₀ r * radialArclength g₀ t
  have hd (t : ℝ) : HasDerivAt H
      (radialSpeed g₀ t * (angularRadiusSlope g₀ t - angularRadiusSlope g₀ r)) t := by
    have hp := ((euclideanWarpRadius_contDiff g₀).differentiable (by simp) t).hasDerivAt
    apply (hp.sub ((radialArclength_hasDerivAt g₀ t).const_mul
      (angularRadiusSlope g₀ r))).congr_deriv
    dsimp only [angularRadiusSlope]
    field_simp [(radialSpeed_pos g₀ t).ne']
  have hanti : AntitoneOn H (Ici r) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici r)
      (((euclideanWarpRadius_contDiff g₀).continuous.sub
        ((radialArclength_contDiff g₀).continuous.const_mul _)).continuousOn)
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    have hrt : r < t := by simpa only [interior_Ici, mem_Ioi] using ht
    apply mul_nonpos_of_nonneg_of_nonpos (radialSpeed_pos g₀ t).le
    exact sub_nonpos.mpr (angularRadiusSlope_antitoneOn g₀ hr (hr.trans hrt) hrt.le)
  obtain ⟨t, hrt, ht⟩ := Filter.exists_lt_of_tendsto_atTop
    (radialArclength_tendsto_atTop g₀) r
    (radialArclength g₀ r + euclideanWarpRadius g₀ r / (-angularRadiusSlope g₀ r))
  have hbound := hanti (show r ∈ Ici r by simp) hrt hrt
  have hp := euclideanWarpRadius_pos g₀ (hr.trans_le hrt)
  have hneg : euclideanWarpRadius g₀ r <
      (-angularRadiusSlope g₀ r) * (radialArclength g₀ t - radialArclength g₀ r) := by
    apply (div_lt_iff₀' (neg_pos.mpr hq)).mp
    linarith only [ht]
  dsimp only [H] at hbound
  nlinarith only [hp, hbound, hneg]

theorem euclideanWarpRadius_monotoneOn (g₀ : StandardInitialMetric) :
    MonotoneOn (euclideanWarpRadius g₀) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (euclideanWarpRadius_contDiff g₀).continuous.continuousOn
    ((euclideanWarpRadius_contDiff g₀).differentiable (by simp)).differentiableOn
  intro r hr
  have h := angularRadiusSlope_nonneg g₀ (by simpa only [interior_Ici, mem_Ioi] using hr)
  change 0 ≤ deriv (euclideanWarpRadius g₀) r / radialSpeed g₀ r at h
  simpa only [zero_mul] using (le_div_iff₀ (radialSpeed_pos g₀ r)).mp h

theorem angularRadiusSlope_sq_le_one (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) : (angularRadiusSlope g₀ r) ^ 2 ≤ 1 := by
  rw [angularRadiusSlope_eq, div_pow]
  have he : (2 * radialSpeed g₀ r * Real.sqrt (axisTangentialCoefficient g₀ r)) ^ 2 =
      4 * axisRadialCoefficient g₀ r * axisTangentialCoefficient g₀ r := by
    rw [mul_pow, mul_pow, show (radialSpeed g₀ r) ^ 2 = axisRadialCoefficient g₀ r from
      Real.sq_sqrt (axisRadialCoefficient_pos g₀ r).le,
      Real.sq_sqrt (axisTangentialCoefficient_pos g₀ r).le]
    norm_num
  rw [he]
  have hden : 0 < 4 * axisRadialCoefficient g₀ r * axisTangentialCoefficient g₀ r :=
    mul_pos (mul_pos (by norm_num) (axisRadialCoefficient_pos g₀ r))
      (axisTangentialCoefficient_pos g₀ r)
  exact (div_le_one hden).mpr (standardCap_angular_derivative_sq_le g₀ hr)

private theorem warp_sectional_smul (g₀ : StandardInitialMetric) (x : StandardCapSpace)
    (u v : StandardCapSpace) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    g₀.connection.sectionalCurvature x (a • u) (b • v) =
      g₀.connection.sectionalCurvature x u v := by
  obtain ⟨A, hA⟩ := (M04.isSmoothCovariantTensor_riemannEvaluation g₀.connection).1 x
  have hscale := A.map_smul_univ ![a, b, a, b] ![u, v, u, v]
  have he : (fun i : Fin 4 => ![a, b, a, b] i • ![u, v, u, v] i) =
      ![a • u, b • v, a • u, b • v] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at hscale
  simp only [← hA, LeviCivitaData.riemannEvaluation, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.cons_val_succ,
    Fin.prod_univ_succ, Fin.prod_univ_zero,
    smul_eq_mul, mul_one] at hscale
  have hnum : g₀.connection.curvatureTensor x (a • u) (b • v) (a • u) (b • v) =
      (a ^ 2 * b ^ 2) * g₀.connection.curvatureTensor x u v u v := by
    rw [hscale]
    ring
  have hden : g₀.metric.inner x (a • u) (a • u) *
      g₀.metric.inner x (b • v) (b • v) -
        (g₀.metric.inner x (a • u) (b • v)) ^ 2 =
      (a ^ 2 * b ^ 2) *
        (g₀.metric.inner x u u * g₀.metric.inner x v v - (g₀.metric.inner x u v) ^ 2) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  unfold LeviCivitaData.sectionalCurvature
  rw [hnum, hden]
  exact mul_div_mul_left _ _ (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb))

private theorem warp_axis_orthonormal (g₀ : StandardInitialMetric) (r : ℝ) :
    LeviCivitaData.IsOrthonormalPair g₀.metric (axisPoint r)
      ((radialSpeed g₀ r)⁻¹ • axisBasis 0)
      ((Real.sqrt (axisTangentialCoefficient g₀ r))⁻¹ • axisBasis 1) := by
  have ha : (radialSpeed g₀ r) ^ 2 = axisRadialCoefficient g₀ r :=
    Real.sq_sqrt (axisRadialCoefficient_pos g₀ r).le
  have hc := Real.sq_sqrt (axisTangentialCoefficient_pos g₀ r).le
  have ha0 := (radialSpeed_pos g₀ r).ne'
  have hc0 := (Real.sqrt_pos.mpr (axisTangentialCoefficient_pos g₀ r)).ne'
  unfold LeviCivitaData.IsOrthonormalPair
  simp only [map_smul, smul_apply, smul_eq_mul, axis_metric_zero_one, mul_zero]
  change (radialSpeed g₀ r)⁻¹ * ((radialSpeed g₀ r)⁻¹ * axisRadialCoefficient g₀ r) = 1 ∧
    (Real.sqrt (axisTangentialCoefficient g₀ r))⁻¹ *
      ((Real.sqrt (axisTangentialCoefficient g₀ r))⁻¹ * axisTangentialCoefficient g₀ r) = 1 ∧
        True
  constructor
  · rw [← ha]
    field_simp
  constructor
  · generalize hs : Real.sqrt (axisTangentialCoefficient g₀ r) = s at *
    rw [← hc]
    field_simp
  · trivial

private theorem warp_tip_radial_sectional (g₀ : StandardInitialMetric) :
    ∃ e : ℝ, 0 < e ∧ ∀ r ∈ Ioo 0 e,
      g₀.connection.sectionalCurvature (axisPoint r) (axisBasis 0) (axisBasis 1) =
        (1 / 4 : ℝ) := by
  obtain ⟨R, hR, htip⟩ := g₀.tip_sectional_curvature
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), radialArclength g₀ r < R :=
    (radialArclength_contDiff g₀).continuous.continuousAt.eventually
      (gt_mem_nhds (by simpa only [radialArclength_zero] using hR))
  obtain ⟨e, he, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨e, he, ?_⟩
  intro r hr
  have hdist := axis_edist_le_arclength_sub g₀ hr.1.le
  have hzero : axisPoint 0 = 0 := by simp [axisPoint_eq_smul]
  have hin : axisPoint r ∈ g₀.metric.ball 0 R := by
    change g₀.metric.edist 0 (axisPoint r) < ENNReal.ofReal R
    rw [hzero, radialArclength_zero, sub_zero] at hdist
    apply hdist.trans_lt
    exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr
      (hsmall (by simpa [Real.dist_eq, abs_of_pos hr.1] using hr.2))
  have hk := htip (axisPoint r) hin _ _ (warp_axis_orthonormal g₀ r)
  rw [warp_sectional_smul g₀ _ _ _ (inv_ne_zero (radialSpeed_pos g₀ r).ne')
    (inv_ne_zero (Real.sqrt_pos.mpr (axisTangentialCoefficient_pos g₀ r)).ne')] at hk
  exact hk



theorem angularRadiusSlope_lt_one (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    angularRadiusSlope g₀ r < 1 := by
  obtain ⟨e, he, htip⟩ := warp_tip_radial_sectional g₀
  have hneg (t : ℝ) (ht : t ∈ Ioo 0 e) : deriv (angularRadiusSlope g₀) t < 0 := by
    have hk := htip t ht
    rw [standardCap_sectional_radial_slope g₀ ht.1] at hk
    have hden := mul_pos (radialSpeed_pos g₀ t) (euclideanWarpRadius_pos g₀ ht.1)
    have hn : 0 < -deriv (angularRadiusSlope g₀) t :=
      (div_pos_iff_of_pos_right hden).mp (by rw [hk]; norm_num)
    linarith only [hn]
  have hstrict : StrictAntiOn (angularRadiusSlope g₀) (Ioo 0 e) :=
    strictAntiOn_of_deriv_neg (convex_Ioo 0 e)
      (angularRadiusSlope_contDiff g₀).continuous.continuousOn
      (fun t ht => hneg t (by simpa only [interior_Ioo] using ht))
  let t := min r e / 2
  let s := t / 2
  have ht0 : 0 < t := by dsimp only [t]; positivity
  have htr : t < r := by dsimp only [t]; nlinarith only [min_le_left r e, hr]
  have hte : t < e := by dsimp only [t]; nlinarith only [min_le_right r e, he]
  have hs0 : 0 < s := half_pos ht0
  have hst : s < t := by dsimp only [s]; linarith only [ht0]
  have hqs : angularRadiusSlope g₀ s ≤ 1 := by
    have hsq := angularRadiusSlope_sq_le_one g₀ hs0
    nlinarith only [hsq, sq_nonneg (angularRadiusSlope g₀ s - 1)]
  exact (angularRadiusSlope_antitoneOn g₀ ht0 hr htr.le).trans_lt
    ((hstrict ⟨hs0, hst.trans hte⟩ ⟨ht0, hte⟩ hst).trans_le hqs)



theorem standardCap_sectional_tangential_pos (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) :
    0 < g₀.connection.sectionalCurvature (axisPoint r) (axisBasis 1) (axisBasis 2) := by
  have hq0 := angularRadiusSlope_nonneg g₀ hr
  have hq1 := angularRadiusSlope_lt_one g₀ hr
  have hq : (angularRadiusSlope g₀ r) ^ 2 < 1 := by nlinarith only [hq0, hq1]
  rw [angularRadiusSlope_eq, div_pow] at hq
  have he : (2 * radialSpeed g₀ r * Real.sqrt (axisTangentialCoefficient g₀ r)) ^ 2 =
      4 * axisRadialCoefficient g₀ r * axisTangentialCoefficient g₀ r := by
    rw [mul_pow, mul_pow, show (radialSpeed g₀ r) ^ 2 = axisRadialCoefficient g₀ r from
      Real.sq_sqrt (axisRadialCoefficient_pos g₀ r).le,
      Real.sq_sqrt (axisTangentialCoefficient_pos g₀ r).le]
    norm_num
  rw [he] at hq
  have ha := axisRadialCoefficient_pos g₀ r
  have hc := axisTangentialCoefficient_pos g₀ r
  have hden : 0 < 4 * axisRadialCoefficient g₀ r * axisTangentialCoefficient g₀ r := by
    positivity
  have hnum := (div_lt_one hden).mp hq
  rw [standardCap_sectional_tangential g₀ hr]
  exact div_pos (sub_pos.mpr hnum) (by positivity)


end PoincareConjecture.M36
