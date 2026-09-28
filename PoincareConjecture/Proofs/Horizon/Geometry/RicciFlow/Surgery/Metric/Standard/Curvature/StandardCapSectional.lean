import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.ConformalSectional
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Standard.Radial.RadialMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Standard.Radial.RadialArclength
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle
open Filter Set Topology

namespace PoincareConjecture.MetricSurgery

private theorem cap_fderiv_inner (x v w : StandardCapSpace) :
    fderiv ℝ (fun y : StandardCapSpace => inner ℝ y w) x v = inner ℝ v w := by
  change fderiv ℝ ((innerSL ℝ).flip w) x v = _
  rw [ContinuousLinearMap.fderiv]
  rfl

private theorem cap_fderiv_norm {x : StandardCapSpace} (hx : x ≠ 0)
    (v : StandardCapSpace) :
    fderiv ℝ (fun y : StandardCapSpace => ‖y‖) x v = inner ℝ x v / ‖x‖ := by
  have hn := (differentiableAt_id (𝕜 := ℝ) (x := x)).norm ℝ hx
  have hs := congrArg (fun L : StandardCapSpace →L[ℝ] ℝ => L v)
    (hn.hasFDerivAt.pow 2).fderiv
  simp only [id_eq] at hs
  rw [fderiv_norm_sq_apply] at hs
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
    Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat] at hs
  apply (eq_div_iff (norm_ne_zero_iff.mpr hx)).mpr
  nlinarith only [hs]

private theorem cap_fderiv_radial {f : ℝ → ℝ} {x : StandardCapSpace}
    (hf : DifferentiableAt ℝ f ‖x‖) (hx : x ≠ 0) (v : StandardCapSpace) :
    fderiv ℝ (fun y : StandardCapSpace => f ‖y‖) x v =
      deriv f ‖x‖ * (inner ℝ x v / ‖x‖) := by
  change fderiv ℝ (f ∘ fun y : StandardCapSpace => ‖y‖) x v = _
  rw [fderiv_comp x hf ((differentiableAt_id (𝕜 := ℝ) (x := x)).norm ℝ hx)]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul]
  rw [cap_fderiv_norm hx]

private noncomputable def capRadialExcess (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  (axisRadialCoefficient g₀ r - axisTangentialCoefficient g₀ r) / r ^ 2

private theorem capRadialExcess_contDiffAt (g₀ : StandardInitialMetric) {r : ℝ}
    (hr : r ≠ 0) : ContDiffAt ℝ ∞ (capRadialExcess g₀) r :=
  ((axisRadialCoefficient_contDiff g₀).contDiffAt.sub
    (axisTangentialCoefficient_contDiff g₀).contDiffAt).div
      (contDiffAt_id.pow 2) (pow_ne_zero 2 hr)

private theorem cap_metric_cartesian (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace) :
    g₀.metric.inner x v w = axisTangentialCoefficient g₀ ‖x‖ * inner ℝ v w +
      capRadialExcess g₀ ‖x‖ * inner ℝ x v * inner ℝ x w := by
  rw [standard_metric_radial_formula g₀ x hx]
  simp only [real_inner_smul_left]
  dsimp only [capRadialExcess]
  ring

private theorem cap_metric_radial (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v : StandardCapSpace) :
    g₀.metric.inner x x v = axisRadialCoefficient g₀ ‖x‖ * inner ℝ x v := by
  rw [cap_metric_cartesian g₀ hx, real_inner_self_eq_norm_sq]
  dsimp only [capRadialExcess]
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

theorem standard_metric_fderiv_inner (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w z : StandardCapSpace) :
    fderiv ℝ (fun y : StandardCapSpace => g₀.metric.inner y v w) x z =
      deriv (axisTangentialCoefficient g₀) ‖x‖ * (inner ℝ x z / ‖x‖) *
          inner ℝ v w +
        deriv (capRadialExcess g₀) ‖x‖ * (inner ℝ x z / ‖x‖) *
          inner ℝ x v * inner ℝ x w +
        capRadialExcess g₀ ‖x‖ *
          (inner ℝ z v * inner ℝ x w + inner ℝ x v * inner ℝ z w) := by
  have hn := (differentiableAt_id (𝕜 := ℝ) (x := x)).norm ℝ hx
  have hc := (axisTangentialCoefficient_contDiff g₀).differentiable (by simp) ‖x‖
  have hb := (capRadialExcess_contDiffAt g₀ (norm_ne_zero_iff.mpr hx)).differentiableAt
    (by simp)
  have hv : DifferentiableAt ℝ (fun y : StandardCapSpace => inner ℝ y v) x :=
    differentiableAt_id.inner ℝ (differentiableAt_const v)
  have hw : DifferentiableAt ℝ (fun y : StandardCapSpace => inner ℝ y w) x :=
    differentiableAt_id.inner ℝ (differentiableAt_const w)
  have he : (fun y : StandardCapSpace => g₀.metric.inner y v w) =ᶠ[𝓝 x]
      (fun y => axisTangentialCoefficient g₀ ‖y‖ * inner ℝ v w +
        capRadialExcess g₀ ‖y‖ * inner ℝ y v * inner ℝ y w) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact cap_metric_cartesian g₀ hy v w
  rw [he.fderiv_eq]
  erw [fderiv_fun_add ((hc.comp x hn).mul_const _) (((hb.comp x hn).mul hv).mul hw),
    fderiv_fun_mul ((hb.comp x hn).mul hv) hw,
    fderiv_fun_mul (hb.comp x hn) hv, fderiv_mul_const (hc.comp x hn) _]
  simp only [Function.comp_def, Pi.mul_def]
  simp only [add_apply, smul_apply,
    smul_eq_mul, cap_fderiv_radial hc hx, cap_fderiv_radial hb hx,
    cap_fderiv_inner]
  ring

private noncomputable def capConnectionA (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  deriv (axisTangentialCoefficient g₀) r / (2 * axisTangentialCoefficient g₀ r * r)

private noncomputable def capConnectionB (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  (2 * capRadialExcess g₀ r - deriv (axisTangentialCoefficient g₀) r / r) /
    (2 * axisRadialCoefficient g₀ r)

private noncomputable def capConnectionC (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  (deriv (capRadialExcess g₀) r / r -
    4 * capConnectionA g₀ r * capRadialExcess g₀ r) / (2 * axisRadialCoefficient g₀ r)

private noncomputable def capConnectionTerm (g₀ : StandardInitialMetric)
    (x v w : StandardCapSpace) : StandardCapSpace :=
  capConnectionA g₀ ‖x‖ • (inner ℝ x v • w + inner ℝ x w • v) +
    (capConnectionB g₀ ‖x‖ * inner ℝ v w +
      capConnectionC g₀ ‖x‖ * inner ℝ x v * inner ℝ x w) • x

private theorem cap_constant_field_smooth (v : StandardCapSpace) :
    ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
      (fun x : StandardCapSpace => (⟨x, v⟩ : TangentBundle (𝓡 3) StandardCapSpace)) :=
  contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const

private theorem cap_constant_bracket (v w : StandardCapSpace) :
    VectorField.mlieBracket (𝓡 3) (fun _ : StandardCapSpace => v)
      (fun _ : StandardCapSpace => w) = 0 := by
  unfold VectorField.mlieBracket
  erw [VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin_univ]
  simp [VectorField.lieBracket]
  rfl

private theorem cap_connection_constant (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace) :
    g₀.connection.connection (fun _ : StandardCapSpace => w) x v =
      capConnectionTerm g₀ x v w := by
  have hp (z : StandardCapSpace) :
      g₀.metric.inner x (g₀.connection.connection (fun _ => w) x v) z =
        g₀.metric.inner x (capConnectionTerm g₀ x v w) z := by
    have hk := g₀.connection.normalization_koszul (fun _ : StandardCapSpace => v)
      (fun _ : StandardCapSpace => w) (fun _ : StandardCapSpace => z)
      ((cap_constant_field_smooth v x).mdifferentiableAt (by simp))
      ((cap_constant_field_smooth w x).mdifferentiableAt (by simp))
      ((cap_constant_field_smooth z x).mdifferentiableAt (by simp))
    simp only [cap_constant_bracket, Pi.zero_apply, map_zero,
      zero_apply, add_zero, sub_zero, mvfderiv, mfderiv_eq_fderiv,
      ContinuousLinearMap.comp_apply, NormedSpace.fromTangentSpace] at hk
    change 2 * g₀.metric.inner x (g₀.connection.connection (fun _ => w) x v) z =
      fderiv ℝ (fun y => g₀.metric.inner y w z) x v +
        fderiv ℝ (fun y => g₀.metric.inner y z v) x w -
        fderiv ℝ (fun y => g₀.metric.inner y v w) x z at hk
    rw [standard_metric_fderiv_inner g₀ hx, standard_metric_fderiv_inner g₀ hx,
      standard_metric_fderiv_inner g₀ hx] at hk
    have hterm : 2 * g₀.metric.inner x (capConnectionTerm g₀ x v w) z =
        deriv (axisTangentialCoefficient g₀) ‖x‖ / ‖x‖ *
          (inner ℝ x v * inner ℝ w z + inner ℝ x w * inner ℝ v z -
            inner ℝ x z * inner ℝ v w) +
          deriv (capRadialExcess g₀) ‖x‖ / ‖x‖ *
            inner ℝ x v * inner ℝ x w * inner ℝ x z +
          2 * capRadialExcess g₀ ‖x‖ * inner ℝ v w * inner ℝ x z := by
      let G : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := g₀.metric.inner x
      have hGw : G w z = axisTangentialCoefficient g₀ ‖x‖ * inner ℝ w z +
          capRadialExcess g₀ ‖x‖ * inner ℝ x w * inner ℝ x z :=
        cap_metric_cartesian g₀ hx w z
      have hGv : G v z = axisTangentialCoefficient g₀ ‖x‖ * inner ℝ v z +
          capRadialExcess g₀ ‖x‖ * inner ℝ x v * inner ℝ x z :=
        cap_metric_cartesian g₀ hx v z
      have hGx : G x z = axisRadialCoefficient g₀ ‖x‖ * inner ℝ x z :=
        cap_metric_radial g₀ hx z
      change 2 * G (capConnectionTerm g₀ x v w) z = _
      simp only [capConnectionTerm, map_add, map_smul, add_apply, smul_apply,
        smul_eq_mul]
      rw [hGw, hGv, hGx]
      dsimp only [capConnectionA, capConnectionB, capConnectionC]
      field_simp [(axisRadialCoefficient_pos g₀ ‖x‖).ne',
        (axisTangentialCoefficient_pos g₀ ‖x‖).ne', norm_ne_zero_iff.mpr hx]
      ring
    simp only [real_inner_comm] at hk hterm
    ring_nf at hk hterm
    linarith only [hk, hterm]
  let q : StandardCapSpace := g₀.connection.connection (fun _ => w) x v
  change q = capConnectionTerm g₀ x v w
  by_contra hne
  have hpos := g₀.metric.pos x _ (sub_ne_zero.mpr hne)
  have hz := hp (q - capConnectionTerm g₀ x v w)
  let G : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := g₀.metric.inner x
  change G q (q - capConnectionTerm g₀ x v w) =
    G (capConnectionTerm g₀ x v w) (q - capConnectionTerm g₀ x v w) at hz
  have hzero : g₀.metric.inner x
      (q - capConnectionTerm g₀ x v w) (q - capConnectionTerm g₀ x v w) = 0 := by
    change G (q - capConnectionTerm g₀ x v w) (q - capConnectionTerm g₀ x v w) = 0
    rw [map_sub G, sub_apply, hz, sub_self]
  exact hpos.ne' hzero

private theorem cap_connection_pairing (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w z : StandardCapSpace) :
    g₀.metric.inner x (g₀.connection.connection (fun _ => w) x v) z =
      deriv (axisTangentialCoefficient g₀) ‖x‖ / (2 * ‖x‖) *
        (inner ℝ x v * inner ℝ w z + inner ℝ x w * inner ℝ v z) +
      (capRadialExcess g₀ ‖x‖ - deriv (axisTangentialCoefficient g₀) ‖x‖ / (2 * ‖x‖)) *
        inner ℝ v w * inner ℝ x z +
      deriv (capRadialExcess g₀) ‖x‖ / (2 * ‖x‖) *
        inner ℝ x v * inner ℝ x w * inner ℝ x z := by
  rw [cap_connection_constant g₀ hx]
  let G : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := g₀.metric.inner x
  have hGw : G w z = axisTangentialCoefficient g₀ ‖x‖ * inner ℝ w z +
      capRadialExcess g₀ ‖x‖ * inner ℝ x w * inner ℝ x z :=
    cap_metric_cartesian g₀ hx w z
  have hGv : G v z = axisTangentialCoefficient g₀ ‖x‖ * inner ℝ v z +
      capRadialExcess g₀ ‖x‖ * inner ℝ x v * inner ℝ x z :=
    cap_metric_cartesian g₀ hx v z
  have hGx : G x z = axisRadialCoefficient g₀ ‖x‖ * inner ℝ x z :=
    cap_metric_radial g₀ hx z
  change G (capConnectionTerm g₀ x v w) z = _
  simp only [capConnectionTerm, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [hGw, hGv, hGx]
  dsimp only [capConnectionA, capConnectionB, capConnectionC]
  field_simp [(axisRadialCoefficient_pos g₀ ‖x‖).ne',
    (axisTangentialCoefficient_pos g₀ ‖x‖).ne', norm_ne_zero_iff.mpr hx]
  ring

private theorem cap_fderiv_radial_linear {f : ℝ → ℝ} {x : StandardCapSpace}
    (hf : DifferentiableAt ℝ f ‖x‖) (hx : x ≠ 0) (v z : StandardCapSpace)
    (hxv : inner ℝ x v = 0) :
    fderiv ℝ (fun y : StandardCapSpace => f ‖y‖ * inner ℝ y v) x z =
      f ‖x‖ * inner ℝ z v := by
  erw [fderiv_fun_mul (hf.comp x ((differentiableAt_id (𝕜 := ℝ)).norm ℝ hx))
    (differentiableAt_id.inner ℝ (differentiableAt_const v))]
  simp only [Function.comp_def, id_eq]
  simp only [add_apply, smul_apply,
    smul_eq_mul, hxv, zero_mul, add_zero, cap_fderiv_inner]

private theorem cap_fderiv_radial_cubic {f : ℝ → ℝ} {x : StandardCapSpace}
    (hf : DifferentiableAt ℝ f ‖x‖) (hx : x ≠ 0) (v w z : StandardCapSpace)
    (hxv : inner ℝ x v = 0) (hxw : inner ℝ x w = 0) :
    fderiv ℝ (fun y : StandardCapSpace =>
      f ‖y‖ * (inner ℝ y w) ^ 2 * inner ℝ y v) x z = 0 := by
  have hv : DifferentiableAt ℝ (fun y : StandardCapSpace => inner ℝ y v) x :=
    differentiableAt_id.inner ℝ (differentiableAt_const v)
  have hw : DifferentiableAt ℝ (fun y : StandardCapSpace => inner ℝ y w) x :=
    differentiableAt_id.inner ℝ (differentiableAt_const w)
  erw [fderiv_fun_mul
    ((hf.comp x ((differentiableAt_id (𝕜 := ℝ)).norm ℝ hx)).mul (hw.pow 2)) hv]
  simp only [Function.comp_def, Pi.mul_def, Pi.pow_def]
  simp only [add_apply, smul_apply,
    smul_eq_mul, hxv, hxw, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, add_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem cap_tangential_curvature_numerator (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace)
    (hvv : inner ℝ v v = 1) (hww : inner ℝ w w = 1) (hvw : inner ℝ v w = 0)
    (hxv : inner ℝ x v = 0) (hxw : inner ℝ x w = 0) :
    g₀.metric.inner x (g₀.connection.curvature x v w w) v =
      capRadialExcess g₀ ‖x‖ - deriv (axisTangentialCoefficient g₀) ‖x‖ / ‖x‖ -
        axisRadialCoefficient g₀ ‖x‖ * (capConnectionB g₀ ‖x‖) ^ 2 * ‖x‖ ^ 2 := by
  let d : ℝ → ℝ := fun r => deriv (axisTangentialCoefficient g₀) r / (2 * r)
  let e : ℝ → ℝ := fun r => deriv (capRadialExcess g₀) r / (2 * r)
  let X := fun _ : StandardCapSpace => v
  let Y := fun _ : StandardCapSpace => w
  let W := fun y => g₀.connection.connection Y y w
  let V := fun y => g₀.connection.connection Y y v
  have hX := cap_constant_field_smooth v
  have hY := cap_constant_field_smooth w
  have hW := g₀.connection.normalization_contMDiffOn_connection_apply isOpen_univ Y Y
    hY.contMDiffOn hY.contMDiffOn
  have hV := g₀.connection.normalization_contMDiffOn_connection_apply isOpen_univ X Y
    hX.contMDiffOn hY.contMDiffOn
  have hWd := (hW.contMDiffAt (x := x) (by simp)).mdifferentiableAt (by simp)
  have hVd := (hV.contMDiffAt (x := x) (by simp)).mdifferentiableAt (by simp)
  have hwv : inner ℝ w v = 0 := by rw [real_inner_comm, hvw]
  have hn0 := norm_ne_zero_iff.mpr hx
  have hb := capRadialExcess_contDiffAt g₀ hn0
  have hc' : ContDiff ℝ ∞ (deriv (axisTangentialCoefficient g₀)) :=
    (contDiff_infty_iff_deriv.mp (axisTangentialCoefficient_contDiff g₀)).2
  have hd : DifferentiableAt ℝ d ‖x‖ :=
    (hc'.contDiffAt.div (contDiffAt_const.mul contDiffAt_id)
      (mul_ne_zero (by norm_num) hn0)).differentiableAt (by simp)
  have he : DifferentiableAt ℝ e ‖x‖ :=
    ((hb.derivWithin (m := ∞) (by simp)).div (contDiffAt_const.mul contDiffAt_id)
      (mul_ne_zero (by norm_num) hn0)).differentiableAt (by simp)
  have hbd : DifferentiableAt ℝ (fun r => capRadialExcess g₀ r - d r) ‖x‖ :=
    (hb.differentiableAt (by simp)).sub hd
  have hS : (fun y => g₀.metric.inner y (W y) v) =ᶠ[𝓝 x]
      (fun y => (capRadialExcess g₀ ‖y‖ - d ‖y‖) * inner ℝ y v +
        e ‖y‖ * (inner ℝ y w) ^ 2 * inner ℝ y v) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [show W y = g₀.connection.connection (fun _ => w) y w from rfl,
      cap_connection_pairing g₀ hy]
    simp only [hwv, hww, mul_zero, add_zero, mul_one, zero_add]
    dsimp only [d, e]
    ring
  have hT : (fun y => g₀.metric.inner y (V y) v) =ᶠ[𝓝 x]
      (fun y => d ‖y‖ * inner ℝ y w + e ‖y‖ * (inner ℝ y v) ^ 2 * inner ℝ y w) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [show V y = g₀.connection.connection (fun _ => w) y v from rfl,
      cap_connection_pairing g₀ hy]
    simp only [hwv, hvw, hvv, mul_zero, mul_one, zero_add]
    dsimp only [d, e]
    ring
  have hSd : fderiv ℝ (fun y => g₀.metric.inner y (W y) v) x v =
      capRadialExcess g₀ ‖x‖ - d ‖x‖ := by
    rw [hS.fderiv_eq]
    have hn := (differentiableAt_id (𝕜 := ℝ) (x := x)).norm ℝ hx
    have hl (z : StandardCapSpace) :
        DifferentiableAt ℝ (fun y : StandardCapSpace => inner ℝ y z) x :=
      differentiableAt_id.inner ℝ (differentiableAt_const z)
    erw [fderiv_fun_add ((hbd.comp x hn).mul (hl v))
      (((he.comp x hn).mul ((hl w).pow 2)).mul (hl v))]
    simp only [Function.comp_def, Pi.mul_def, Pi.pow_def]
    simp only [add_apply, cap_fderiv_radial_linear hbd hx v v hxv,
      cap_fderiv_radial_cubic he hx v w v hxv hxw, hvv, mul_one, add_zero]
  have hTd : fderiv ℝ (fun y => g₀.metric.inner y (V y) v) x w = d ‖x‖ := by
    rw [hT.fderiv_eq]
    have hn := (differentiableAt_id (𝕜 := ℝ) (x := x)).norm ℝ hx
    have hl (z : StandardCapSpace) :
        DifferentiableAt ℝ (fun y : StandardCapSpace => inner ℝ y z) x :=
      differentiableAt_id.inner ℝ (differentiableAt_const z)
    erw [fderiv_fun_add ((hd.comp x hn).mul (hl w))
      (((he.comp x hn).mul ((hl v).pow 2)).mul (hl w))]
    simp only [Function.comp_def, Pi.mul_def, Pi.pow_def]
    simp only [add_apply, cap_fderiv_radial_linear hd hx w w hxw,
      cap_fderiv_radial_cubic he hx w v w hxw hxv, hww, mul_one, add_zero]
  have hXX : g₀.connection.connection X x v = capConnectionB g₀ ‖x‖ • x := by
    rw [cap_connection_constant g₀ hx]
    simp only [capConnectionTerm, hxv, hvv, zero_smul, add_zero, smul_zero,
      mul_one, mul_zero, zero_add]
  have hYY : W x = capConnectionB g₀ ‖x‖ • x := by
    rw [show W x = g₀.connection.connection (fun _ => w) x w from rfl,
      cap_connection_constant g₀ hx]
    simp only [capConnectionTerm, hxw, hww, zero_smul, add_zero, smul_zero,
      mul_one, mul_zero, zero_add]
  have hXY : V x = 0 := by
    rw [show V x = g₀.connection.connection (fun _ => w) x v from rfl,
      cap_connection_constant g₀ hx]
    simp [capConnectionTerm, hxv, hxw, hvw]
  have hDW := g₀.connection.normalization_mvfderiv_inner X W X hWd
    ((hX x).mdifferentiableAt (by simp))
  have hDV := g₀.connection.normalization_mvfderiv_inner Y V X hVd
    ((hX x).mdifferentiableAt (by simp))
  simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
    NormedSpace.fromTangentSpace] at hDW hDV
  change fderiv ℝ (fun y => g₀.metric.inner y (W y) v) x v =
    g₀.metric.inner x (g₀.connection.connection W x v) v +
      g₀.metric.inner x (W x) (g₀.connection.connection X x v) at hDW
  change fderiv ℝ (fun y => g₀.metric.inner y (V y) v) x w =
    g₀.metric.inner x (g₀.connection.connection V x w) v +
      g₀.metric.inner x (V x) (g₀.connection.connection X x w) at hDV
  rw [hSd, hYY, hXX] at hDW
  simp only [map_smul, smul_apply, smul_eq_mul] at hDW
  rw [cap_metric_radial g₀ hx, real_inner_self_eq_norm_sq] at hDW
  rw [hTd, hXY, map_zero, zero_apply, add_zero] at hDV
  rw [← RicciFlowAnalysis.curvatureOnFields_eq_curvature g₀.connection isOpen_univ
    hX.contMDiffOn hY.contMDiffOn hY.contMDiffOn (mem_univ x)]
  change g₀.metric.inner x (g₀.connection.connection W x v -
    g₀.connection.connection V x w -
    g₀.connection.connection Y x (VectorField.mlieBracket (𝓡 3) X Y x)) v = _
  rw [show VectorField.mlieBracket (𝓡 3) X Y x = 0 by
    exact congrFun (cap_constant_bracket v w) x, map_zero, sub_zero]
  simp only [map_sub, sub_apply]
  dsimp only [d] at hDW hDV
  ring_nf at hDW hDV ⊢
  linarith only [hDW, hDV]

theorem standardCap_sectional_tangential (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) :
    g₀.connection.sectionalCurvature (axisPoint r) (axisBasis 1) (axisBasis 2) =
      (4 * axisRadialCoefficient g₀ r * axisTangentialCoefficient g₀ r -
        (2 * axisTangentialCoefficient g₀ r +
          r * deriv (axisTangentialCoefficient g₀) r) ^ 2) /
      (4 * axisRadialCoefficient g₀ r * r ^ 2 * (axisTangentialCoefficient g₀ r) ^ 2) := by
  have hnorm : ‖axisPoint r‖ = r := by
    rw [axisPoint_eq_smul]
    simp [axisBasis, norm_smul, abs_of_pos hr]
  have hx : axisPoint r ≠ 0 := norm_ne_zero_iff.mp (hnorm.trans_ne hr.ne')
  have hi (i j : Fin 3) : inner ℝ (axisBasis i) (axisBasis j) = if i = j then 1 else 0 := by
    simp [axisBasis, EuclideanSpace.inner_single_left]
  have hx1 : inner ℝ (axisPoint r) (axisBasis 1) = 0 := by
    rw [axisPoint_eq_smul, real_inner_smul_left, hi, if_neg (by decide), mul_zero]
  have hx2 : inner ℝ (axisPoint r) (axisBasis 2) = 0 := by
    rw [axisPoint_eq_smul, real_inner_smul_left, hi, if_neg (by decide), mul_zero]
  have hR := cap_tangential_curvature_numerator g₀ hx (axisBasis 1) (axisBasis 2)
    (by rw [hi, if_pos rfl]) (by rw [hi, if_pos rfl])
    (by rw [hi, if_neg (by decide)]) hx1 hx2
  unfold LeviCivitaData.sectionalCurvature LeviCivitaData.curvatureTensor
  rw [hR]
  rw [← axis_metric_tangential_eq, axis_metric_one_two]
  change (capRadialExcess g₀ ‖axisPoint r‖ -
      deriv (axisTangentialCoefficient g₀) ‖axisPoint r‖ / ‖axisPoint r‖ -
      axisRadialCoefficient g₀ ‖axisPoint r‖ * (capConnectionB g₀ ‖axisPoint r‖) ^ 2 *
        ‖axisPoint r‖ ^ 2) /
    (axisTangentialCoefficient g₀ r * axisTangentialCoefficient g₀ r - 0 ^ 2) = _
  rw [hnorm]
  dsimp only [capConnectionB, capRadialExcess]
  field_simp [hr.ne', (axisRadialCoefficient_pos g₀ r).ne',
    (axisTangentialCoefficient_pos g₀ r).ne']
  ring

theorem standardCap_angular_derivative_sq_le (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) :
    (2 * axisTangentialCoefficient g₀ r +
      r * deriv (axisTangentialCoefficient g₀) r) ^ 2 ≤
        4 * axisRadialCoefficient g₀ r * axisTangentialCoefficient g₀ r := by
  have hK : 0 ≤ g₀.connection.sectionalCurvature (axisPoint r)
      (axisBasis 1) (axisBasis 2) := by
    unfold LeviCivitaData.sectionalCurvature
    apply div_nonneg (g₀.nonnegative_sectional _ _ _)
    rw [← axis_metric_tangential_eq, axis_metric_one_two]
    change 0 ≤ axisTangentialCoefficient g₀ r * axisTangentialCoefficient g₀ r - 0 ^ 2
    simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero] using
      mul_self_nonneg (axisTangentialCoefficient g₀ r)
  rw [standardCap_sectional_tangential g₀ hr] at hK
  have hden : 0 < 4 * axisRadialCoefficient g₀ r * r ^ 2 *
      (axisTangentialCoefficient g₀ r) ^ 2 := by
    have ha := axisRadialCoefficient_pos g₀ r
    have hc := axisTangentialCoefficient_pos g₀ r
    positivity
  exact sub_nonneg.mp (by simpa only [zero_mul] using (le_div_iff₀ hden).mp hK)

private theorem cap_mvfderiv_eq_fderiv (f : StandardCapSpace → ℝ)
    (x v : StandardCapSpace) : mvfderiv (𝓡 3) f x v = fderiv ℝ f x v := by
  simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
    NormedSpace.fromTangentSpace]
  rfl

theorem standardCap_radialArclength_mvfderiv (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v : StandardCapSpace) :
    mvfderiv (𝓡 3) (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x v =
      radialSpeed g₀ ‖x‖ / ‖x‖ * inner ℝ x v := by
  rw [cap_mvfderiv_eq_fderiv,
    cap_fderiv_radial (radialArclength_hasDerivAt g₀ ‖x‖).differentiableAt hx,
    radialArclength_deriv]
  ring

private theorem cap_radialSpeed_deriv (g₀ : StandardInitialMetric) (r : ℝ) :
    deriv (radialSpeed g₀) r =
      deriv (axisRadialCoefficient g₀) r / (2 * radialSpeed g₀ r) := by
  exact (((axisRadialCoefficient_contDiff g₀).differentiable (by simp) r).hasDerivAt.sqrt
    (axisRadialCoefficient_pos g₀ r).ne').deriv

private theorem capRadialExcess_deriv (g₀ : StandardInitialMetric) {r : ℝ}
    (hr : r ≠ 0) :
    deriv (capRadialExcess g₀) r =
      ((deriv (axisRadialCoefficient g₀) r - deriv (axisTangentialCoefficient g₀) r) *
        r ^ 2 - (axisRadialCoefficient g₀ r - axisTangentialCoefficient g₀ r) *
          (2 * r)) / (r ^ 2) ^ 2 := by
  have ha := ((axisRadialCoefficient_contDiff g₀).differentiable (by simp) r).hasDerivAt
  have hc := ((axisTangentialCoefficient_contDiff g₀).differentiable (by simp) r).hasDerivAt
  change deriv (fun t => (axisRadialCoefficient g₀ t -
    axisTangentialCoefficient g₀ t) / t ^ 2) r = _
  simpa only [Pi.div_def, Pi.sub_def, Pi.pow_def, id_eq,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using
    ((ha.sub hc).div ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr)).deriv

private theorem cap_hessian_constant (g₀ : StandardInitialMetric)
    {f : StandardCapSpace → ℝ} {x : StandardCapSpace}
    (hf : ContDiffAt ℝ ∞ f x) (v w : StandardCapSpace) :
    g₀.connection.hessian f x v w =
      fderiv ℝ (fun y => fderiv ℝ f y w) x v -
        fderiv ℝ f x (g₀.connection.connection (fun _ => w) x v) := by
  have hm := hf.contMDiffAt
  have hY := (cap_constant_field_smooth w x).mdifferentiableAt (by simp)
  calc
    g₀.connection.hessian f x v w =
        g₀.connection.hessianOnFields f (fun _ => v) (fun _ => w) x := by
      rw [g₀.connection.hessian_eq_inner_connection_gradient hm,
        g₀.connection.hessianOnFields_eq_inner_connection_gradient hm _ hY]
    _ = _ := by
      unfold LeviCivitaData.hessianOnFields
      simp only [cap_mvfderiv_eq_fderiv]

private theorem cap_fderiv_radial_pairing {f : ℝ → ℝ} {x : StandardCapSpace}
    (hf : DifferentiableAt ℝ f ‖x‖) (hx : x ≠ 0) (v w : StandardCapSpace) :
    fderiv ℝ (fun y : StandardCapSpace => f ‖y‖ * inner ℝ y w) x v =
      f ‖x‖ * inner ℝ v w +
        deriv f ‖x‖ / ‖x‖ * inner ℝ x v * inner ℝ x w := by
  erw [fderiv_fun_mul (hf.comp x ((differentiableAt_id (𝕜 := ℝ)).norm ℝ hx))
    (differentiableAt_id.inner ℝ (differentiableAt_const w))]
  simp only [Function.comp_def, id_eq]
  simp only [add_apply, smul_apply, smul_eq_mul, cap_fderiv_radial hf hx,
    cap_fderiv_inner]
  ring

theorem standardCap_radialArclength_hessian (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace) :
    g₀.connection.hessian (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x v w =
      (2 * axisTangentialCoefficient g₀ ‖x‖ +
        ‖x‖ * deriv (axisTangentialCoefficient g₀) ‖x‖) /
          (2 * ‖x‖ * axisTangentialCoefficient g₀ ‖x‖ * radialSpeed g₀ ‖x‖) *
        (g₀.metric.inner x v w -
          mvfderiv (𝓡 3) (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x v *
          mvfderiv (𝓡 3) (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x w) := by
  let q : ℝ → ℝ := fun r => radialSpeed g₀ r / r
  have hn := norm_ne_zero_iff.mpr hx
  have hq : DifferentiableAt ℝ q ‖x‖ :=
    ((radialSpeed_contDiff g₀).differentiable (by simp) ‖x‖).div differentiableAt_id hn
  have hqd : deriv q ‖x‖ =
      (deriv (radialSpeed g₀) ‖x‖ * ‖x‖ - radialSpeed g₀ ‖x‖) / ‖x‖ ^ 2 := by
    simpa only [q, Pi.div_def, id_eq, mul_one] using
      ((((radialSpeed_contDiff g₀).differentiable (by simp) ‖x‖).hasDerivAt).div
        (hasDerivAt_id ‖x‖) hn).deriv
  have he : (fun y : StandardCapSpace =>
      fderiv ℝ (fun z : StandardCapSpace => radialArclength g₀ ‖z‖) y w) =ᶠ[𝓝 x]
      (fun y => q ‖y‖ * inner ℝ y w) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [← cap_mvfderiv_eq_fderiv]
    exact standardCap_radialArclength_mvfderiv g₀ hy w
  have hrho : ContDiffAt ℝ ∞
      (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x :=
    (radialArclength_contDiff g₀).contDiffAt.comp x (contDiffAt_norm ℝ hx)
  erw [cap_hessian_constant g₀ hrho v w]
  rw [he.fderiv_eq, cap_fderiv_radial_pairing hq hx, cap_connection_constant g₀ hx]
  rw [← cap_mvfderiv_eq_fderiv, standardCap_radialArclength_mvfderiv g₀ hx,
    standardCap_radialArclength_mvfderiv g₀ hx,
    standardCap_radialArclength_mvfderiv g₀ hx, cap_metric_cartesian g₀ hx]
  simp only [capConnectionTerm, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [hqd, cap_radialSpeed_deriv]
  dsimp only [q, capConnectionA, capConnectionB, capConnectionC]
  rw [capRadialExcess_deriv g₀ hn]
  dsimp only [capRadialExcess]
  have hs : (radialSpeed g₀ ‖x‖) ^ 2 = axisRadialCoefficient g₀ ‖x‖ :=
    Real.sq_sqrt (axisRadialCoefficient_pos g₀ ‖x‖).le
  rw [← hs]
  field_simp [hn, (radialSpeed_pos g₀ ‖x‖).ne',
    (axisTangentialCoefficient_pos g₀ ‖x‖).ne']
  ring

theorem standardCap_radialArclength_gradient (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    g₀.connection.gradient (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x =
      (‖x‖ * radialSpeed g₀ ‖x‖)⁻¹ • x := by
  apply (g₀.metric.inner_isInvertible x).inverse_apply_eq.mpr
  ext v
  rw [standardCap_radialArclength_mvfderiv g₀ hx]
  change radialSpeed g₀ ‖x‖ / ‖x‖ * inner ℝ x v =
    g₀.metric.inner x ((‖x‖ * radialSpeed g₀ ‖x‖)⁻¹ • x) v
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [cap_metric_radial g₀ hx]
  have hs : (radialSpeed g₀ ‖x‖) ^ 2 = axisRadialCoefficient g₀ ‖x‖ :=
    Real.sq_sqrt (axisRadialCoefficient_pos g₀ ‖x‖).le
  rw [← hs]
  field_simp [(norm_ne_zero_iff.mpr hx), (radialSpeed_pos g₀ ‖x‖).ne']

theorem standardCap_radialArclength_gradient_sq (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    g₀.metric.inner x
      (g₀.connection.gradient (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x)
      (g₀.connection.gradient (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x) =
        1 := by
  rw [g₀.connection.inner_gradient, standardCap_radialArclength_mvfderiv g₀ hx,
    standardCap_radialArclength_gradient g₀ hx, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp [norm_ne_zero_iff.mpr hx, (radialSpeed_pos g₀ ‖x‖).ne']

theorem standardCap_radial_pair_sq_le (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace)
    (hvv : g₀.metric.inner x v v = 1) (hww : g₀.metric.inner x w w = 1)
    (hvw : g₀.metric.inner x v w = 0) :
    (mvfderiv (𝓡 3) (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x v) ^ 2 +
      (mvfderiv (𝓡 3) (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x w) ^ 2 ≤
        1 := by
  let rho := fun y : StandardCapSpace => radialArclength g₀ ‖y‖
  let U : StandardCapSpace := g₀.connection.gradient rho x
  let dv := mvfderiv (𝓡 3) rho x v
  let dw := mvfderiv (𝓡 3) rho x w
  let G : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := g₀.metric.inner x
  have hUv : G U v = dv := g₀.connection.inner_gradient rho x v
  have hUw : G U w = dw := g₀.connection.inner_gradient rho x w
  have hvU : G v U = dv := (g₀.metric.symm x v U).trans hUv
  have hwU : G w U = dw := (g₀.metric.symm x w U).trans hUw
  have hwv : G w v = 0 := (g₀.metric.symm x w v).trans hvw
  have hUU : G U U = 1 := standardCap_radialArclength_gradient_sq g₀ hx
  have hnn (u : StandardCapSpace) : 0 ≤ G u u := by
    by_cases hu : u = 0
    · simp only [hu, map_zero, le_refl]
    · exact (g₀.metric.pos x u hu).le
  have h := hnn (U - dv • v - dw • w)
  change G v v = 1 at hvv
  change G w w = 1 at hww
  change G v w = 0 at hvw
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
    hUU, hUv, hUw, hvU, hwU, hvv, hww, hvw, hwv] at h
  change dv ^ 2 + dw ^ 2 ≤ 1
  nlinarith only [h]

private theorem cap_scalar_fderiv_comp {f : StandardCapSpace → ℝ} {h : ℝ → ℝ}
    {x : StandardCapSpace} (hf : DifferentiableAt ℝ f x)
    (hh : DifferentiableAt ℝ h (f x)) (v : StandardCapSpace) :
    fderiv ℝ (fun y => h (f y)) x v = deriv h (f x) * fderiv ℝ f x v := by
  change fderiv ℝ (h ∘ f) x v = _
  rw [fderiv_comp x hh hf]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul]

theorem standardCap_connection_inner (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w z : StandardCapSpace) :
    g₀.metric.inner x (g₀.connection.connection (fun _ => w) x v) z =
      deriv (axisTangentialCoefficient g₀) ‖x‖ / (2 * ‖x‖) *
        (inner ℝ x v * inner ℝ w z + inner ℝ x w * inner ℝ v z) +
      ((axisRadialCoefficient g₀ ‖x‖ - axisTangentialCoefficient g₀ ‖x‖) / ‖x‖ ^ 2 -
        deriv (axisTangentialCoefficient g₀) ‖x‖ / (2 * ‖x‖)) *
          inner ℝ v w * inner ℝ x z +
      deriv (fun r => (axisRadialCoefficient g₀ r - axisTangentialCoefficient g₀ r) /
        r ^ 2) ‖x‖ / (2 * ‖x‖) * inner ℝ x v * inner ℝ x w * inner ℝ x z :=
  cap_connection_pairing g₀ hx v w z

theorem standardCap_fderiv_radial {f : ℝ → ℝ} {x : StandardCapSpace}
    (hf : DifferentiableAt ℝ f ‖x‖) (hx : x ≠ 0) (v : StandardCapSpace) :
    fderiv ℝ (fun y : StandardCapSpace => f ‖y‖) x v =
      deriv f ‖x‖ * (inner ℝ x v / ‖x‖) :=
  cap_fderiv_radial hf hx v

theorem standardCap_radial_germ_mvfderiv (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) {F : StandardCapSpace → ℝ} {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h)
    (hF : F =ᶠ[𝓝 x] fun y : StandardCapSpace => h (radialArclength g₀ ‖y‖))
    (v : StandardCapSpace) :
    mvfderiv (𝓡 3) F x v = deriv h (radialArclength g₀ ‖x‖) *
      mvfderiv (𝓡 3) (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x v := by
  rw [cap_mvfderiv_eq_fderiv, cap_mvfderiv_eq_fderiv, hF.fderiv_eq]
  apply cap_scalar_fderiv_comp
  · exact ((radialArclength_contDiff g₀).contDiffAt.comp x
      (contDiffAt_norm ℝ hx)).differentiableAt (by simp)
  · exact hh.differentiable (by simp) _

theorem standardCap_radial_germ_hessian (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) {F : StandardCapSpace → ℝ} {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h)
    (hF : F =ᶠ[𝓝 x] fun y : StandardCapSpace => h (radialArclength g₀ ‖y‖))
    (v w : StandardCapSpace) :
    g₀.connection.hessian F x v w =
      deriv h (radialArclength g₀ ‖x‖) *
        g₀.connection.hessian (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x v w +
      deriv (deriv h) (radialArclength g₀ ‖x‖) *
        mvfderiv (𝓡 3) (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x v *
        mvfderiv (𝓡 3) (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x w := by
  let rho := fun y : StandardCapSpace => radialArclength g₀ ‖y‖
  have hrho {y : StandardCapSpace} (hy : y ≠ 0) : ContDiffAt ℝ ∞ rho y :=
    (radialArclength_contDiff g₀).contDiffAt.comp y (contDiffAt_norm ℝ hy)
  have hrhod {y : StandardCapSpace} (hy : y ≠ 0) : DifferentiableAt ℝ rho y :=
    (hrho hy).differentiableAt (by simp)
  have hh' := (contDiff_infty_iff_deriv.mp hh).2
  have hFs : ContDiffAt ℝ ∞ F x :=
    (hh.contDiffAt.comp x (hrho hx)).congr_of_eventuallyEq hF
  have hDF (u : StandardCapSpace) :
      fderiv ℝ F x u = deriv h (rho x) * fderiv ℝ rho x u := by
    rw [hF.fderiv_eq]
    exact cap_scalar_fderiv_comp (hrhod hx) (hh.differentiable (by simp) _) u
  have he : (fun y : StandardCapSpace => fderiv ℝ F y w) =ᶠ[𝓝 x]
      (fun y => deriv h (rho y) * fderiv ℝ rho y w) := by
    filter_upwards [hF.fderiv (𝕜 := ℝ), isOpen_ne.mem_nhds hx] with y hy hy0
    rw [hy]
    exact cap_scalar_fderiv_comp (hrhod hy0) (hh.differentiable (by simp) _) w
  have hP : DifferentiableAt ℝ (fun y => deriv h (rho y)) x :=
    (hh'.contDiffAt.comp x (hrho hx)).differentiableAt (by simp)
  have hQ : DifferentiableAt ℝ (fun y => fderiv ℝ rho y w) x :=
    (((hrho hx).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  erw [cap_hessian_constant g₀ hFs v w]
  rw [he.fderiv_eq, hDF]
  erw [fderiv_fun_mul hP hQ]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [cap_scalar_fderiv_comp (hrhod hx) (hh'.differentiable (by simp) _) v]
  erw [cap_hessian_constant g₀ (hrho hx) v w]
  simp only [cap_mvfderiv_eq_fderiv]
  change _ = deriv h (rho x) *
    (fderiv ℝ (fun y => fderiv ℝ rho y w) x v -
      fderiv ℝ rho x (g₀.connection.connection (fun _ => w) x v)) +
    deriv (deriv h) (rho x) * fderiv ℝ rho x v * fderiv ℝ rho x w
  ring

theorem standardCap_radial_germ_gradient_sq (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) {F : StandardCapSpace → ℝ} {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h)
    (hF : F =ᶠ[𝓝 x] fun y : StandardCapSpace => h (radialArclength g₀ ‖y‖)) :
    g₀.metric.inner x (g₀.connection.gradient F x) (g₀.connection.gradient F x) =
      (deriv h (radialArclength g₀ ‖x‖)) ^ 2 := by
  let rho := fun y : StandardCapSpace => radialArclength g₀ ‖y‖
  have hd : mvfderiv (𝓡 3) F x = deriv h (rho x) • mvfderiv (𝓡 3) rho x := by
    ext u
    exact standardCap_radial_germ_mvfderiv g₀ hx hh hF u
  have hg : g₀.connection.gradient F x =
      deriv h (rho x) • g₀.connection.gradient rho x := by
    unfold LeviCivitaData.gradient
    rw [hd, map_smul]
  rw [hg]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [standardCap_radialArclength_gradient_sq g₀ hx]
  dsimp only [rho]
  ring

theorem standardCap_sectional_positiveScaling_radial_germ (g₀ : StandardInitialMetric)
    (F : StandardCapSpace → ℝ) (hFs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling g₀.metric (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hFs) (fun _ => Real.exp_pos _)))
    {x : StandardCapSpace} (hx : x ≠ 0) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hF : F =ᶠ[𝓝 x] fun y : StandardCapSpace => h (radialArclength g₀ ‖y‖))
    (v w : StandardCapSpace)
    (hvv : g₀.metric.inner x v v = 1) (hww : g₀.metric.inner x w w = 1)
    (hvw : g₀.metric.inner x v w = 0) :
    let rho := fun y : StandardCapSpace => radialArclength g₀ ‖y‖
    let b := (mvfderiv (𝓡 3) rho x v) ^ 2 + (mvfderiv (𝓡 3) rho x w) ^ 2
    let z := (2 * axisTangentialCoefficient g₀ ‖x‖ +
      ‖x‖ * deriv (axisTangentialCoefficient g₀) ‖x‖) /
        (2 * ‖x‖ * axisTangentialCoefficient g₀ ‖x‖ * radialSpeed g₀ ‖x‖)
    D'.sectionalCurvature x v w = Real.exp (2 * F x) *
      (g₀.connection.sectionalCurvature x v w + deriv h (rho x) * z * (2 - b) +
        deriv (deriv h) (rho x) * b + (deriv h (rho x)) ^ 2 * (b - 1)) := by
  dsimp only
  rw [sectionalCurvature_positiveScaling_exp g₀.metric g₀.connection F hFs D'
    x v w hvv hww hvw]
  rw [standardCap_radial_germ_hessian g₀ hx hh hF,
    standardCap_radial_germ_hessian g₀ hx hh hF,
    standardCap_radial_germ_mvfderiv g₀ hx hh hF,
    standardCap_radial_germ_mvfderiv g₀ hx hh hF,
    standardCap_radial_germ_gradient_sq g₀ hx hh hF,
    standardCap_radialArclength_hessian g₀ hx,
    standardCap_radialArclength_hessian g₀ hx, hvv, hww]
  ring

end PoincareConjecture.MetricSurgery
