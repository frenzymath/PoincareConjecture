import PoincareConjecture.Proofs.M36.StandardCapConcavity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle
open Filter Set Topology

namespace PoincareConjecture.M36

private noncomputable def planeExcess (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  (axisRadialCoefficient g₀ r - axisTangentialCoefficient g₀ r) / r ^ 2

private noncomputable def planeD (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  deriv (axisTangentialCoefficient g₀) r / (2 * r)

private noncomputable def planeE (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  deriv (planeExcess g₀) r / (2 * r)

private noncomputable def planeAlpha (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  planeD g₀ r / axisTangentialCoefficient g₀ r

private noncomputable def planeBeta (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  (planeExcess g₀ r - planeD g₀ r) / axisRadialCoefficient g₀ r

private noncomputable def planeGamma (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  (planeE g₀ r - 2 * planeAlpha g₀ r * planeExcess g₀ r) / axisRadialCoefficient g₀ r

private noncomputable def planeConnectionTerm (g₀ : StandardInitialMetric)
    (x v w : StandardCapSpace) : StandardCapSpace :=
  planeAlpha g₀ ‖x‖ • (inner ℝ x v • w + inner ℝ x w • v) +
    (planeBeta g₀ ‖x‖ * inner ℝ v w + planeGamma g₀ ‖x‖ * inner ℝ x v * inner ℝ x w) • x

private noncomputable def planeGram (v w : StandardCapSpace) : ℝ :=
  inner ℝ v v * inner ℝ w w - (inner ℝ v w) ^ 2

private noncomputable def planeRadialWedge (x v w : StandardCapSpace) : ℝ :=
  (inner ℝ x v) ^ 2 * inner ℝ w w + (inner ℝ x w) ^ 2 * inner ℝ v v -
    2 * inner ℝ x v * inner ℝ x w * inner ℝ v w

private noncomputable def planeCurvatureA (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  planeExcess g₀ r - 2 * planeD g₀ r -
    axisRadialCoefficient g₀ r * r ^ 2 * (planeBeta g₀ r) ^ 2

private noncomputable def planeCurvatureB (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  planeE g₀ r - deriv (planeD g₀) r / r +
    axisTangentialCoefficient g₀ r * (planeAlpha g₀ r) ^ 2 -
      axisRadialCoefficient g₀ r * planeBeta g₀ r *
        (2 * planeAlpha g₀ r + r ^ 2 * planeGamma g₀ r)

private theorem planeExcess_smooth (g₀ : StandardInitialMetric) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (planeExcess g₀) r :=
  ((axisRadialCoefficient_contDiff g₀).contDiffAt.sub
    (axisTangentialCoefficient_contDiff g₀).contDiffAt).div
      (contDiffAt_id.pow 2) (pow_ne_zero 2 hr)

private theorem planeD_smooth (g₀ : StandardInitialMetric) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (planeD g₀) r :=
  ((contDiff_infty_iff_deriv.mp (axisTangentialCoefficient_contDiff g₀)).2.contDiffAt).div
    (contDiffAt_const.mul contDiffAt_id) (mul_ne_zero (by norm_num) hr)

private theorem planeE_smooth (g₀ : StandardInitialMetric) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (planeE g₀) r :=
  ((planeExcess_smooth g₀ hr).derivWithin (m := ∞) (by simp)).div
    (contDiffAt_const.mul contDiffAt_id) (mul_ne_zero (by norm_num) hr)

private theorem plane_metric_cartesian (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace) :
    g₀.metric.inner x v w = axisTangentialCoefficient g₀ ‖x‖ * inner ℝ v w +
      planeExcess g₀ ‖x‖ * inner ℝ x v * inner ℝ x w := by
  rw [standard_metric_radial_formula g₀ x hx]
  simp only [real_inner_smul_left]
  dsimp only [planeExcess]
  ring

private theorem plane_metric_radial (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v : StandardCapSpace) :
    g₀.metric.inner x x v = axisRadialCoefficient g₀ ‖x‖ * inner ℝ x v := by
  rw [plane_metric_cartesian g₀ hx, real_inner_self_eq_norm_sq]
  dsimp only [planeExcess]
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

private theorem plane_connection_pairing (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w z : StandardCapSpace) :
    g₀.metric.inner x (g₀.connection.connection (fun _ => w) x v) z =
      planeD g₀ ‖x‖ * (inner ℝ x v * inner ℝ w z + inner ℝ x w * inner ℝ v z) +
      (planeExcess g₀ ‖x‖ - planeD g₀ ‖x‖) * inner ℝ v w * inner ℝ x z +
      planeE g₀ ‖x‖ * inner ℝ x v * inner ℝ x w * inner ℝ x z :=
  standardCap_connection_inner g₀ hx v w z

private theorem plane_connection_constant (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace) :
    g₀.connection.connection (fun _ => w) x v = planeConnectionTerm g₀ x v w := by
  have hp (z : StandardCapSpace) :
      g₀.metric.inner x (g₀.connection.connection (fun _ => w) x v) z =
        g₀.metric.inner x (planeConnectionTerm g₀ x v w) z := by
    rw [plane_connection_pairing g₀ hx]
    let G : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := g₀.metric.inner x
    change _ = G (planeConnectionTerm g₀ x v w) z
    simp only [planeConnectionTerm, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    rw [show G w z = _ from plane_metric_cartesian g₀ hx w z,
      show G v z = _ from plane_metric_cartesian g₀ hx v z,
      show G x z = _ from plane_metric_radial g₀ hx z]
    dsimp only [planeAlpha, planeBeta, planeGamma]
    field_simp [(axisRadialCoefficient_pos g₀ ‖x‖).ne',
      (axisTangentialCoefficient_pos g₀ ‖x‖).ne']
    ring
  let u : StandardCapSpace := g₀.connection.connection (fun _ => w) x v
  change u = planeConnectionTerm g₀ x v w
  by_contra hne
  have hpos := g₀.metric.pos x _ (sub_ne_zero.mpr hne)
  let G : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := g₀.metric.inner x
  have hz : G u (u - planeConnectionTerm g₀ x v w) =
      G (planeConnectionTerm g₀ x v w) (u - planeConnectionTerm g₀ x v w) := hp _
  have hzero : g₀.metric.inner x
      (u - planeConnectionTerm g₀ x v w) (u - planeConnectionTerm g₀ x v w) = 0 := by
    change G (u - planeConnectionTerm g₀ x v w) (u - planeConnectionTerm g₀ x v w) = 0
    rw [map_sub G, sub_apply, hz, sub_self]
  exact hpos.ne' hzero

private theorem plane_fderiv_inner (x v w : StandardCapSpace) :
    fderiv ℝ (fun y : StandardCapSpace => inner ℝ y w) x v = inner ℝ v w := by
  change fderiv ℝ ((innerSL ℝ).flip w) x v = _
  rw [ContinuousLinearMap.fderiv]
  rfl

private theorem plane_fderiv_linear {f : ℝ → ℝ} {x : StandardCapSpace}
    (hf : DifferentiableAt ℝ f ‖x‖) (hx : x ≠ 0) (v z : StandardCapSpace) :
    fderiv ℝ (fun y : StandardCapSpace => f ‖y‖ * inner ℝ y v) x z =
      deriv f ‖x‖ * (inner ℝ x z / ‖x‖) * inner ℝ x v +
        f ‖x‖ * inner ℝ z v := by
  erw [fderiv_fun_mul (hf.comp x ((differentiableAt_id (𝕜 := ℝ)).norm ℝ hx))
    (differentiableAt_id.inner ℝ (differentiableAt_const v))]
  simp only [Function.comp_def, id_eq]
  simp only [add_apply, smul_apply, smul_eq_mul,
    standardCap_fderiv_radial hf hx, plane_fderiv_inner]
  ring

private theorem plane_fderiv_cubic {f : ℝ → ℝ} {x : StandardCapSpace}
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
    standardCap_fderiv_radial hf hx, plane_fderiv_inner, Nat.reduceSub, pow_one]
  ring

private theorem plane_fderiv_combination {f g h : ℝ → ℝ} {x : StandardCapSpace}
    (hf : DifferentiableAt ℝ f ‖x‖) (hg : DifferentiableAt ℝ g ‖x‖)
    (hh : DifferentiableAt ℝ h ‖x‖) (hx : x ≠ 0)
    (A B : ℝ) (v w z : StandardCapSpace) :
    fderiv ℝ (fun y : StandardCapSpace => A * (f ‖y‖ * inner ℝ y v) +
      B * (g ‖y‖ * inner ℝ y w) + h ‖y‖ * (inner ℝ y v) ^ 2 * inner ℝ y w) x z =
      A * (deriv f ‖x‖ * (inner ℝ x z / ‖x‖) * inner ℝ x v + f ‖x‖ * inner ℝ z v) +
      B * (deriv g ‖x‖ * (inner ℝ x z / ‖x‖) * inner ℝ x w + g ‖x‖ * inner ℝ z w) +
      (deriv h ‖x‖ * (inner ℝ x z / ‖x‖) * (inner ℝ x v) ^ 2 * inner ℝ x w +
        2 * h ‖x‖ * inner ℝ x v * inner ℝ z v * inner ℝ x w +
          h ‖x‖ * (inner ℝ x v) ^ 2 * inner ℝ z w) := by
  have hn := (differentiableAt_id (𝕜 := ℝ) (x := x)).norm ℝ hx
  have hv : DifferentiableAt ℝ (fun y : StandardCapSpace => inner ℝ y v) x :=
    differentiableAt_id.inner ℝ (differentiableAt_const v)
  have hw : DifferentiableAt ℝ (fun y : StandardCapSpace => inner ℝ y w) x :=
    differentiableAt_id.inner ℝ (differentiableAt_const w)
  have hf' := (hf.comp x hn).mul hv
  have hg' := (hg.comp x hn).mul hw
  have hh' := ((hh.comp x hn).mul (hv.pow 2)).mul hw
  erw [fderiv_fun_add ((hf'.const_mul A).add (hg'.const_mul B)) hh',
    fderiv_fun_add (hf'.const_mul A) (hg'.const_mul B),
    fderiv_const_mul hf' A, fderiv_const_mul hg' B]
  simp only [Function.comp_def, Pi.mul_def, Pi.pow_def]
  simp only [add_apply, smul_apply, smul_eq_mul,
    plane_fderiv_linear hf hx, plane_fderiv_linear hg hx, plane_fderiv_cubic hh hx]

private theorem plane_connection_derivative_difference (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace) :
    fderiv ℝ (fun y => g₀.metric.inner y
      (g₀.connection.connection (fun _ => w) y w) v) x v -
    fderiv ℝ (fun y => g₀.metric.inner y
      (g₀.connection.connection (fun _ => w) y v) v) x w =
      (planeExcess g₀ ‖x‖ - 2 * planeD g₀ ‖x‖) * planeGram v w +
        (planeE g₀ ‖x‖ - deriv (planeD g₀) ‖x‖ / ‖x‖) * planeRadialWedge x v w := by
  have hwv : inner ℝ w v = inner ℝ v w := real_inner_comm v w
  have hS : (fun y => g₀.metric.inner y
      (g₀.connection.connection (fun _ => w) y w) v) =ᶠ[𝓝 x]
      (fun y => (2 * inner ℝ v w) * (planeD g₀ ‖y‖ * inner ℝ y w) +
        inner ℝ w w * ((planeExcess g₀ ‖y‖ - planeD g₀ ‖y‖) * inner ℝ y v) +
          planeE g₀ ‖y‖ * (inner ℝ y w) ^ 2 * inner ℝ y v) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [plane_connection_pairing g₀ hy, hwv]
    ring
  have hT : (fun y => g₀.metric.inner y
      (g₀.connection.connection (fun _ => w) y v) v) =ᶠ[𝓝 x]
      (fun y => inner ℝ v w * (planeExcess g₀ ‖y‖ * inner ℝ y v) +
        inner ℝ v v * (planeD g₀ ‖y‖ * inner ℝ y w) +
          planeE g₀ ‖y‖ * (inner ℝ y v) ^ 2 * inner ℝ y w) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [plane_connection_pairing g₀ hy, hwv]
    ring
  have hE := (planeExcess_smooth g₀ (norm_ne_zero_iff.mpr hx)).differentiableAt (by simp)
  have hd := (planeD_smooth g₀ (norm_ne_zero_iff.mpr hx)).differentiableAt (by simp)
  have he := (planeE_smooth g₀ (norm_ne_zero_iff.mpr hx)).differentiableAt (by simp)
  rw [hS.fderiv_eq, hT.fderiv_eq]
  erw [plane_fderiv_combination hd (hE.sub hd) he hx,
    plane_fderiv_combination hE hd he hx]
  rw [deriv_sub hE hd, hwv]
  dsimp only [planeE, planeGram, planeRadialWedge, Pi.sub_apply]
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

private theorem plane_connection_correction (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace) :
    -g₀.metric.inner x (g₀.connection.connection (fun _ => w) x w)
        (g₀.connection.connection (fun _ => v) x v) +
      g₀.metric.inner x (g₀.connection.connection (fun _ => w) x v)
        (g₀.connection.connection (fun _ => v) x w) =
      -(axisRadialCoefficient g₀ ‖x‖ * ‖x‖ ^ 2 * (planeBeta g₀ ‖x‖) ^ 2) *
        planeGram v w +
      (axisTangentialCoefficient g₀ ‖x‖ * (planeAlpha g₀ ‖x‖) ^ 2 -
        axisRadialCoefficient g₀ ‖x‖ * planeBeta g₀ ‖x‖ *
          (2 * planeAlpha g₀ ‖x‖ + ‖x‖ ^ 2 * planeGamma g₀ ‖x‖)) *
        planeRadialWedge x v w := by
  rw [plane_connection_constant g₀ hx, plane_connection_constant g₀ hx,
    plane_connection_constant g₀ hx, plane_connection_constant g₀ hx,
    plane_metric_cartesian g₀ hx, plane_metric_cartesian g₀ hx]
  have ha : axisRadialCoefficient g₀ ‖x‖ =
      axisTangentialCoefficient g₀ ‖x‖ + planeExcess g₀ ‖x‖ * ‖x‖ ^ 2 := by
    dsimp only [planeExcess]
    field_simp [norm_ne_zero_iff.mpr hx]
    ring
  have hxx : inner ℝ x x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  have hvx : inner ℝ v x = inner ℝ x v := real_inner_comm x v
  have hwx : inner ℝ w x = inner ℝ x w := real_inner_comm x w
  have hwv : inner ℝ w v = inner ℝ v w := real_inner_comm v w
  dsimp only [planeConnectionTerm, planeGram, planeRadialWedge]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hxx, hvx, hwx, hwv]
  rw [ha]
  ring

private theorem plane_constant_smooth (v : StandardCapSpace) :
    ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
      (fun x : StandardCapSpace => (⟨x, v⟩ : TangentBundle (𝓡 3) StandardCapSpace)) :=
  contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const

private theorem plane_constant_bracket (v w : StandardCapSpace) :
    VectorField.mlieBracket (𝓡 3) (fun _ : StandardCapSpace => v)
      (fun _ : StandardCapSpace => w) = 0 := by
  unfold VectorField.mlieBracket
  erw [VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin_univ]
  simp [VectorField.lieBracket]
  rfl

private theorem plane_curvature_numerator (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace) :
    g₀.connection.curvatureTensor x v w v w =
      planeCurvatureA g₀ ‖x‖ * planeGram v w +
        planeCurvatureB g₀ ‖x‖ * planeRadialWedge x v w := by
  let X := fun _ : StandardCapSpace => v
  let Y := fun _ : StandardCapSpace => w
  let W := fun y => g₀.connection.connection Y y w
  let V := fun y => g₀.connection.connection Y y v
  have hX := plane_constant_smooth v
  have hY := plane_constant_smooth w
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
  have hdiff := plane_connection_derivative_difference g₀ hx v w
  have hcorr := plane_connection_correction g₀ hx v w
  unfold LeviCivitaData.curvatureTensor
  rw [← M04.curvatureOnFields_eq_curvature g₀.connection isOpen_univ
    hX.contMDiffOn hY.contMDiffOn hY.contMDiffOn (mem_univ x)]
  change g₀.metric.inner x (g₀.connection.connection W x v -
    g₀.connection.connection V x w -
    g₀.connection.connection Y x (VectorField.mlieBracket (𝓡 3) X Y x)) v = _
  rw [show VectorField.mlieBracket (𝓡 3) X Y x = 0 by
    exact congrFun (plane_constant_bracket v w) x, map_zero, sub_zero]
  simp only [map_sub, sub_apply]
  dsimp only [planeCurvatureA, planeCurvatureB]
  change fderiv ℝ (fun y => g₀.metric.inner y (W y) v) x v -
    fderiv ℝ (fun y => g₀.metric.inner y (V y) v) x w = _ at hdiff
  change -g₀.metric.inner x (W x) (g₀.connection.connection X x v) +
    g₀.metric.inner x (V x) (g₀.connection.connection X x w) = _ at hcorr
  nlinarith only [hDW, hDV, hdiff, hcorr]

private theorem plane_basis_inner (i j : Fin 3) :
    inner ℝ (axisBasis i) (axisBasis j) = if i = j then 1 else 0 := by
  simp [axisBasis, EuclideanSpace.inner_single_left]

private theorem plane_axis_norm {r : ℝ} (hr : 0 < r) : ‖axisPoint r‖ = r := by
  rw [axisPoint_eq_smul]
  simp [axisBasis, norm_smul, abs_of_pos hr]

private theorem plane_axis_ne_zero {r : ℝ} (hr : 0 < r) : axisPoint r ≠ 0 := by
  exact norm_ne_zero_iff.mp ((plane_axis_norm hr).trans_ne hr.ne')

private theorem plane_axis_inner (r : ℝ) (i : Fin 3) :
    inner ℝ (axisPoint r) (axisBasis i) = r * (if 0 = i then 1 else 0) := by
  rw [axisPoint_eq_smul, real_inner_smul_left, plane_basis_inner]

private theorem plane_curvatureA_axis (g₀ : StandardInitialMetric) {r : ℝ}
    (hr : 0 < r) :
    planeCurvatureA g₀ r = (axisTangentialCoefficient g₀ r) ^ 2 *
      g₀.connection.sectionalCurvature (axisPoint r) (axisBasis 1) (axisBasis 2) := by
  have hnum := plane_curvature_numerator g₀ (plane_axis_ne_zero hr)
    (axisBasis 1) (axisBasis 2)
  have hnum' : g₀.connection.curvatureTensor (axisPoint r)
      (axisBasis 1) (axisBasis 2) (axisBasis 1) (axisBasis 2) =
      planeCurvatureA g₀ r := by
    simp only [planeGram, planeRadialWedge, plane_axis_inner, plane_basis_inner,
      plane_axis_norm hr] at hnum
    norm_num [Fin.ext_iff] at hnum
    exact hnum
  have hc : axisTangentialCoefficient g₀ r ≠ 0 :=
    (axisTangentialCoefficient_pos g₀ r).ne'
  unfold LeviCivitaData.sectionalCurvature
  rw [hnum', axis_metric_one_two, ← axis_metric_tangential_eq]
  change planeCurvatureA g₀ r = (axisTangentialCoefficient g₀ r) ^ 2 *
    (planeCurvatureA g₀ r /
      (axisTangentialCoefficient g₀ r * axisTangentialCoefficient g₀ r - 0 ^ 2))
  field_simp [hc]
  ring

private theorem plane_curvatureAB_axis (g₀ : StandardInitialMetric) {r : ℝ}
    (hr : 0 < r) :
    planeCurvatureA g₀ r + r ^ 2 * planeCurvatureB g₀ r =
      axisRadialCoefficient g₀ r * axisTangentialCoefficient g₀ r *
        g₀.connection.sectionalCurvature (axisPoint r) (axisBasis 0) (axisBasis 1) := by
  have hnum := plane_curvature_numerator g₀ (plane_axis_ne_zero hr)
    (axisBasis 0) (axisBasis 1)
  have hnum' : g₀.connection.curvatureTensor (axisPoint r)
      (axisBasis 0) (axisBasis 1) (axisBasis 0) (axisBasis 1) =
      planeCurvatureA g₀ r + r ^ 2 * planeCurvatureB g₀ r := by
    simp only [planeGram, planeRadialWedge, plane_axis_inner, plane_basis_inner,
      plane_axis_norm hr] at hnum
    norm_num at hnum
    simpa only [mul_comm] using hnum
  have ha : axisRadialCoefficient g₀ r ≠ 0 :=
    (axisRadialCoefficient_pos g₀ r).ne'
  have hc : axisTangentialCoefficient g₀ r ≠ 0 :=
    (axisTangentialCoefficient_pos g₀ r).ne'
  unfold LeviCivitaData.sectionalCurvature
  rw [hnum', axis_metric_zero_one]
  change planeCurvatureA g₀ r + r ^ 2 * planeCurvatureB g₀ r =
    axisRadialCoefficient g₀ r * axisTangentialCoefficient g₀ r *
      ((planeCurvatureA g₀ r + r ^ 2 * planeCurvatureB g₀ r) /
        (axisRadialCoefficient g₀ r * axisTangentialCoefficient g₀ r - 0 ^ 2))
  field_simp [ha, hc]
  ring

private theorem plane_orthonormal_metric_equations (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace)
    (hvv : g₀.metric.inner x v v = 1) (hww : g₀.metric.inner x w w = 1)
    (hvw : g₀.metric.inner x v w = 0) :
    let c := axisTangentialCoefficient g₀ ‖x‖
    let e := planeExcess g₀ ‖x‖
    c * inner ℝ v v + e * (inner ℝ x v) ^ 2 = 1 ∧
      c * inner ℝ w w + e * (inner ℝ x w) ^ 2 = 1 ∧
      c * inner ℝ v w + e * inner ℝ x v * inner ℝ x w = 0 := by
  dsimp only
  constructor
  · rw [plane_metric_cartesian g₀ hx] at hvv
    nlinarith only [hvv]
  constructor
  · rw [plane_metric_cartesian g₀ hx] at hww
    nlinarith only [hww]
  · rw [← plane_metric_cartesian g₀ hx]
    exact hvw

private theorem plane_orthonormal_wedge (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace)
    (hvv : g₀.metric.inner x v v = 1) (hww : g₀.metric.inner x w w = 1)
    (hvw : g₀.metric.inner x v w = 0) :
    axisTangentialCoefficient g₀ ‖x‖ * planeRadialWedge x v w =
      (inner ℝ x v) ^ 2 + (inner ℝ x w) ^ 2 := by
  have he := plane_orthonormal_metric_equations g₀ hx v w hvv hww hvw
  dsimp only at he
  dsimp only [planeRadialWedge]
  linear_combination
    (inner ℝ x v) ^ 2 * he.2.1 +
      (inner ℝ x w) ^ 2 * he.1 -
      2 * inner ℝ x v * inner ℝ x w * he.2.2

private theorem plane_orthonormal_gram (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace)
    (hvv : g₀.metric.inner x v v = 1) (hww : g₀.metric.inner x w w = 1)
    (hvw : g₀.metric.inner x v w = 0) :
    (axisTangentialCoefficient g₀ ‖x‖) ^ 2 * planeGram v w +
      axisTangentialCoefficient g₀ ‖x‖ * planeExcess g₀ ‖x‖ *
        planeRadialWedge x v w = 1 := by
  have he := plane_orthonormal_metric_equations g₀ hx v w hvv hww hvw
  have hw := plane_orthonormal_wedge g₀ hx v w hvv hww hvw
  dsimp only at he
  have hvv' := eq_sub_of_add_eq he.1
  have hww' := eq_sub_of_add_eq he.2.1
  have hvw' : axisTangentialCoefficient g₀ ‖x‖ * inner ℝ v w =
      -planeExcess g₀ ‖x‖ * inner ℝ x v * inner ℝ x w := by
    nlinarith only [he.2.2]
  dsimp only [planeGram]
  calc
    (axisTangentialCoefficient g₀ ‖x‖) ^ 2 *
          (inner ℝ v v * inner ℝ w w - (inner ℝ v w) ^ 2) +
        axisTangentialCoefficient g₀ ‖x‖ * planeExcess g₀ ‖x‖ *
          planeRadialWedge x v w =
      (axisTangentialCoefficient g₀ ‖x‖ * inner ℝ v v) *
          (axisTangentialCoefficient g₀ ‖x‖ * inner ℝ w w) -
        (axisTangentialCoefficient g₀ ‖x‖ * inner ℝ v w) ^ 2 +
        planeExcess g₀ ‖x‖ *
          (axisTangentialCoefficient g₀ ‖x‖ * planeRadialWedge x v w) := by ring
    _ = (1 - planeExcess g₀ ‖x‖ * (inner ℝ x v) ^ 2) *
          (1 - planeExcess g₀ ‖x‖ * (inner ℝ x w) ^ 2) -
        (-planeExcess g₀ ‖x‖ * inner ℝ x v * inner ℝ x w) ^ 2 +
        planeExcess g₀ ‖x‖ *
          ((inner ℝ x v) ^ 2 + (inner ℝ x w) ^ 2) := by
      rw [hvv', hww', hvw', hw]
    _ = 1 := by ring

private theorem plane_radial_weight (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace)
    (hvv : g₀.metric.inner x v v = 1) (hww : g₀.metric.inner x w w = 1)
    (hvw : g₀.metric.inner x v w = 0) :
    (mvfderiv (𝓡 3) (fun y : StandardCapSpace =>
      radialArclength g₀ ‖y‖) x v) ^ 2 +
      (mvfderiv (𝓡 3) (fun y : StandardCapSpace =>
        radialArclength g₀ ‖y‖) x w) ^ 2 =
      axisRadialCoefficient g₀ ‖x‖ * axisTangentialCoefficient g₀ ‖x‖ *
        planeRadialWedge x v w / ‖x‖ ^ 2 := by
  rw [standardCap_radialArclength_mvfderiv g₀ hx,
    standardCap_radialArclength_mvfderiv g₀ hx]
  have hs : (radialSpeed g₀ ‖x‖) ^ 2 = axisRadialCoefficient g₀ ‖x‖ := by
    exact Real.sq_sqrt (axisRadialCoefficient_pos g₀ ‖x‖).le
  have hc := plane_orthonormal_wedge g₀ hx v w hvv hww hvw
  simp only [mul_pow, div_pow, hs]
  calc
    axisRadialCoefficient g₀ ‖x‖ / ‖x‖ ^ 2 * (inner ℝ x v) ^ 2 +
        axisRadialCoefficient g₀ ‖x‖ / ‖x‖ ^ 2 * (inner ℝ x w) ^ 2 =
      axisRadialCoefficient g₀ ‖x‖ / ‖x‖ ^ 2 *
        ((inner ℝ x v) ^ 2 + (inner ℝ x w) ^ 2) := by ring
    _ = _ := by rw [← hc]; ring

theorem standardCap_sectional_plane (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (v w : StandardCapSpace)
    (hvv : g₀.metric.inner x v v = 1) (hww : g₀.metric.inner x w w = 1)
    (hvw : g₀.metric.inner x v w = 0) :
    let b := (mvfderiv (𝓡 3) (fun y : StandardCapSpace =>
      radialArclength g₀ ‖y‖) x v) ^ 2 +
      (mvfderiv (𝓡 3) (fun y : StandardCapSpace =>
        radialArclength g₀ ‖y‖) x w) ^ 2
    g₀.connection.sectionalCurvature x v w =
      b * g₀.connection.sectionalCurvature (axisPoint ‖x‖)
          (axisBasis 0) (axisBasis 1) +
        (1 - b) * g₀.connection.sectionalCurvature (axisPoint ‖x‖)
          (axisBasis 1) (axisBasis 2) := by
  dsimp only
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr0 : ‖x‖ ≠ 0 := hr.ne'
  have hc : axisTangentialCoefficient g₀ ‖x‖ ≠ 0 :=
    (axisTangentialCoefficient_pos g₀ ‖x‖).ne'
  have hden : g₀.metric.inner x v v * g₀.metric.inner x w w -
      (g₀.metric.inner x v w) ^ 2 = 1 := by
    rw [hvv, hww, hvw]
    norm_num
  have hnum := plane_curvature_numerator g₀ hx v w
  have hg := plane_orthonormal_gram g₀ hx v w hvv hww hvw
  have hb := plane_radial_weight g₀ hx v w hvv hww hvw
  have hA := plane_curvatureA_axis g₀ hr
  have hAB := plane_curvatureAB_axis g₀ hr
  have hB : planeCurvatureB g₀ ‖x‖ =
      (axisRadialCoefficient g₀ ‖x‖ * axisTangentialCoefficient g₀ ‖x‖ *
          g₀.connection.sectionalCurvature (axisPoint ‖x‖)
            (axisBasis 0) (axisBasis 1) -
        (axisTangentialCoefficient g₀ ‖x‖) ^ 2 *
          g₀.connection.sectionalCurvature (axisPoint ‖x‖)
            (axisBasis 1) (axisBasis 2)) / ‖x‖ ^ 2 := by
    calc
      planeCurvatureB g₀ ‖x‖ =
          ((planeCurvatureA g₀ ‖x‖ + ‖x‖ ^ 2 *
              planeCurvatureB g₀ ‖x‖) - planeCurvatureA g₀ ‖x‖) /
            ‖x‖ ^ 2 := by
              field_simp [hr0]
              ring
      _ = (axisRadialCoefficient g₀ ‖x‖ * axisTangentialCoefficient g₀ ‖x‖ *
          g₀.connection.sectionalCurvature (axisPoint ‖x‖)
            (axisBasis 0) (axisBasis 1) -
        (axisTangentialCoefficient g₀ ‖x‖) ^ 2 *
          g₀.connection.sectionalCurvature (axisPoint ‖x‖)
            (axisBasis 1) (axisBasis 2)) / ‖x‖ ^ 2 := by
              rw [hAB, hA]
  have hGc : (axisTangentialCoefficient g₀ ‖x‖) ^ 2 * planeGram v w =
      1 - axisTangentialCoefficient g₀ ‖x‖ * planeExcess g₀ ‖x‖ *
        planeRadialWedge x v w := by
    nlinarith only [hg]
  change g₀.connection.curvatureTensor x v w v w /
      (g₀.metric.inner x v v * g₀.metric.inner x w w -
        (g₀.metric.inner x v w) ^ 2) = _
  rw [hden, div_one, hnum, hb]
  calc
    planeCurvatureA g₀ ‖x‖ * planeGram v w +
        planeCurvatureB g₀ ‖x‖ * planeRadialWedge x v w =
      (planeCurvatureA g₀ ‖x‖ /
        (axisTangentialCoefficient g₀ ‖x‖) ^ 2) *
          ((axisTangentialCoefficient g₀ ‖x‖) ^ 2 * planeGram v w) +
        planeCurvatureB g₀ ‖x‖ * planeRadialWedge x v w := by
          field_simp [hc]
    _ = (planeCurvatureA g₀ ‖x‖ /
        (axisTangentialCoefficient g₀ ‖x‖) ^ 2) *
          (1 - axisTangentialCoefficient g₀ ‖x‖ *
            planeExcess g₀ ‖x‖ * planeRadialWedge x v w) +
        planeCurvatureB g₀ ‖x‖ * planeRadialWedge x v w := by rw [hGc]
    _ = (axisRadialCoefficient g₀ ‖x‖ * axisTangentialCoefficient g₀ ‖x‖ *
          g₀.connection.sectionalCurvature (axisPoint ‖x‖)
            (axisBasis 0) (axisBasis 1) * planeRadialWedge x v w /
          ‖x‖ ^ 2) +
        (1 - axisRadialCoefficient g₀ ‖x‖ * axisTangentialCoefficient g₀ ‖x‖ *
          planeRadialWedge x v w / ‖x‖ ^ 2) *
          g₀.connection.sectionalCurvature (axisPoint ‖x‖)
            (axisBasis 1) (axisBasis 2) := by
          rw [hA, hB]
          dsimp only [planeExcess]
          field_simp [hr0, hc]
          ring
    _ = _ := by ring

private theorem plane_angular_log_derivative (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) :
    (2 * axisTangentialCoefficient g₀ r +
      r * deriv (axisTangentialCoefficient g₀) r) /
        (2 * r * axisTangentialCoefficient g₀ r * radialSpeed g₀ r) =
      angularRadiusSlope g₀ r / euclideanWarpRadius g₀ r := by
  rw [angularRadiusSlope_eq, euclideanWarpRadius]
  have hc := axisTangentialCoefficient_pos g₀ r
  have hs := Real.sq_sqrt hc.le
  have hs0 := (Real.sqrt_pos.mpr hc).ne'
  generalize Real.sqrt (axisTangentialCoefficient g₀ r) = s at *
  rw [← hs]
  field_simp [hr.ne', hs0, (radialSpeed_pos g₀ r).ne']

theorem standardCap_sectional_positiveScaling_endpoints (g₀ : StandardInitialMetric)
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
    let z := angularRadiusSlope g₀ ‖x‖ / euclideanWarpRadius g₀ ‖x‖
    D'.sectionalCurvature x v w = Real.exp (2 * F x) *
      (b * (g₀.connection.sectionalCurvature (axisPoint ‖x‖)
          (axisBasis 0) (axisBasis 1) + deriv (deriv h) (rho x) +
            deriv h (rho x) * z) +
        (1 - b) * (g₀.connection.sectionalCurvature (axisPoint ‖x‖)
          (axisBasis 1) (axisBasis 2) + 2 * deriv h (rho x) * z -
            (deriv h (rho x)) ^ 2)) := by
  dsimp only
  rw [standardCap_sectional_positiveScaling_radial_germ g₀ F hFs D'
    hx hh hF v w hvv hww hvw,
    plane_angular_log_derivative g₀ (norm_pos_iff.mpr hx),
    standardCap_sectional_plane g₀ hx v w hvv hww hvw]
  ring

theorem standardCap_sectional_positiveScaling_pos (g₀ : StandardInitialMetric)
    (F : StandardCapSpace → ℝ) (hFs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling g₀.metric (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hFs) (fun _ => Real.exp_pos _)))
    {x : StandardCapSpace} (hx : x ≠ 0) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hF : F =ᶠ[𝓝 x] fun y : StandardCapSpace => h (radialArclength g₀ ‖y‖))
    (hR : 0 < g₀.connection.sectionalCurvature (axisPoint ‖x‖)
      (axisBasis 0) (axisBasis 1) + deriv (deriv h) (radialArclength g₀ ‖x‖) +
        deriv h (radialArclength g₀ ‖x‖) *
          (angularRadiusSlope g₀ ‖x‖ / euclideanWarpRadius g₀ ‖x‖))
    (hT : 0 < g₀.connection.sectionalCurvature (axisPoint ‖x‖)
      (axisBasis 1) (axisBasis 2) + 2 * deriv h (radialArclength g₀ ‖x‖) *
        (angularRadiusSlope g₀ ‖x‖ / euclideanWarpRadius g₀ ‖x‖) -
          (deriv h (radialArclength g₀ ‖x‖)) ^ 2)
    (v w : StandardCapSpace)
    (hvv : g₀.metric.inner x v v = 1) (hww : g₀.metric.inner x w w = 1)
    (hvw : g₀.metric.inner x v w = 0) :
    0 < D'.sectionalCurvature x v w := by
  rw [standardCap_sectional_positiveScaling_endpoints g₀ F hFs D'
    hx hh hF v w hvv hww hvw]
  let b := (mvfderiv (𝓡 3) (fun y : StandardCapSpace =>
    radialArclength g₀ ‖y‖) x v) ^ 2 +
      (mvfderiv (𝓡 3) (fun y : StandardCapSpace =>
        radialArclength g₀ ‖y‖) x w) ^ 2
  have hb0 : 0 ≤ b := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hb1 : b ≤ 1 := standardCap_radial_pair_sq_le g₀ hx v w hvv hww hvw
  apply mul_pos (Real.exp_pos _)
  by_cases hb : b = 0
  · change 0 < b * _ + (1 - b) * _
    simpa only [hb, zero_mul, sub_zero, one_mul, zero_add] using hT
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hb0 (Ne.symm hb)) hR)
      (mul_nonneg (sub_nonneg.mpr hb1) hT.le)

end PoincareConjecture.M36
