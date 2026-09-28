import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Construction.MetricCombination
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Connection.Koszul
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Connection.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Positivity.TensorNullMinimum
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.CurvaturePointwise
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module









set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Filter Set Topology

universe u

namespace PoincareConjecture.MetricSurgery

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
theorem contMDiff_exp_neg_two {F : M → ℝ}
    (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => Real.exp (-2 * F y)) :=
  Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hF)

omit [IsManifold (𝓡 n) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
theorem mvfderiv_exp_neg_two {F : M → ℝ} {x : M}
    (hF : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) F x)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => Real.exp (-2 * F y)) x v =
      -2 * Real.exp (-2 * F x) * mvfderiv (𝓡 n) F x v := by
  let φ : ℝ → ℝ := fun s => Real.exp (-2 * s)
  have hφ (s : ℝ) : HasDerivAt φ (Real.exp (-2 * s) * (-2)) s := by
    simpa [φ] using ((hasDerivAt_id s).const_mul (-2)).exp
  change mvfderiv (𝓡 n) (φ ∘ F) x v = _
  calc
    _ = deriv φ (F x) * mvfderiv (𝓡 n) F x v := by
      rw [mvfderiv_comp_apply x (hφ (F x)).differentiableAt.mdifferentiableAt hF v]
      simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
      exact fderiv_eq_deriv_mul (𝕜 := ℝ)
    _ = _ := by rw [(hφ (F x)).deriv]; ring


theorem mvfderiv_conformal_inner (g : RiemannianMetric n M)
    {F : M → ℝ} {x : M}
    (hF : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) F x)
    {Y Z : (y : M) → TangentSpace (𝓡 n) y}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) x) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => Real.exp (-2 * F y) * g.inner y (Y y) (Z y)) x v =
      Real.exp (-2 * F x) *
        (mvfderiv (𝓡 n) (fun y => g.inner y (Y y) (Z y)) x v -
          2 * mvfderiv (𝓡 n) F x v * g.inner x (Y x) (Z x)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hg : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => g.inner y (Y y) (Z y)) x := hY.inner_bundle hZ
  have hprod : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => (-2 : ℝ) * F y) x := mdifferentiableAt_const.mul hF
  have he : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => Real.exp (-2 * F y)) x :=
    Real.differentiable_exp.comp_mdifferentiableAt hprod
  rw [mvfderiv_fun_mul he hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [mvfderiv_exp_neg_two hF]
  ring



theorem connection_positiveScaling_exp
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (F : M → ℝ) (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling g (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)))
    {Y : (y : M) → TangentSpace (𝓡 n) y} {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x) (v : TangentSpace (𝓡 n) x) :
    D'.connection Y x v = D.connection Y x v -
      mvfderiv (𝓡 n) F x v • Y x - mvfderiv (𝓡 n) F x (Y x) • v +
      g.inner x v (Y x) • D.gradient F x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro w
  change g.inner x (D'.connection Y x v) w = g.inner x _ w
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  have hX := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have hZ := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w
  have hD := D.normalization_koszul X Y Z hX hY hZ
  have hD' := D'.normalization_koszul X Y Z hX hY hZ
  simp only [positiveScaling_inner] at hD'
  rw [mvfderiv_conformal_inner g ((hF x).mdifferentiableAt (by simp)) hY hZ,
    mvfderiv_conformal_inner g ((hF x).mdifferentiableAt (by simp)) hZ hX,
    mvfderiv_conformal_inner g ((hF x).mdifferentiableAt (by simp)) hX hY] at hD'
  simp only [X, Z, FiberBundle.extend_apply_self] at hD hD'
  simp only [map_sub, map_add, map_smul, sub_apply,
    add_apply, smul_apply, smul_eq_mul,
    D.inner_gradient]
  rw [g.symm x w v] at hD'
  have hscaled := congrArg (fun t : ℝ => Real.exp (-2 * F x) * t) hD
  apply mul_left_cancel₀ (Real.exp_ne_zero (-2 * F x))
  nlinarith only [hD', hscaled]

private theorem mvfderiv_inner_of_connection_zero
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {X Y : (y : M) → TangentSpace (𝓡 n) y} {x : M}
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x)
    (hDX : D.connection X x = 0) (hDY : D.connection Y x = 0)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => g.inner y (X y) (Y y)) x v = 0 := by
  have h := D.normalization_mvfderiv_inner (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    X Y hX hY
  simpa only [FiberBundle.extend_apply_self, hDX, hDY, zero_apply,
    map_zero, add_zero] using h

private theorem mvfderiv_directional_of_connection_zero
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {F : M → ℝ} {Y : (y : M) → TangentSpace (𝓡 n) y} {x : M}
    (hF : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ F x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x) (hDY : D.connection Y x = 0) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) F y (Y y)) x v =
      D.hessian F x v (Y x) := by
  have h := D.hessianOnFields_eq_inner_connection_gradient hF
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) hY
  simp only [LeviCivitaData.hessianOnFields, FiberBundle.extend_apply_self,
    hDY, zero_apply, map_zero, sub_zero] at h
  rw [D.hessian_eq_inner_connection_gradient hF]
  exact h

section Conformal

variable (g : RiemannianMetric n M) (D : LeviCivitaData g)
  (F : M → ℝ) (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F)
  (D' : LeviCivitaData (positiveScaling g (fun y => Real.exp (-2 * F y))
    (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)))

private theorem conformal_connection_pairing_self
    {Y : (y : M) → TangentSpace (𝓡 n) y} {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x) (v : TangentSpace (𝓡 n) x) :
    g.inner x (D'.connection Y x v) v = g.inner x (D.connection Y x v) v -
      mvfderiv (𝓡 n) F x (Y x) * g.inner x v v := by
  rw [connection_positiveScaling_exp g D F hF D' hY]
  simp only [map_sub, map_add, map_smul, sub_apply,
    add_apply, smul_apply, smul_eq_mul,
    D.inner_gradient]
  rw [g.symm x (Y x) v]
  ring

private theorem conformal_connection_pairing_diagonal
    {Y : (y : M) → TangentSpace (𝓡 n) y} {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x) (v : TangentSpace (𝓡 n) x) :
    g.inner x (D'.connection Y x (Y x)) v =
      g.inner x (D.connection Y x (Y x)) v -
        2 * mvfderiv (𝓡 n) F x (Y x) * g.inner x (Y x) v +
        g.inner x (Y x) (Y x) * mvfderiv (𝓡 n) F x v := by
  rw [connection_positiveScaling_exp g D F hF D' hY]
  simp only [map_sub, map_add, map_smul, sub_apply,
    add_apply, smul_apply, smul_eq_mul,
    D.inner_gradient]
  ring

set_option backward.isDefEq.respectTransparency false in


private theorem conformal_curvature_normal_fields
    {U : Set M} (hU : IsOpen U)
    {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    {x : M} (hx : x ∈ U) (hDX : D.connection X x = 0)
    (hDY : D.connection Y x = 0)
    (hXX : g.inner x (X x) (X x) = 1) (hYY : g.inner x (Y x) (Y x) = 1)
    (hXY : g.inner x (X x) (Y x) = 0) :
    g.inner x (D'.curvatureOnFields X Y Y x) (X x) =
      g.inner x (D.curvatureOnFields X Y Y x) (X x) +
        D.hessian F x (X x) (X x) + D.hessian F x (Y x) (Y x) +
        (mvfderiv (𝓡 n) F x (X x)) ^ 2 + (mvfderiv (𝓡 n) F x (Y x)) ^ 2 -
        g.inner x (D.gradient F x) (D.gradient F x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hXd := (hX.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hYd := (hY.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hYX : g.inner x (Y x) (X x) = 0 := by rw [g.symm, hXY]
  let a : M → ℝ := fun y => mvfderiv (𝓡 n) F y (X y)
  let b : M → ℝ := fun y => mvfderiv (𝓡 n) F y (Y y)
  let W := fun y => D'.connection Y y (Y y)
  let V := fun y => D'.connection Y y (X y)
  let W₀ := fun y => D.connection Y y (Y y)
  let V₀ := fun y => D.connection Y y (X y)
  have hW := D'.normalization_contMDiffOn_connection_apply hU Y Y hY hY
  have hV := D'.normalization_contMDiffOn_connection_apply hU X Y hX hY
  have hW₀ := D.normalization_contMDiffOn_connection_apply hU Y Y hY hY
  have hV₀ := D.normalization_contMDiffOn_connection_apply hU X Y hX hY
  have hWd := (hW.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hVd := (hV.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hW₀d := (hW₀.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hV₀d := (hV₀.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have had : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) a x := by
    have h : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun y => g.inner y (D.gradient F y) (X y)) x :=
      ((D.contMDiff_gradient hF x).mdifferentiableAt (by simp)).inner_bundle hXd
    simpa only [a, D.inner_gradient] using h
  have hbd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) b x := by
    have h : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun y => g.inner y (D.gradient F y) (Y y)) x :=
      ((D.contMDiff_gradient hF x).mdifferentiableAt (by simp)).inner_bundle hYd
    simpa only [b, D.inner_gradient] using h
  have hp₀d : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => g.inner y (W₀ y) (X y)) x := hW₀d.inner_bundle hXd
  have hq₀d : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => g.inner y (V₀ y) (X y)) x := hV₀d.inner_bundle hXd
  have hxxd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => g.inner y (X y) (X y)) x := hXd.inner_bundle hXd
  have hyxd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => g.inner y (Y y) (X y)) x := hYd.inner_bundle hXd
  have hyyd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => g.inner y (Y y) (Y y)) x := hYd.inner_bundle hYd
  have hxx (v : TangentSpace (𝓡 n) x) :=
    mvfderiv_inner_of_connection_zero D hXd hXd hDX hDX v
  have hyx (v : TangentSpace (𝓡 n) x) :=
    mvfderiv_inner_of_connection_zero D hYd hXd hDY hDX v
  have hyy (v : TangentSpace (𝓡 n) x) :=
    mvfderiv_inner_of_connection_zero D hYd hYd hDY hDY v
  have ha : mvfderiv (𝓡 n) a x (X x) = D.hessian F x (X x) (X x) :=
    mvfderiv_directional_of_connection_zero D (hF x) hXd hDX (X x)
  have hb : mvfderiv (𝓡 n) b x (Y x) = D.hessian F x (Y x) (Y x) :=
    mvfderiv_directional_of_connection_zero D (hF x) hYd hDY (Y x)
  have hp : (fun y => g.inner y (W y) (X y)) =ᶠ[𝓝 x]
      (fun y => g.inner y (W₀ y) (X y) -
        2 * b y * g.inner y (Y y) (X y) + g.inner y (Y y) (Y y) * a y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact conformal_connection_pairing_diagonal g D F hF D'
      ((hY.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)) (X y)
  have hq : (fun y => g.inner y (V y) (X y)) =ᶠ[𝓝 x]
      (fun y => g.inner y (V₀ y) (X y) - b y * g.inner y (X y) (X y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact conformal_connection_pairing_self g D F hF D'
      ((hY.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)) (X y)
  have hp' : mvfderiv (𝓡 n) (fun y => g.inner y (W y) (X y)) x (X x) =
      mvfderiv (𝓡 n) (fun y => g.inner y (W₀ y) (X y)) x (X x) +
        D.hessian F x (X x) (X x) := by
    rw [show mvfderiv (𝓡 n) (fun y => g.inner y (W y) (X y)) x =
      mvfderiv (𝓡 n) (fun y => g.inner y (W₀ y) (X y) -
        2 * b y * g.inner y (Y y) (X y) + g.inner y (Y y) (Y y) * a y) x
      from hp.mfderiv_eq]
    erw [mvfderiv_fun_add (hp₀d.sub
      (((mdifferentiableAt_const (c := (2 : ℝ))).mul hbd).mul hyxd)) (hyyd.mul had),
      mvfderiv_fun_sub hp₀d
        (((mdifferentiableAt_const (c := (2 : ℝ))).mul hbd).mul hyxd),
      mvfderiv_fun_mul ((mdifferentiableAt_const (c := (2 : ℝ))).mul hbd) hyxd,
      mvfderiv_fun_mul hyyd had]
    simp only [add_apply, sub_apply,
      smul_apply, smul_eq_mul, hYX, hYY, hyx, hyy, ha]
    ring
  have hq' : mvfderiv (𝓡 n) (fun y => g.inner y (V y) (X y)) x (Y x) =
      mvfderiv (𝓡 n) (fun y => g.inner y (V₀ y) (X y)) x (Y x) -
        D.hessian F x (Y x) (Y x) := by
    rw [show mvfderiv (𝓡 n) (fun y => g.inner y (V y) (X y)) x =
      mvfderiv (𝓡 n) (fun y => g.inner y (V₀ y) (X y) -
        b y * g.inner y (X y) (X y)) x from hq.mfderiv_eq]
    erw [mvfderiv_fun_sub hq₀d (hbd.mul hxxd),
      mvfderiv_fun_mul hbd hxxd]
    simp only [sub_apply, add_apply,
      smul_apply, smul_eq_mul, hXX, hxx, hb]
    ring
  have hWval : W x = -(2 * b x) • Y x + D.gradient F x := by
    dsimp only [W]
    rw [connection_positiveScaling_exp g D F hF D' hYd, hDY, hYY]
    simp only [zero_apply, one_smul]
    change (0 : TangentSpace (𝓡 n) x) - b x • Y x - b x • Y x + _ = _
    module
  have hVval : V x = -(a x) • Y x - b x • X x := by
    dsimp only [V]
    rw [connection_positiveScaling_exp g D F hF D' hYd, hDY, hXY]
    simp only [zero_apply, zero_smul, add_zero, zero_sub,
      neg_smul, a, b]
  have hbracket : VectorField.mlieBracket (𝓡 n) X Y x = 0 := by
    rw [← D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero hXd hYd, hDX, hDY]
    simp
  have hDW := D.normalization_mvfderiv_inner X W X hWd hXd
  have hDV := D.normalization_mvfderiv_inner Y V X hVd hXd
  have hDW₀ := D.normalization_mvfderiv_inner X W₀ X hW₀d hXd
  have hDV₀ := D.normalization_mvfderiv_inner Y V₀ X hV₀d hXd
  simp only [hDX, zero_apply, map_zero, add_zero] at hDW hDV hDW₀ hDV₀
  have houterW : g.inner x (D'.connection W x (X x)) (X x) =
      g.inner x (D.connection W x (X x)) (X x) + 2 * (b x) ^ 2 -
        g.inner x (D.gradient F x) (D.gradient F x) := by
    rw [conformal_connection_pairing_self g D F hF D' (Y := W) hWd, hXX]
    erw [hWval]
    simp only [map_add, map_smul, smul_eq_mul]
    rw [← D.inner_gradient F x (D.gradient F x)]
    dsimp only [b]
    ring
  have houterV : g.inner x (D'.connection V x (Y x)) (X x) =
      g.inner x (D.connection V x (Y x)) (X x) + (b x) ^ 2 - (a x) ^ 2 := by
    rw [connection_positiveScaling_exp g D F hF D' (Y := V) hVd]
    simp only [map_sub, map_add, map_smul, sub_apply,
      add_apply, smul_apply, smul_eq_mul,
      D.inner_gradient, hYX, mul_zero, sub_zero]
    erw [hVval]
    simp only [map_sub, map_smul, sub_apply,
      smul_apply, smul_eq_mul, hYX, hYY, hXX]
    dsimp only [a, b]
    ring
  change g.inner x (D'.connection W x (X x) - D'.connection V x (Y x) -
    D'.connection Y x (VectorField.mlieBracket (𝓡 n) X Y x)) (X x) = _
  rw [hbracket, map_zero, sub_zero]
  simp only [map_sub, sub_apply]
  rw [houterW, houterV, ← hDW, ← hDV, hp', hq', hDW₀, hDV₀]
  simp only [LeviCivitaData.curvatureOnFields, hbracket, map_zero, sub_zero,
    map_sub, sub_apply]
  dsimp only [W₀, V₀, a, b]
  ring





theorem sectionalCurvature_positiveScaling_exp (x : M)
    (v w : TangentSpace (𝓡 n) x)
    (hvv : g.inner x v v = 1) (hww : g.inner x w w = 1)
    (hvw : g.inner x v w = 0) :
    D'.sectionalCurvature x v w = Real.exp (2 * F x) *
      (D.sectionalCurvature x v w + D.hessian F x v v + D.hessian F x w w +
        (mvfderiv (𝓡 n) F x v) ^ 2 + (mvfderiv (𝓡 n) F x w) ^ 2 -
        g.inner x (D.gradient F x) (D.gradient F x)) := by
  obtain ⟨U, X, hU, hxU, hX, hXx, hDX⟩ := RicciFlowAnalysis.exists_local_field_connection_zero D x v
  obtain ⟨V, Y, hV, hxV, hY, hYx, hDY⟩ := RicciFlowAnalysis.exists_local_field_connection_zero D x w
  have hXO := hX.mono (t := U ∩ V) inter_subset_left
  have hYO := hY.mono (t := U ∩ V) inter_subset_right
  have hxO : x ∈ U ∩ V := ⟨hxU, hxV⟩
  have hR := conformal_curvature_normal_fields g D F hF D' (hU.inter hV)
    hXO hYO hxO hDX hDY
    (by simpa only [hXx] using hvv) (by simpa only [hYx] using hww)
    (by simpa only [hXx, hYx] using hvw)
  rw [RicciFlowAnalysis.curvatureOnFields_eq_curvature D' (hU.inter hV) hXO hYO hYO hxO,
    RicciFlowAnalysis.curvatureOnFields_eq_curvature D (hU.inter hV) hXO hYO hYO hxO,
    hXx, hYx] at hR
  have he : Real.exp (-2 * F x) * Real.exp (2 * F x) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have he0 : Real.exp (-2 * F x) ≠ 0 := (Real.exp_pos _).ne'
  unfold LeviCivitaData.sectionalCurvature LeviCivitaData.curvatureTensor
  simp only [positiveScaling_inner, hvv, hww, hvw, mul_one, mul_zero,
    show (0 : ℝ) ^ 2 = 0 by norm_num,
    sub_zero, div_one]
  rw [hR]
  apply (div_eq_iff (mul_ne_zero he0 he0)).mpr
  calc
    _ = (Real.exp (-2 * F x) * Real.exp (2 * F x)) *
        (Real.exp (-2 * F x) *
          (g.inner x (D.curvature x v w w) v + D.hessian F x v v +
            D.hessian F x w w + (mvfderiv (𝓡 n) F x v) ^ 2 +
            (mvfderiv (𝓡 n) F x w) ^ 2 -
            g.inner x (D.gradient F x) (D.gradient F x))) := by rw [he, one_mul]
    _ = _ := by ring

end Conformal


end PoincareConjecture.MetricSurgery
