import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.RadialConnection










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

open ConnectionVariation Poincare.Riemannian.RadialTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]



def radialFrameConnection (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (T : E → E →L[ℝ] E) (x d : E) : E →L[ℝ] E :=
  (T x).inverse.comp (fderiv ℝ T x d + (Γ x d).comp (T x))

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem radialFrameConnection_apply
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTv : ∀ x v, T x v = field Γ v x) (x d v : E) :
    radialFrameConnection Γ T x d v =
      (T x).inverse (covariantDerivative Γ (field Γ v) x d) := by
  have hd := ((hT.differentiable (by simp)).differentiableAt.hasFDerivAt.clm_apply
    (hasFDerivAt_const v x)).fderiv
  have he : (fun y => T y v) = field Γ v := funext fun y => hTv y v
  rw [he] at hd
  have hv := congrArg (fun L => L d) hd
  simp only [ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] at hv
  simp only [radialFrameConnection, ContinuousLinearMap.comp_apply, add_apply,
    covariantDerivative, hv, hTv]

omit [FiniteDimensional ℝ E] in

theorem fderiv_inverse_transport_constant
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTi : ∀ x, (T x).IsInvertible) (x d w : E)
    (hpar : fderiv ℝ T x d = -(Γ x d).comp (T x)) :
    fderiv ℝ (fun y => (T y).inverse w) x d =
      (T x).inverse (Γ x d w) := by
  have h := fderiv_inverse_transport_apply (Γ := Γ) (q := id)
    (V := fun _ : E => w) (p := x) (d := d) (differentiableAt_const w)
    (hT.differentiable (by simp)).differentiableAt (hTi x)
    (by simpa only [id_eq, fderiv_id, ContinuousLinearMap.id_apply] using hpar)
  simpa only [covDerivAlong, fderiv_const_apply, zero_apply, fderiv_id,
    ContinuousLinearMap.id_apply, zero_add, id_eq] using h


theorem radial_field_self_of_geodesic_rays
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    (hgeo : ∀ x : E, ∀ t : ℝ, Γ (t • x) x x = 0) (x : E) :
    field Γ x x = x := by
  have hY := contDiff_field hΓ x
  have hYd (t : ℝ) : HasDerivAt (fun s : ℝ => field Γ x (s • x))
      (-(Γ (t • x) x (field Γ x (t • x)))) t := by
    have hd := (hY.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const x)
    have hp := covariantDerivative_field_radial_all hΓ x x t
    simpa only [Function.comp_def, id_eq, one_smul,
      eq_neg_of_add_eq_zero_left hp] using hd
  have hA : Continuous (fun t : ℝ => -(Γ (t • x) x)) :=
    ((hΓ.continuous.comp (continuous_id.smul continuous_const)).clm_apply
      continuous_const).neg
  have heq := Poincare.ODE.LocalFlow.linearODE_unique_on_Ioo
    (A := fun t : ℝ => -(Γ (t • x) x)) (a := -2) (b := 2) (h₀ := 0)
    (Z₂ := fun _ : ℝ => x) (by norm_num) hA.continuousOn
    (fun t _ => hYd t)
    (fun t _ => by simpa only [neg_apply, hgeo x t, neg_zero] using hasDerivAt_const t x)
    (by simp [field_zero hΓ]) (show (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
  simpa only [one_smul] using heq



theorem radial_coframe_euler_equation
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    (hsymm : ∀ x v w : E, Γ x v w = Γ x w v)
    (hgeo : ∀ x : E, ∀ t : ℝ, Γ (t • x) x x = 0)
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field Γ v x) (x w : E) :
    fderiv ℝ (fun y => (T y).inverse w) x x + (T x).inverse w =
      w + radialFrameConnection Γ T x w x := by
  have hrad (y : E) : T y y = y :=
    (hTv y y).trans (radial_field_self_of_geodesic_rays hΓ hgeo y)
  have hd := ((hT.differentiable (by simp)).differentiableAt.hasFDerivAt.clm_apply
    (hasFDerivAt_id x)).fderiv
  simp only [id_eq] at hd
  rw [show (fun y => T y y) = id from funext hrad, fderiv_id] at hd
  have hw := congrArg (fun L => L w) hd
  simp only [ContinuousLinearMap.id_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at hw
  have hw' := congrArg (T x).inverse hw
  simp only [map_add, (hTi x).inverse_apply_self] at hw'
  have hpar : fderiv ℝ T x x = -(Γ x x).comp (T x) := by
    simpa only [one_smul] using fderiv_radial_transport hΓ hT hTv x 1
  rw [fderiv_inverse_transport_constant hT hTi x x w hpar]
  simp only [radialFrameConnection, ContinuousLinearMap.comp_apply, add_apply,
    hrad, map_add]
  rw [hsymm x w x, hw']
  abel

omit [FiniteDimensional ℝ E] in
theorem contDiff_radialFrameConnection_apply
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTi : ∀ x, (T x).IsInvertible) :
    ContDiff ℝ ∞ (fun z : E × (E × E) =>
      radialFrameConnection Γ T z.1 z.2.1 z.2.2) := by
  have hInv : ContDiff ℝ ∞ (fun x => (T x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hTi x).contDiffAt_map_inverse.comp x hT.contDiffAt
  have hdT : ContDiff ℝ ∞ (fderiv ℝ T) := hT.fderiv_right (by simp)
  change ContDiff ℝ ∞ (fun z : E × (E × E) => (T z.1).inverse
    (fderiv ℝ T z.1 z.2.1 z.2.2 + Γ z.1 z.2.1 (T z.1 z.2.2)))
  exact (hInv.comp contDiff_fst).clm_apply
    (((hdT.comp contDiff_fst).clm_apply contDiff_snd.fst |>.clm_apply contDiff_snd.snd).add
      (((hΓ.comp contDiff_fst).clm_apply contDiff_snd.fst).clm_apply
        ((hT.comp contDiff_fst).clm_apply contDiff_snd.snd)))



theorem radial_coframe_eq_integral
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    (hsymm : ∀ x v w : E, Γ x v w = Γ x w v)
    (hgeo : ∀ x : E, ∀ t : ℝ, Γ (t • x) x x = 0)
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field Γ v x) (x w : E) :
    (T x).inverse w = w +
      ∫ t : ℝ in 0..1, radialFrameConnection Γ T (t • x) w (t • x) := by
  have hInv : ContDiff ℝ ∞ (fun y => (T y).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact (hTi y).contDiffAt_map_inverse.comp y hT.contDiffAt
  have hA : ContDiff ℝ ∞ (fun y => (T y).inverse w) :=
    hInv.clm_apply contDiff_const
  let F : ℝ → E := fun t => radialFrameConnection Γ T (t • x) w (t • x)
  have hF : Continuous F :=
    (contDiff_radialFrameConnection_apply hΓ hT hTi).continuous.comp
      ((continuous_id.smul continuous_const).prodMk
        (continuous_const.prodMk (continuous_id.smul continuous_const)))
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => s • (T (s • x)).inverse w)
      (w + F t) t := by
    have h := (hA.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const x)
    have hh := (hasDerivAt_id t).smul h
    have he := radial_coframe_euler_equation hΓ hsymm hgeo hT hTi hTv (t • x) w
    rw [map_smul] at he
    convert hh using 1
    · rfl
    · simpa only [id_eq, one_smul, Function.comp_def, F] using he.symm
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) ((continuous_const.add hF).intervalIntegrable (a := 0) (b := 1))
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (hF.intervalIntegrable (a := 0) (b := 1))] at hint
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul, zero_smul,
    F] using hint.symm

end PoincareConjecture.CoordinateExponential
