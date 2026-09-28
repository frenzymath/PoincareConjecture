import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TransportVariation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Radial

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

open ConnectionVariation Poincare.Riemannian.RadialTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem fderiv_radial_map (x : E) (t : ℝ) (v : E) (s : ℝ) :
    fderiv ℝ (fun z : E × ℝ => z.2 • z.1) (x, t) (v, s) = t • v + s • x := by
  rw [fderiv_fun_smul differentiableAt_snd differentiableAt_fst]
  rw [hasFDerivAt_fst.fderiv, hasFDerivAt_snd.fderiv]
  rfl

theorem covDerivAlong_radial_field_time
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    (v x : E) (t : ℝ) :
    covDerivAlong Γ (fun z : E × ℝ => z.2 • z.1)
      (fun z => field Γ v (z.2 • z.1)) (0, 1) (x, t) = 0 := by
  have hq : DifferentiableAt ℝ (fun z : E × ℝ => z.2 • z.1) (x, t) := by fun_prop
  have hY := (contDiff_field hΓ v).differentiable (by simp)
  rw [covDerivAlong, fderiv_fun_comp (x, t) hY.differentiableAt hq]
  simp only [ContinuousLinearMap.comp_apply, fderiv_radial_map, smul_zero,
    one_smul, zero_add]
  exact covariantDerivative_field_radial_all hΓ v x t

theorem covDerivAlong_radial_field_space
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    (v x w : E) (t : ℝ) :
    covDerivAlong Γ (fun z : E × ℝ => z.2 • z.1)
      (fun z => field Γ v (z.2 • z.1)) (w, 0) (x, t) =
      t • covariantDerivative Γ (field Γ v) (t • x) w := by
  have hq : DifferentiableAt ℝ (fun z : E × ℝ => z.2 • z.1) (x, t) := by fun_prop
  have hY := (contDiff_field hΓ v).differentiable (by simp)
  rw [covDerivAlong, fderiv_fun_comp (x, t) hY.differentiableAt hq]
  simp only [ContinuousLinearMap.comp_apply, fderiv_radial_map, zero_smul,
    add_zero, map_smul, smul_apply, covariantDerivative, smul_add]

theorem covDerivAlong_variation_radial_field
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    (v x w : E) (t : ℝ) :
    covDerivAlong Γ (fun z : E × ℝ => z.2 • z.1)
      (covDerivAlong Γ (fun z : E × ℝ => z.2 • z.1)
        (fun z => field Γ v (z.2 • z.1)) (w, 0)) (0, 1) (x, t) =
      christoffelCurvature Γ (t • x) x (t • w) (field Γ v (t • x)) := by
  have hq : ContDiff ℝ ∞ (fun z : E × ℝ => z.2 • z.1) := by fun_prop
  have hV := (contDiff_field hΓ v).comp hq
  have h := covDerivAlong_variation_of_parallel (p := (x, t))
    (hq.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hV.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hΓ.differentiable (by simp)).differentiableAt (0, 1) (w, 0)
    (Filter.Eventually.of_forall fun z => covDerivAlong_radial_field_time hΓ v z.1 z.2)
  simpa only [fderiv_radial_map, smul_zero, one_smul, zero_add, zero_smul,
    add_zero, Function.comp_def] using h

theorem exists_radial_transport_operator
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ) :
    ∃ T : E → E →L[ℝ] E, ContDiff ℝ ∞ T ∧
      T 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ x v, T x v = field Γ v x) ∧
      (∀ x, (T x).IsInvertible) ∧
      ∀ x, fderiv ℝ T x x = -(Γ x x).comp (T x) := by
  let Γ' : E → E →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    fun x => (ContinuousLinearMap.compL ℝ E E E).comp (Γ x)
  have hΓ' : ContDiff ℝ ∞ Γ' := contDiff_const.clm_comp hΓ
  let T := field Γ' (ContinuousLinearMap.id ℝ E)
  have hT : ContDiff ℝ ∞ T := contDiff_field hΓ' _
  have hT0 : T 0 = ContinuousLinearMap.id ℝ E := field_zero hΓ' _
  have hA (x : E) : Continuous (fun t : ℝ => -(Γ (t • x) x)) :=
    ((hΓ.continuous.comp (continuous_id.smul continuous_const)).clm_apply
      continuous_const).neg
  have hTd (x : E) (t : ℝ) :
      HasDerivAt (fun s : ℝ => T (s • x)) (-(Γ (t • x) x).comp (T (t • x))) t := by
    have hd := (hT.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const x)
    have hp := covariantDerivative_field_radial_all hΓ' (ContinuousLinearMap.id ℝ E) x t
    have hv : fderiv ℝ T (t • x) x = -(Γ (t • x) x).comp (T (t • x)) := by
      exact eq_neg_of_add_eq_zero_left hp
    simpa only [Function.comp_def, id_eq, one_smul, hv] using hd
  have hTv (x v : E) : T x v = field Γ v x := by
    have hY := contDiff_field hΓ v
    have hYd (t : ℝ) : HasDerivAt (fun s : ℝ => field Γ v (s • x))
        (-(Γ (t • x) x (field Γ v (t • x)))) t := by
      have hd := (hY.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const x)
      have hp := covariantDerivative_field_radial_all hΓ v x t
      simpa only [Function.comp_def, id_eq, one_smul,
        eq_neg_of_add_eq_zero_left hp] using hd
    have heq := Poincare.ODE.LocalFlow.linearODE_unique_on_Ioo
      (A := fun t : ℝ => -(Γ (t • x) x)) (a := -2) (b := 2) (h₀ := 0)
      (by norm_num) (hA x).continuousOn
      (fun t _ => by simpa using (hTd x t).clm_apply (hasDerivAt_const t v))
      (fun t _ => hYd t) (by simp [hT0, field_zero hΓ])
      (show (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
    simpa only [one_smul] using heq
  have hTi (x : E) : (T x).IsInvertible := by
    have hinj : Function.Injective (T x) := by
      intro v w hvw
      have heq := Poincare.ODE.LocalFlow.linearODE_unique_on_Ioo
        (A := fun t : ℝ => -(Γ (t • x) x)) (a := -2) (b := 2) (h₀ := 1)
        (by norm_num) (hA x).continuousOn
        (fun t _ => by simpa using (hTd x t).clm_apply (hasDerivAt_const t v))
        (fun t _ => by simpa using (hTd x t).clm_apply (hasDerivAt_const t w))
        (by simpa only [one_smul] using hvw)
        (show (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
      simpa only [zero_smul, hT0, ContinuousLinearMap.id_apply] using heq
    let e := LinearEquiv.ofBijective (T x).toLinearMap
      ⟨hinj, (LinearMap.injective_iff_surjective (f := (T x).toLinearMap)).mp hinj⟩
    exact ⟨e.toContinuousLinearEquiv, rfl⟩
  refine ⟨T, hT, hT0, hTv, hTi, ?_⟩
  intro x
  have hp := covariantDerivative_field_radial_all hΓ' (ContinuousLinearMap.id ℝ E) x 1
  have hh := eq_neg_of_add_eq_zero_left hp
  ext v
  simpa only [T, Γ', ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    one_smul, hTv, neg_apply, map_neg] using congrArg (fun L => L v) hh

end PoincareConjecture.CoordinateExponential
