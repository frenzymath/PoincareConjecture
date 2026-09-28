import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.RadialFrameVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus









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


theorem fderiv_radial_transport
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTv : ∀ x v, T x v = field Γ v x) (x : E) (t : ℝ) :
    fderiv ℝ T (t • x) x = -(Γ (t • x) x).comp (T (t • x)) := by
  ext v
  have heq : (fun y => T y v) = field Γ v := funext fun y => hTv y v
  have hd := ((hT.differentiable (by simp)).differentiableAt.hasFDerivAt.clm_apply
    (hasFDerivAt_const v (t • x))).fderiv
  have hv := congrArg (fun L => L x) hd
  rw [heq] at hv
  have hp := covariantDerivative_field_radial_all hΓ v x t
  change fderiv ℝ (field Γ v) (t • x) x + Γ (t • x) x (field Γ v (t • x)) = 0 at hp
  simpa only [neg_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_zero, zero_apply, zero_add, hTv] using
    hv.symm.trans (eq_neg_of_add_eq_zero_left hp)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem fderiv_radial_parameter (x v : E) (t s : ℝ) :
    fderiv ℝ (fun z : E × ℝ => z.2 • z.1) (x, t) (v, s) = t • v + s • x := by
  rw [fderiv_fun_smul differentiableAt_snd differentiableAt_fst]
  rw [hasFDerivAt_fst.fderiv, hasFDerivAt_snd.fderiv]
  rfl



theorem radial_connection_eq_integral
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field Γ v x) (x v w : E) :
    (T x).inverse (covariantDerivative Γ (field Γ v) x w) =
      ∫ t : ℝ in 0..1, (T (t • x)).inverse
        (christoffelCurvature Γ (t • x) x (t • w) (field Γ v (t • x))) := by
  let q : E × ℝ → E := fun z => z.2 • z.1
  let V : E × ℝ → E := fun z => field Γ v (q z)
  let S : E × ℝ → E →L[ℝ] E := fun z => T (q z)
  let H : E × ℝ → E := fun z => (S z).inverse (covDerivAlong Γ q V (w, 0) z)
  have hq : ContDiff ℝ ∞ q := by dsimp [q]; fun_prop
  have hV : ContDiff ℝ ∞ V := (contDiff_field hΓ v).comp hq
  have hS : ContDiff ℝ ∞ S := hT.comp hq
  have hInv : ContDiff ℝ ∞ (fun z => (S z).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (hTi (q z)).contDiffAt_map_inverse.comp z hS.contDiffAt
  have hW : ContDiff ℝ ∞ (covDerivAlong Γ q V (w, 0)) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact contDiffAt_covDerivAlong hΓ.contDiffAt hq.contDiffAt hV.contDiffAt (w, 0)
  have hH : ContDiff ℝ ∞ H := hInv.clm_apply hW
  have hpar (t : ℝ) : fderiv ℝ S (x, t) (0, 1) =
      -(Γ (q (x, t)) (fderiv ℝ q (x, t) (0, 1))).comp (S (x, t)) := by
    rw [show S = T ∘ q from rfl,
      fderiv_comp (x, t) ((hT.differentiable (by simp)).differentiableAt)
        ((hq.differentiable (by simp)).differentiableAt)]
    simp only [ContinuousLinearMap.comp_apply, q, fderiv_radial_parameter,
      smul_zero, one_smul, zero_add]
    exact fderiv_radial_transport hΓ hT hTv x t
  let F : ℝ → E := fun t => (T (t • x)).inverse
    (christoffelCurvature Γ (t • x) x (t • w) (field Γ v (t • x)))
  have hd (t : ℝ) : HasDerivAt (fun s => H (x, s)) (F t) t := by
    have hv := fderiv_inverse_transport_variation hq.contDiffAt hV.contDiffAt
      hΓ.contDiffAt ((hS.differentiable (by simp)).differentiableAt)
      (hTi (q (x, t))) (0, 1) (w, 0) (hpar t)
      (Filter.Eventually.of_forall fun z => covDerivAlong_radial_field_time hΓ v z.1 z.2)
    have h := (hH.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
    apply h.congr_deriv
    simpa only [H, S, q, V, id_eq, fderiv_radial_parameter, smul_zero,
      one_smul, zero_add, zero_smul, add_zero, F] using hv
  have hF : Continuous F := by
    have hcurve : ContDiff ℝ ∞ (fun t : ℝ => H (x, t)) :=
      hH.comp (contDiff_const.prodMk contDiff_id)
    have heq : F = deriv (fun t : ℝ => H (x, t)) := funext fun t => (hd t).deriv.symm
    rw [heq]
    rw [show deriv (fun t : ℝ => H (x, t)) =
      (fun t => fderiv ℝ (fun s : ℝ => H (x, s)) t 1) from rfl]
    exact (hcurve.fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hF.intervalIntegrable (a := 0) (b := 1))
  have hendpoint (t : ℝ) : H (x, t) =
      (T (t • x)).inverse (t • covariantDerivative Γ (field Γ v) (t • x) w) := by
    change (T (t • x)).inverse
      (covDerivAlong Γ (fun z : E × ℝ => z.2 • z.1)
        (fun z => field Γ v (z.2 • z.1)) (w, 0) (x, t)) = _
    rw [covDerivAlong_radial_field_space hΓ]
  simpa only [hendpoint, one_smul, zero_smul, map_zero, sub_zero, F] using hint.symm




theorem exists_radial_transport_connection_integral
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ) :
    ∃ T : E → E →L[ℝ] E, ContDiff ℝ ∞ T ∧
      T 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ x v, T x v = field Γ v x) ∧
      (∀ x, (T x).IsInvertible) ∧
      ∀ x v w, (T x).inverse (covariantDerivative Γ (field Γ v) x w) =
        ∫ t : ℝ in 0..1, (T (t • x)).inverse
          (christoffelCurvature Γ (t • x) x (t • w) (field Γ v (t • x))) := by
  obtain ⟨T, hT, hT0, hTv, hTi, _⟩ := exists_radial_transport_operator hΓ
  exact ⟨T, hT, hT0, hTv, hTi, radial_connection_eq_integral hΓ hT hTi hTv⟩

end PoincareConjecture.CoordinateExponential
