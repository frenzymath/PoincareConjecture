import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereCollarCorrection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FixedSphereBallPreservation
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology Pointwise InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

noncomputable def surgeryMatchingRadius (c a r : ℝ) : ℝ :=
  c + a * (r ^ 2 - 1) / (1 + r ^ 2)

theorem surgeryMatchingRadius_contDiff (c a : ℝ) :
    ContDiff ℝ ∞ (surgeryMatchingRadius c a) := by
  exact contDiff_const.add ((contDiff_const.mul ((contDiff_id.pow 2).sub contDiff_const)).div
    (contDiff_const.add (contDiff_id.pow 2)) (fun r => ne_of_gt (by positivity)))

@[simp] theorem surgeryMatchingRadius_one (c a : ℝ) : surgeryMatchingRadius c a 1 = c := by
  simp [surgeryMatchingRadius]

theorem surgeryMatchingRadius_hasDerivAt_one (c a : ℝ) :
    HasDerivAt (surgeryMatchingRadius c a) a 1 := by
  have hp : HasDerivAt (fun r : ℝ => r ^ 2) 2 1 := by
    simpa using hasDerivAt_pow 2 (1 : ℝ)
  have hN : HasDerivAt (fun r : ℝ => a * (r ^ 2 - 1)) (a * 2) 1 :=
    (hp.sub_const 1).const_mul a
  have hD : HasDerivAt (fun r : ℝ => 1 + r ^ 2) 2 1 := hp.const_add 1
  have hd := (hN.div hD (by norm_num)).const_add c
  change HasDerivAt (surgeryMatchingRadius c a)
    ((a * 2 * (1 + 1 ^ 2) - (a * (1 ^ 2 - 1)) * 2) / (1 + 1 ^ 2) ^ 2) 1 at hd
  have hv : (a * 2 * (1 + 1 ^ 2) - (a * (1 ^ 2 - 1)) * 2) / (1 + 1 ^ 2) ^ 2 = a := by
    ring
  rwa [hv] at hd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def surgeryMatchingCollar (c a : ℝ) (x : E) : E :=
  (surgeryMatchingRadius c a ‖x‖ / c) • NormedSpace.normalize x

theorem surgeryMatchingCollar_contDiffOn (c a : ℝ) :
    ContDiffOn ℝ ∞ (surgeryMatchingCollar (E := E) c a) ({0}ᶜ : Set E) := by
  intro x hx
  have hn : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) x :=
    contDiffAt_norm ℝ (show x ≠ 0 from hx)
  exact (((surgeryMatchingRadius_contDiff c a).contDiffAt.comp x hn).div_const c).smul
    (hn.inv (norm_ne_zero_iff.mpr hx) |>.smul contDiffAt_id) |>.contDiffWithinAt

theorem surgeryMatchingCollar_fixed {c : ℝ} (hc : c ≠ 0) (a : ℝ)
    {x : E} (hx : ‖x‖ = 1) : surgeryMatchingCollar c a x = x := by
  rw [surgeryMatchingCollar, hx, surgeryMatchingRadius_one, div_self hc,
    one_smul, NormedSpace.normalize_eq_self_of_norm_eq_one hx]

theorem surgeryMatchingCollar_fderiv_normal (c a : ℝ)
    {x : E} (hx : ‖x‖ = 1) :
    fderiv ℝ (surgeryMatchingCollar c a) x x = (a / c) • x := by
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; exact one_ne_zero)
  have hm : DifferentiableAt ℝ (surgeryMatchingCollar c a) x :=
    ((surgeryMatchingCollar_contDiffOn c a).contDiffAt
      (isClosed_singleton.isOpen_compl.mem_nhds hx0)).differentiableAt (by simp)
  have hray : HasDerivAt (fun r : ℝ => r • x) x 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hF : HasFDerivAt (surgeryMatchingCollar c a)
      (fderiv ℝ (surgeryMatchingCollar c a) x) ((1 : ℝ) • x) := by
    simpa only [one_smul] using hm.hasFDerivAt
  have hd : HasDerivAt (fun r : ℝ => surgeryMatchingCollar c a (r • x))
      (fderiv ℝ (surgeryMatchingCollar c a) x x) 1 := by
    simpa only [Function.comp_def, one_smul] using
      hF.comp_hasDerivAt 1 hray
  have heq : (fun r : ℝ => surgeryMatchingCollar c a (r • x)) =ᶠ[𝓝 1]
      (fun r => (surgeryMatchingRadius c a r / c) • x) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with r hr
    simp only [surgeryMatchingCollar, norm_smul, Real.norm_eq_abs, hx, mul_one,
      abs_of_pos (show 0 < r from hr),
      NormedSpace.normalize_smul_of_pos (show 0 < r from hr),
      NormedSpace.normalize_eq_self_of_norm_eq_one hx]
  exact hd.unique (((surgeryMatchingRadius_hasDerivAt_one c a).div_const c).smul_const x
    |>.congr_of_eventuallyEq heq)

variable [FiniteDimensional ℝ E]

theorem exists_surgery_matching_diffeomorph {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∃ R : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      R '' ball 0 1 = ball 0 c ∧ R '' closedBall 0 1 = closedBall 0 c ∧
      (∀ x ∈ sphere (0 : E) 1, R x = c • x) ∧
      ∀ᶠ x in 𝓝ˢ (sphere (0 : E) 1),
        R x = surgeryMatchingRadius c a ‖x‖ • NormedSpace.normalize x := by
  have hunit : sphere (0 : E) 1 ⊆ ({0}ᶜ : Set E) := by
    intro x hx
    exact ne_zero_of_mem_unit_sphere ⟨x, hx⟩
  have hn (x : E) (hx : x ∈ sphere 0 1) :
      0 < ⟪x, fderiv ℝ (surgeryMatchingCollar c a) x x⟫_ℝ := by
    rw [surgeryMatchingCollar_fderiv_normal c a (mem_sphere_zero_iff_norm.mp hx),
      inner_smul_right, real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp hx,
      one_pow, mul_one]
    exact div_pos ha hc
  obtain ⟨Φ, hΦ, hzero, hfix, hnear, _⟩ := exists_sphere_collar_correction
    (surgeryMatchingCollar c a) isClosed_singleton.isOpen_compl hunit
    (surgeryMatchingCollar_contDiffOn c a)
    (fun _ hx => surgeryMatchingCollar_fixed hc.ne' a (mem_sphere_zero_iff_norm.mp hx)) hn
  have hballs := fixedSphere_isotopy_image_balls (fun t => (Φ t).toHomeomorph)
    (fun x => (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn)
    hzero (fun t ht x hx => hfix t ht x (mem_sphere_zero_iff_norm.mpr hx))
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  change Φ 1 '' ball 0 1 = ball 0 1 ∧
    Φ 1 '' closedBall 0 1 = closedBall 0 1 at hballs
  let S : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ := {
    toEquiv := (Homeomorph.smulOfNeZero c hc.ne').toEquiv
    contMDiff_toFun := (contDiff_const.smul contDiff_id).contMDiff
    contMDiff_invFun := (contDiff_const.smul contDiff_id).contMDiff }
  refine ⟨(Φ 1).trans S, ?_, ?_, ?_, ?_⟩
  · change (fun x => c • Φ 1 x) '' ball 0 1 = _
    rw [← image_image (fun x : E => c • x), hballs.1]
    change c • ball (0 : E) 1 = ball 0 c
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hc, mul_one] using
      smul_ball hc.ne' (0 : E) 1
  · change (fun x => c • Φ 1 x) '' closedBall 0 1 = _
    rw [← image_image (fun x : E => c • x), hballs.2]
    change c • closedBall (0 : E) 1 = closedBall 0 c
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hc, mul_one] using
      smul_closedBall' hc.ne' (0 : E) 1
  · intro x hx
    change c • Φ 1 x = c • x
    rw [hfix 1 (by norm_num) x hx]
  · filter_upwards [hnear] with x hx
    change c • Φ 1 x = _
    rw [hx, surgeryMatchingCollar, smul_smul]
    congr 1
    field_simp [hc.ne']

end PoincareConjecture.M25.Topology3D
