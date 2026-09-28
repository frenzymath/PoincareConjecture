import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.ContinuousMap.Bounded.Normed









set_option autoImplicit false

open Asymptotics Filter Set
open scoped Topology ContDiff

namespace Poincare.Parabolic.Interior

variable {V F : Type*} [TopologicalSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem hasDerivAt_bcf_of_bounded_second_derivative
    (u du : ℝ → BoundedContinuousFunction V F) (ddu : ℝ → V → F)
    {K : ℝ} (hK : 0 ≤ K)
    (hu : ∀ t x, HasDerivAt (fun s => u s x) (du t x) t)
    (hdu : ∀ t x, HasDerivAt (fun s => du s x) (ddu t x) t)
    (hb : ∀ t x, ‖ddu t x‖ ≤ K) (t : ℝ) :
    HasDerivAt u (du t) t := by
  have hLip (s r : ℝ) (x : V) : ‖du s x - du r x‖ ≤ K * ‖s - r‖ := by
    exact (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun q _ => (hdu q x).hasDerivWithinAt) (fun q _ => hb q x) (mem_univ r) (mem_univ s)
  have hrem (s : ℝ) : ‖u s - u t - (s - t) • du t‖ ≤ K * ‖s - t‖ ^ 2 := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    change ‖u s x - u t x - (s - t) • du t x‖ ≤ _
    have hd (r : ℝ) : HasDerivAt
        (fun q => u q x - u t x - (q - t) • du t x) (du r x - du t x) r := by
      have h := ((hu r x).sub_const (u t x)).sub
        (((hasDerivAt_id r).sub_const t).smul_const (du t x))
      convert h using 1 <;> simp
      funext q
      rfl
    have h := (convex_segment t s).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r _ => (hd r).hasDerivWithinAt)
      (fun r hr => (hLip r t x).trans (mul_le_mul_of_nonneg_left
        (norm_sub_le_of_mem_segment hr) hK))
      (left_mem_segment ℝ t s) (right_mem_segment ℝ t s)
    simpa [pow_two, mul_assoc] using h
  apply HasDerivAt.of_isLittleO
  have hbig : (fun s => u s - u t - (s - t) • du t) =O[𝓝 t]
      (fun s => ‖s - t‖ ^ 2) := by
    apply IsBigO.of_bound K
    filter_upwards with s
    simpa only [norm_pow, norm_norm] using hrem s
  exact hbig.trans_isLittleO (isLittleO_pow_sub_sub t (by norm_num : 1 < (2 : ℕ)))

section CompactSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



noncomputable def compactSlice (f : E × ℝ → F) (hf : Continuous f)
    (hc : HasCompactSupport f) (t : ℝ) : BoundedContinuousFunction E F :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => f (x, t))
    (hf.comp (continuous_id.prodMk continuous_const))
    (hc.exists_bound_of_continuous hf).choose
    (fun x => (hc.exists_bound_of_continuous hf).choose_spec (x, t))

omit [NormedSpace ℝ F] [NormedSpace ℝ E] in
@[simp]
theorem compactSlice_apply (f : E × ℝ → F) (hf : Continuous f)
    (hc : HasCompactSupport f) (t : ℝ) (x : E) :
    compactSlice f hf hc t x = f (x, t) := rfl


noncomputable def timeDerivative (f : E × ℝ → F) (p : E × ℝ) : F :=
  fderiv ℝ f p (0, 1)

theorem contDiff_timeDerivative {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (timeDerivative f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_timeDerivative {f : E × ℝ → F}
    (hf : HasCompactSupport f) : HasCompactSupport (timeDerivative f) :=
  hf.fderiv_apply ℝ (0, 1)

theorem hasDerivAt_timeSlice {f : E × ℝ → F} (hf : Differentiable ℝ f)
    (x : E) (t : ℝ) :
    HasDerivAt (fun s => f (x, s)) (timeDerivative f (x, t)) t := by
  exact (hf (x, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))




theorem hasDerivAt_compactSlice {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (t : ℝ) :
    HasDerivAt (compactSlice f hf.continuous hc)
      (compactSlice (timeDerivative f) (contDiff_timeDerivative hf).continuous
        (hasCompactSupport_timeDerivative hc) t) t := by
  have hdt := contDiff_timeDerivative hf
  have hdtt := contDiff_timeDerivative hdt
  have hct := hasCompactSupport_timeDerivative hc
  obtain ⟨K, hK⟩ := (hasCompactSupport_timeDerivative hct).exists_bound_of_continuous
    hdtt.continuous
  apply hasDerivAt_bcf_of_bounded_second_derivative
    (ddu := fun s x => timeDerivative (timeDerivative f) (x, s))
    (hK := le_max_left 0 K)
  · intro s x
    exact hasDerivAt_timeSlice (hf.differentiable (by simp)) x s
  · intro s x
    exact hasDerivAt_timeSlice (hdt.differentiable (by simp)) x s
  · intro s x
    exact (hK (x, s)).trans (le_max_right 0 K)

theorem continuous_compactSlice {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : Continuous (compactSlice f hf.continuous hc) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_compactSlice hf hc t).continuousAt


noncomputable def spatialDerivative (f : E × ℝ → F) (p : E × ℝ) : E →L[ℝ] F :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)

theorem contDiff_spatialDerivative {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (spatialDerivative f) := by
  exact (hf.fderiv_right (by simp)).clm_comp contDiff_const

theorem hasCompactSupport_spatialDerivative {f : E × ℝ → F}
    (hf : HasCompactSupport f) : HasCompactSupport (spatialDerivative f) := by
  exact (hf.fderiv ℝ).comp_left (g := fun L => L.comp (ContinuousLinearMap.inl ℝ E ℝ))
    (by ext; simp)

theorem hasFDerivAt_spatialSlice {f : E × ℝ → F} (hf : Differentiable ℝ f)
    (x : E) (t : ℝ) :
    HasFDerivAt (fun y => f (y, t)) (spatialDerivative f (x, t)) x := by
  exact (hf (x, t)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)

theorem fderiv_spatialSlice {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (x : E) (t : ℝ) :
    fderiv ℝ (fun y => f (y, t)) x = spatialDerivative f (x, t) :=
  (hasFDerivAt_spatialSlice (hf.differentiable (by simp)) x t).fderiv

theorem fderiv_fderiv_spatialSlice {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (x : E) (t : ℝ) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, t)) y) x =
      spatialDerivative (spatialDerivative f) (x, t) := by
  simp only [fderiv_spatialSlice hf]
  exact fderiv_spatialSlice (contDiff_spatialDerivative hf) x t

end CompactSupport

end Poincare.Parabolic.Interior
