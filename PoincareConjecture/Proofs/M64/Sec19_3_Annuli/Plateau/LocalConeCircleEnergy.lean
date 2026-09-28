import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeRectangle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64_circle_endpoint_distance_sq_le_energy
    (g : RiemannianMetric n M) {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
    (g.edist (gamma 0) (gamma x)).toReal ^ 2 ≤
      curvePeriod * ∫ t in Icc (0 : ℝ) curvePeriod,
        (g.tangentNorm (gamma t) (curveVelocity gamma t)) ^ 2 := by
  let speed := M04.pathSpeed g gamma
  have hc : Continuous speed := M04.continuous_pathSpeed g hgamma
  have hd := g.edist_le_pathELength_of_mem_Icc hgamma.contMDiffOn
    (show x ∈ Icc (0 : ℝ) x from ⟨hx.1, le_rfl⟩)
  rw [M04.pathELength_eq_ofReal_integral_pathSpeed g hgamma hx.1] at hd
  have hI : 0 ≤ ∫ t in (0 : ℝ)..x, speed t :=
    intervalIntegral.integral_nonneg hx.1 (fun t _ => M04.pathSpeed_nonneg g gamma t)
  have hreal : (g.edist (gamma 0) (gamma x)).toReal ≤ ∫ t in (0 : ℝ)..x, speed t :=
    ENNReal.toReal_le_of_le_ofReal hI hd
  have hsq : (g.edist (gamma 0) (gamma x)).toReal ^ 2 ≤
      (∫ t in (0 : ℝ)..x, speed t) ^ 2 := by
    nlinarith [mul_self_le_mul_self ENNReal.toReal_nonneg hreal]
  have hcs := SpectralHeatNative.integral_sq_le_time_mul_integral_sq hx.1
    (hc.intervalIntegrable 0 x) ((hc.pow 2).intervalIntegrable 0 x)
  have hsub : (∫ t in (0 : ℝ)..x, speed t ^ 2) ≤
      ∫ t in Icc (0 : ℝ) curvePeriod, speed t ^ 2 := by
    rw [intervalIntegral.integral_of_le hx.1]
    exact setIntegral_mono_set ((hc.pow 2).integrableOn_Icc)
      (Eventually.of_forall fun t => sq_nonneg (speed t))
      (Eventually.of_forall fun t ht => ⟨ht.1.le, ht.2.trans hx.2⟩)
  have hE : 0 ≤ ∫ t in Icc (0 : ℝ) curvePeriod, speed t ^ 2 :=
    integral_nonneg fun t => sq_nonneg (speed t)
  change _ ≤ curvePeriod * ∫ t in Icc (0 : ℝ) curvePeriod, speed t ^ 2
  exact (hsq.trans hcs).trans
    ((mul_le_mul_of_nonneg_left hsub hx.1).trans
      (mul_le_mul_of_nonneg_right hx.2 hE))

theorem m64_periodic_circle_distance_sq_le_energy
    (g : RiemannianMetric n M) {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (x : ℝ) :
    (g.edist (gamma 0) (gamma x)).toReal ^ 2 ≤
      curvePeriod * ∫ t in Icc (0 : ℝ) curvePeriod,
        (g.tangentNorm (gamma t) (curveVelocity gamma t)) ^ 2 := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have heq : gamma (toIcoMod hP 0 x) = gamma x := by
    simpa only [toIcoMod, neg_smul, sub_eq_add_neg] using
      (hperiod.zsmul (-toIcoDiv hP 0 x)) x
  rw [← heq]
  exact m64_circle_endpoint_distance_sq_le_energy g hgamma
    (Ico_subset_Icc_self (toIcoMod_mem_Ico' hP x))

theorem m64_periodic_circle_speed
    (g : RiemannianMetric n M) {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) :
    Function.Periodic (fun t => g.tangentNorm (gamma t) (curveVelocity gamma t))
      curvePeriod := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro t
  let a : ℝ → ℝ := fun s => s + curvePeriod
  have ha : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a t :=
    ((contDiff_id.add contDiff_const).contDiffAt : ContDiffAt ℝ ∞ a t).contMDiffAt
      |>.mdifferentiableAt (by simp)
  have hda : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a t (1 : ℝ) = 1 := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using!
      ((hasDerivAt_id t).add_const curvePeriod).deriv
  have heq : gamma ∘ a = gamma := funext hperiod
  have ht := tangentMap_comp_at (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓡 n)
    (f := a) (g := gamma) (⟨t, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)
    (hgamma.mdifferentiable one_ne_zero (a t)) ha
  rw [heq] at ht
  have hinput : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a ⟨t, 1⟩ =
      (⟨t + curvePeriod, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) := by
    change (⟨t + curvePeriod, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a t 1⟩ :
      TangentBundle 𝓘(ℝ, ℝ) ℝ) = _
    erw [hda]
  rw [hinput] at ht
  exact (congrArg (fun v : TangentBundle (𝓡 n) M => ‖v.2‖) ht).symm

theorem m64_circle_energy_polar_interval
    (g : RiemannianMetric n M) {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) :
    (∫ t in Ioo (-Real.pi) Real.pi,
      (g.tangentNorm (gamma t) (curveVelocity gamma t)) ^ 2) =
      ∫ t in Icc (0 : ℝ) curvePeriod,
        (g.tangentNorm (gamma t) (curveVelocity gamma t)) ^ 2 := by
  have hp : Function.Periodic
      (fun t => (g.tangentNorm (gamma t) (curveVelocity gamma t)) ^ 2) curvePeriod :=
    fun t => congrArg (fun x : ℝ => x ^ 2) (m64_periodic_circle_speed g hgamma hperiod t)
  have h := hp.intervalIntegral_add_eq (-Real.pi) 0
  have hends : -Real.pi + curvePeriod = Real.pi := by unfold curvePeriod; ring
  rw [hends, zero_add] at h
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le
      (by unfold curvePeriod; positivity), ← integral_Icc_eq_integral_Ioc] at h
  exact h

end PoincareConjecture
