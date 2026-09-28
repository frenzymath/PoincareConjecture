import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Cutoff
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Operator
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Continuity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Weighted
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.WeakDerivative.Interval








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M}
  (D : LeviCivitaData g)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M)
  (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)

include hreg in
omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
private theorem levelQ_pos (x : M) (hx : x ∈ U) : 0 < D.levelQ f x := by
  have h := (g.tangentNorm_gradient_pos_iff f x).mpr (hreg x hx)
  exact Real.sqrt_pos.mp h

theorem integral_levelVariation_mul_test
    {h : M → ℝ} (hh : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ h)
    (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) :
    (∫ c, η c * ∫ z, D.levelVariation f h (openLevelIncl f U c z)
      ∂g.regularLevelVolume hf U hreg c) =
      -(∫ c, deriv η c * ∫ z, h (openLevelIncl f U c z)
        ∂g.regularLevelVolume hf U hreg c) := by
  let s := fun x => g.tangentNorm x (g.gradient f x)
  let φ := fun x => η (f x) * h x
  have hq (x : M) (hx : x ∈ tsupport h) : 0 < D.levelQ f x :=
    D.levelQ_pos U hreg x (hs hx)
  have hφ : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ φ :=
    (hη.contMDiff.comp hf).mul hh
  have hφs : tsupport φ ⊆ tsupport h := tsupport_mul_subset_right
  have hφc : HasCompactSupport φ := hc.mul_left
  have hp := D.contMDiff_levelVariation hf hh hq
  have hpc := D.hasCompactSupport_levelVariation (f := f) hc
  have hps := (D.tsupport_levelVariation_subset f h).trans hs
  have hi := D.integral_unitNormal_green hφ hf hφc (fun x hx => hq x (hφs hx))
  have heq (x : M) :
      φ x * D.levelMeanCurvature f x +
        g.inner x (D.gradient φ x) (D.gradient f x) / Real.sqrt (D.levelQ f x) =
      η (f x) * D.levelVariation f h x * s x + deriv η (f x) * h x * s x := by
    by_cases hx : x ∈ tsupport h
    · have hqx := hq x hx
      rw [D.levelVariation_eq_meanCurvature hf x hqx]
      rw [show φ = fun y => (η ∘ f) y * h y from rfl,
        D.gradient_mul ((hη.contMDiff.comp hf x).mdifferentiableAt (by simp))
          ((hh x).mdifferentiableAt (by simp)),
        D.gradient_comp ((hf x).mdifferentiableAt (by simp))
          (hη.differentiable (by simp) (f x))]
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
        Function.comp_apply]
      change _ = η (f x) * _ * Real.sqrt (D.levelQ f x) +
        deriv η (f x) * h x * Real.sqrt (D.levelQ f x)
      change η (f x) * h x * D.levelMeanCurvature f x +
        (η (f x) * g.inner x (D.gradient h x) (D.gradient f x) +
          h x * (deriv η (f x) * D.levelQ f x)) / Real.sqrt (D.levelQ f x) = _
      have hsqrt := Real.sq_sqrt hqx.le
      have hsne := (Real.sqrt_pos.2 hqx).ne'
      field_simp
      linear_combination -(η (f x) * g.inner x (D.gradient h x) (D.gradient f x) +
        h x * deriv η (f x) * D.levelQ f x) * hsqrt
    · rw [D.levelVariation_eq_zero_of_notMem_tsupport hx,
        D.gradient_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))]
      simp [φ, image_eq_zero_of_notMem_tsupport hx]
  simp_rw [heq] at hi
  have hsi := g.continuous_tangentNorm_gradient hf
  have hpi : Integrable (fun x => η (f x) * D.levelVariation f h x * s x)
      g.volumeMeasure :=
    (((hη.continuous.comp hf.continuous).mul hp.continuous).mul hsi).integrable_of_hasCompactSupport
      hpc.mul_left.mul_right
  have hhi : Integrable (fun x => deriv η (f x) * h x * s x) g.volumeMeasure :=
    ((((hη.continuous_deriv (by simp)).comp hf.continuous).mul hh.continuous).mul hsi).integrable_of_hasCompactSupport
      hc.mul_left.mul_right
  rw [integral_add hpi hhi] at hi
  rw [← g.integral_mul_comp_coarea hf U hreg hp.continuous hpc hps hη.continuous,
    ← g.integral_mul_comp_coarea hf U hreg hh.continuous hc hs
      (hη.continuous_deriv (by simp))]
  exact eq_neg_of_add_eq_zero_left hi


theorem hasDerivAt_regularLevelIntegral
    {h : M → ℝ} (hh : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ h)
    (hc : HasCompactSupport h) (hs : tsupport h ⊆ U) (t : ℝ) :
    HasDerivAt (fun c => ∫ z, h (openLevelIncl f U c z)
      ∂g.regularLevelVolume hf U hreg c)
      (∫ z, D.levelVariation f h (openLevelIncl f U t z)
        ∂g.regularLevelVolume hf U hreg t) t := by
  let p := fun c => ∫ z, D.levelVariation f h (openLevelIncl f U c z)
    ∂g.regularLevelVolume hf U hreg c
  let q := fun c => ∫ z, h (openLevelIncl f U c z)
    ∂g.regularLevelVolume hf U hreg c
  have hp : Continuous p := g.continuous_regularLevelIntegral hf U hreg
    (D.contMDiff_levelVariation hf hh (fun x hx => D.levelQ_pos U hreg x (hs hx))).continuous
    (D.hasCompactSupport_levelVariation hc) ((D.tsupport_levelVariation_subset f h).trans hs)
  have hq : Continuous q := g.continuous_regularLevelIntegral hf U hreg hh.continuous hc hs
  have heq : q =ᶠ[𝓝 t] fun x => (∫ c in t..x, p c) + q t := by
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo (t - 1) (t + 1) by constructor <;> linarith)]
      with x hx
    have hFTC := Poincare.Analysis.WeakDerivative.intervalIntegral_eq_sub_of_weakDerivative
      hp.continuousOn hq.continuousOn
      (fun η hη _ _ => D.integral_levelVariation_mul_test hf U hreg hh hc hs hη)
      (show t ∈ Ioo (t - 1) (t + 1) by constructor <;> linarith) hx
    exact (sub_eq_iff_eq_add.mp hFTC.symm)
  exact ((intervalIntegral.integral_hasDerivAt_right
    (hp.intervalIntegrable t t) (hp.stronglyMeasurableAtFilter _ _) hp.continuousAt).add_const
      (q t)).congr_of_eventuallyEq heq

include D in


theorem contDiff_regularLevelIntegral
    {h : M → ℝ} (hh : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ h)
    (hc : HasCompactSupport h) (hs : tsupport h ⊆ U) :
    ContDiff ℝ ∞ (fun c => ∫ z, h (openLevelIncl f U c z)
      ∂g.regularLevelVolume hf U hreg c) := by
  rw [contDiff_infty]
  intro k
  induction k generalizing h with
  | zero =>
      exact contDiff_zero.mpr (g.continuous_regularLevelIntegral hf U hreg hh.continuous hc hs)
  | succ k ih =>
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun t => (D.hasDerivAt_regularLevelIntegral hf U hreg hh hc hs t).differentiableAt,
        by simp, ?_⟩
      have hd : deriv (fun c => ∫ z, h (openLevelIncl f U c z)
          ∂g.regularLevelVolume hf U hreg c) =
          fun c => ∫ z, D.levelVariation f h (openLevelIncl f U c z)
            ∂g.regularLevelVolume hf U hreg c :=
        funext fun t => (D.hasDerivAt_regularLevelIntegral hf U hreg hh hc hs t).deriv
      rw [hd]
      exact ih (D.contMDiff_levelVariation hf hh
        (fun x hx => D.levelQ_pos U hreg x (hs hx)))
        (D.hasCompactSupport_levelVariation hc) ((D.tsupport_levelVariation_subset f h).trans hs)

end PoincareConjecture.LeviCivitaData
