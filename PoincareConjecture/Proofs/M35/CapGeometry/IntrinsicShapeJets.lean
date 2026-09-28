import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicShapeDerivative
import PoincareConjecture.Proofs.M35.CapGeometry.VanishingMetricErrorJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

noncomputable section

local notation "V" => StandardCapSpace

local instance intrinsicShapeJetsDualNormedGroup : NormedAddCommGroup (V →L[ℝ] ℝ) :=
  inferInstance
local instance intrinsicShapeJetsDualNormedSpace : NormedSpace ℝ (V →L[ℝ] ℝ) :=
  inferInstance

theorem intrinsic_shape_derivative_jets_zero
    (g : ℕ → RiemannianMetric 3 V)
    (hrotation : ∀ k, ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : V,
        (g k).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (g k).inner x u v)
    (hcomplete : ∀ k, MetricComplete (g k)) (f : ℕ → V → V) (p : ℕ → V)
    (hdomain : ∀ᶠ k in atTop, ∀ᶠ y in 𝓝 (p k),
      ContDiffAt ℝ ∞ (f k) y ∧ (fderiv ℝ (f k) y).IsInvertible ∧ f k y ≠ 0)
    (hfield : ∀ r : ℕ, HasUniformJetBoundsAt r
      (fun k => pullback ℝ (f k) (radialUnitField (g k))) p)
    (hshape : ∀ r : ℕ, Tendsto (fun k => iteratedFDeriv ℝ r
      (fun y => axisWarpingSlope (g k) ‖f k y‖ / axisWarpingRadius (g k) ‖f k y‖)
        (p k)) atTop (𝓝 0)) :
    ∀ m r : ℕ, Tendsto (fun k => iteratedFDeriv ℝ r
      (intrinsicShapeDerivativePullback (g k) (hrotation k) (hcomplete k) (f k) m)
        (p k)) atTop (𝓝 0) := by
  let S k m := intrinsicShapeDerivativePullback (g k) (hrotation k) (hcomplete k) (f k) m
  let Z k := pullback ℝ (f k) (radialUnitField (g k))
  have hS (m : ℕ) : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (S k m) (p k) := by
    filter_upwards [hdomain] with k hk
    exact intrinsicShapeDerivativePullback_contDiffAt (g k) (hrotation k) (hcomplete k)
      hk.self_of_nhds.1 hk.self_of_nhds.2.2 m
  have hZ : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (Z k) (p k) := by
    filter_upwards [hdomain] with k hk
    exact euclidean_radial_pullback_contDiffAt (g k) hk.self_of_nhds.1
      hk.self_of_nhds.2.1 hk.self_of_nhds.2.2
  intro m
  induction m with
  | zero =>
    intro r
    apply (hshape r).congr'
    filter_upwards [hdomain] with k hk
    have heq : S k 0 =ᶠ[𝓝 (p k)]
        (fun y => axisWarpingSlope (g k) ‖f k y‖ / axisWarpingRadius (g k) ‖f k y‖) := by
      filter_upwards [hk] with y hy
      exact intrinsicShapeDerivativePullback_zero (g k) (hrotation k) (hcomplete k) hy.2.2
    exact ((heq.iteratedFDeriv ℝ r).self_of_nhds).symm
  | succ m hm =>
    intro r
    have hderiv (j : ℕ) : Tendsto
        (fun k => iteratedFDeriv ℝ j (fderiv ℝ (S k m)) (p k)) atTop (𝓝 0) := by
      let C := continuousMultilinearCurryRightEquiv' ℝ j V ℝ
      have hc (a : V → ℝ) (y : V) :
          iteratedFDeriv ℝ j (fderiv ℝ a) y = C (iteratedFDeriv ℝ (j + 1) a y) := by
        rw [iteratedFDeriv_succ_eq_comp_right]
        exact (C.apply_symm_apply _).symm
      simp_rw [hc]
      have h := (C.continuous.tendsto (0 : V [×(j + 1)]→L[ℝ] ℝ)).comp (hm (j + 1))
      simpa only [Function.comp_def, S, map_zero] using h
    have hz := jet_bilinear_tendsto_zero_of_bounded
      (ContinuousLinearMap.apply ℝ ℝ : V →L[ℝ] (V →L[ℝ] ℝ) →L[ℝ] ℝ).flip
      (fun j _ => hderiv j) (hfield r)
      ((hS m).mono fun _ h => h.fderiv_right (m := ∞) (by simp)) hZ
    apply hz.congr'
    filter_upwards [hdomain] with k hk
    have heq : S k (m + 1) =ᶠ[𝓝 (p k)]
        (fun y => fderiv ℝ (S k m) y (Z k y)) := by
      filter_upwards [hk] with y hy
      exact intrinsicShapeDerivativePullback_succ (g k) (hrotation k) (hcomplete k)
        (hy.1.differentiableAt (by simp)) hy.2.1 hy.2.2 m
    exact ((heq.iteratedFDeriv ℝ r).self_of_nhds).symm

end

end PoincareConjecture.M35.Uniqueness
