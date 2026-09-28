import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient







set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Bundle

namespace PoincareConjecture

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace RiemannianMetric


noncomputable def gradient (g : RiemannianMetric n M) (f : M → ℝ) (x : M) :
    TangentSpace (𝓡 n) x :=
  (g.inner x).inverse (mvfderiv (𝓡 n) f x)

theorem inner_gradient (g : RiemannianMetric n M) (f : M → ℝ) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    g.inner x (g.gradient f x) v = mvfderiv (𝓡 n) f x v := by
  have hi : mvfderiv (𝓡 n) f x = g.inner x (g.gradient f x) :=
    (g.inner_isInvertible x).inverse_apply_eq.mp
      (rfl : (g.inner x).inverse (mvfderiv (𝓡 n) f x) = g.gradient f x)
  exact (congrArg (fun q ↦ q v) hi).symm

theorem contMDiffAt_gradient (g : RiemannianMetric n M) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (g.gradient f)) x := by
  apply g.contMDiffAt_of_metricDual
  have heq (y : M) : g.inner y (g.gradient f y) = mvfderiv (𝓡 n) f y := by
    ext v
    exact g.inner_gradient f y v
  simp_rw [heq]
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  convert hf.mfderiv_const (m := ∞) (by simp) using 1
  funext y
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, mvfderiv,
    NormedSpace.fromTangentSpace]
  rfl

theorem contMDiff_gradient (g : RiemannianMetric n M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (g.gradient f)) :=
  fun x => g.contMDiffAt_gradient (hf x)

theorem contMDiff_inner_gradient (g : RiemannianMetric n M) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (g.gradient f x) (g.gradient h x)) := by
  intro x
  have hi := ((g.contMDiff x).clm_bundle_apply (g.contMDiffAt_gradient (hf x))).clm_bundle_apply
    (g.contMDiffAt_gradient (hh x))
  simpa using (contMDiffAt_totalSpace.mp hi).2

theorem continuous_tangentNorm_gradient (g : RiemannianMetric n M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (fun x => g.tangentNorm x (g.gradient f x)) :=
  (g.contMDiff_inner_gradient hf hf).continuous.sqrt

theorem gradient_eq_zero_iff_mfderiv_eq_zero (g : RiemannianMetric n M)
    (f : M → ℝ) (x : M) :
    g.gradient f x = 0 ↔ mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x = 0 := by
  constructor
  · intro h
    ext v
    have hi := g.inner_gradient f x v
    simpa [h, mvfderiv, NormedSpace.fromTangentSpace] using hi.symm
  · intro h
    simp [gradient, mvfderiv, h]

theorem tangentNorm_gradient_pos_iff (g : RiemannianMetric n M)
    (f : M → ℝ) (x : M) :
    0 < g.tangentNorm x (g.gradient f x) ↔
      mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change 0 < ‖g.gradient f x‖ ↔ _
  rw [norm_pos_iff, ne_eq, g.gradient_eq_zero_iff_mfderiv_eq_zero]

end RiemannianMetric

theorem LeviCivitaData.gradient_eq_metric_gradient {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : M → ℝ) : D.gradient f = g.gradient f := rfl

end PoincareConjecture
