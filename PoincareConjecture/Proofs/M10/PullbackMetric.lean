import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import PoincareConjecture.Proofs.M10.BilinearPerturbation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Bundle ContinuousLinearMap Filter Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

noncomputable def pullbackMetricForm (g : RiemannianMetric n M)
    (f : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  (g.inner (f x)).bilinearComp (mfderiv (𝓡 n) (𝓡 n) f x)
    (mfderiv (𝓡 n) (𝓡 n) f x)

set_option backward.isDefEq.respectTransparency false in

theorem continuousAt_mfderiv_apply_vector
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) 1 f x) (v : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt (fun y ↦ (⟨f y, mfderiv (𝓡 n) (𝓡 n) f y v⟩ :
      TangentBundle (𝓡 n) M)) x := by
  have hD := (hf.mfderiv_const (m := 0) (by simp)).continuousAt
  have hsection : Continuous
      (fun y : EuclideanSpace ℝ (Fin n) ↦
        (⟨y, v⟩ : TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n)))) :=
    (tangentBundleModelSpaceHomeomorph (𝓡 n)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  exact hD.clm_apply_of_inCoordinates hsection.continuousAt hf.continuousAt

set_option backward.isDefEq.respectTransparency false in

theorem pullbackMetricForm_continuousAt (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) 1 f x) :
    ContinuousAt (pullbackMetricForm g f) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  apply continuousAt_clm_apply.mpr
  intro v
  apply continuousAt_clm_apply.mpr
  intro w
  exact (continuousAt_mfderiv_apply_vector hf v).inner_bundle
    (continuousAt_mfderiv_apply_vector hf w)

set_option backward.isDefEq.respectTransparency false in

theorem eventually_pullback_tangentNorm_comparison (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) 1 f x)
    (hD : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 x, ∀ v : EuclideanSpace ℝ (Fin n),
      g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) / r ≤
          g.tangentNorm (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) ∧
      g.tangentNorm (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) ≤
          r * g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) (f x) :=
    LinearEquiv.toContinuousLinearEquiv
      (LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap hD)
  have hcenter : ∀ v, pullbackMetricForm g f x v v = ‖L v‖ ^ 2 := by
    intro v
    exact real_inner_self_eq_norm_sq (L v)
  have h := eventually_sqrt_bilinear_comparison
    (pullbackMetricForm_continuousAt g hf) L hcenter hr
  filter_upwards [h] with y hy
  intro v
  have hnorm : ‖L v‖ =
      g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) :=
    norm_eq_sqrt_real_inner (L v)
  have hvalue : Real.sqrt (pullbackMetricForm g f y v v) =
      g.tangentNorm (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) := rfl
  simpa only [hnorm, hvalue] using hy v

end PoincareConjecture.M10
