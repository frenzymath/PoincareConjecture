import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.OpenSubset
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiber

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle InnerProductSpace

namespace PoincareConjecture.RiemannianMetric

variable {m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
  [IsManifold (𝓡 (m + k)) ∞ M]
  {f : M → Fin k → ℝ}
  (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f) (U : Opens M)
  (hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x))
  (c : Fin k → ℝ)

local instance openFiber_ambient_finrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
  ⟨finrank_euclideanSpace_fin⟩

def openRegularFiberMetric (g : RiemannianMetric (m + k) M) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    RiemannianMetric m (openFiber f U c) := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  exact Induced.pullbackMetric g (openFiberIncl f U c)
    (contMDiff_openFiberIncl hf U hreg c) (injective_mfderiv_openFiberIncl hf U hreg c)

@[simp] theorem openRegularFiberMetric_inner (g : RiemannianMetric (m + k) M)
    (x : openFiber f U c) (v w : EuclideanSpace ℝ (Fin m)) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    (openRegularFiberMetric hf U hreg c g).inner x v w =
      g.inner (openFiberIncl f U c x)
        (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x v)
        (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x w) := rfl

theorem openRegularFiberMetric_tangentNorm (g : RiemannianMetric (m + k) M)
    (x : openFiber f U c) (v : EuclideanSpace ℝ (Fin m)) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    (openRegularFiberMetric hf U hreg c g).tangentNorm x v =
      g.tangentNorm (openFiberIncl f U c x)
        (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x v) := rfl

theorem metricComplete_openRegularFiberMetric [T3Space M]
    (g : RiemannianMetric (m + k) M) (hcomplete : MetricComplete g)
    (hclosed : IsClosed ((U : Set M) ∩ f ⁻¹' {c})) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    MetricComplete (openRegularFiberMetric hf U hreg c g) := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  apply metricComplete_of_isClosedEmbedding (openRegularFiberMetric hf U hreg c g) g
    (contMDiff_openFiberIncl hf U hreg c) ?_
    (openRegularFiberMetric_inner hf U hreg c g) hcomplete
  exact ⟨isEmbedding_openFiberIncl f U c, by rwa [range_openFiberIncl]⟩

theorem mfderiv_gradient_openRegularFiberMetric
    (g : RiemannianMetric (m + k) M) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ) (x : openFiber f U c) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace (𝓡 (m + k)) (openFiberIncl f U c x)) := by
      unfold TangentSpace
      infer_instance
    mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x
        ((openRegularFiberMetric hf U hreg c g).gradient (φ ∘ openFiberIncl f U c) x) =
      (Submodule.span ℝ (Set.range (fun i : Fin k =>
        g.gradient (fun y => f y i) (openFiberIncl f U c x))))ᗮ.starProjection
          (g.gradient φ (openFiberIncl f U c x)) := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (m + k)) (openFiberIncl f U c x)) := by
    unfold TangentSpace
    infer_instance
  have h := mfderiv_gradient_comp_eq_starProjection (openRegularFiberMetric hf U hreg c g) g
    ((contMDiff_openFiberIncl hf U hreg c x).mdifferentiableAt (by simp))
    ((hφ (openFiberIncl f U c x)).mdifferentiableAt (by simp))
    (openRegularFiberMetric_inner hf U hreg c g x)
  rw [range_mfderiv_openFiberIncl hf U hreg c x,
    ker_mfderiv_pi_eq_orthogonal_span_gradients g (fun i y => f y i)
      (contMDiff_pi_space.mp hf) (openFiberIncl f U c x)] at h
  exact h

theorem tangentNorm_gradient_openRegularFiberMetric_eq_norm_starProjection
    (g : RiemannianMetric (m + k) M) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ) (x : openFiber f U c) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace (𝓡 (m + k)) (openFiberIncl f U c x)) := by
      unfold TangentSpace
      infer_instance
    (openRegularFiberMetric hf U hreg c g).tangentNorm x
      ((openRegularFiberMetric hf U hreg c g).gradient (φ ∘ openFiberIncl f U c) x) =
      ‖(Submodule.span ℝ (Set.range (fun i : Fin k =>
        g.gradient (fun y => f y i) (openFiberIncl f U c x))))ᗮ.starProjection
          (g.gradient φ (openFiberIncl f U c x))‖ := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (m + k)) (openFiberIncl f U c x)) := by
    unfold TangentSpace
    infer_instance
  rw [openRegularFiberMetric_tangentNorm, mfderiv_gradient_openRegularFiberMetric hf U hreg c g hφ x]
  rfl

theorem tangentNorm_gradient_openRegularFiberMetric_le
    (g : RiemannianMetric (m + k) M) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ) (x : openFiber f U c) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    (openRegularFiberMetric hf U hreg c g).tangentNorm x
      ((openRegularFiberMetric hf U hreg c g).gradient (φ ∘ openFiberIncl f U c) x) ≤
      g.tangentNorm (openFiberIncl f U c x) (g.gradient φ (openFiberIncl f U c x)) := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (m + k)) (openFiberIncl f U c x)) := by
    unfold TangentSpace
    infer_instance
  rw [tangentNorm_gradient_openRegularFiberMetric_eq_norm_starProjection hf U hreg c g hφ x]
  exact Submodule.norm_starProjection_apply_le _ _

end PoincareConjecture.RiemannianMetric
