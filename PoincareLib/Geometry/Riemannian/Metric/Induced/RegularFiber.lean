import PoincareLib.Geometry.Manifold.RegularFiber.Inclusion
import PoincareLib.Geometry.Riemannian.Metric.Induced.Complete
import PoincareLib.Geometry.Riemannian.Metric.Induced.Gradient

/-!
# The metric of a simultaneous regular fiber

The smooth fiber carries the pullback of the ambient metric. A closed fiber
in a complete ambient manifold is complete in its intrinsic induced metric.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle InnerProductSpace

namespace PoincareMT.RiemannianMetric

variable {m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
  [IsManifold (𝓡 (m + k)) ∞ M]
  {f : M → Fin k → ℝ}
  (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
  (c : Fin k → ℝ)
  (hreg : ∀ x : M, f x = c →
    Function.Surjective (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x))

local instance regularFiber_ambient_finrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The actual induced metric on a simultaneous regular fiber. -/
def regularFiberMetric (g : RiemannianMetric (m + k) M) :
    letI := fiberChartedSpace (m := m) hf c hreg
    letI := isManifold_fiber (m := m) hf c hreg
    RiemannianMetric m (f ⁻¹' {c} : Set M) := by
  let := fiberChartedSpace (m := m) hf c hreg
  let := isManifold_fiber (m := m) hf c hreg
  exact Induced.pullbackMetric g ((↑) : (f ⁻¹' {c} : Set M) → M)
    (contMDiff_fiber_val hf c hreg) (injective_mfderiv_fiber_val hf c hreg)

@[simp] theorem regularFiberMetric_inner (g : RiemannianMetric (m + k) M)
    (x : (f ⁻¹' {c} : Set M)) (v w : EuclideanSpace ℝ (Fin m)) :
    letI := fiberChartedSpace (m := m) hf c hreg
    letI := isManifold_fiber (m := m) hf c hreg
    (regularFiberMetric hf c hreg g).inner x v w =
      g.inner (x : M)
        (mfderiv (𝓡 m) (𝓡 (m + k)) ((↑) : (f ⁻¹' {c} : Set M) → M) x v)
        (mfderiv (𝓡 m) (𝓡 (m + k)) ((↑) : (f ⁻¹' {c} : Set M) → M) x w) := rfl

/-- Completeness is inherited by the actual metric on a closed regular fiber. -/
theorem metricComplete_regularFiberMetric [T3Space M]
    (g : RiemannianMetric (m + k) M) (hcomplete : MetricComplete g) :
    letI := fiberChartedSpace (m := m) hf c hreg
    letI := isManifold_fiber (m := m) hf c hreg
    MetricComplete (regularFiberMetric hf c hreg g) := by
  let := fiberChartedSpace (m := m) hf c hreg
  let := isManifold_fiber (m := m) hf c hreg
  apply metricComplete_of_isClosedEmbedding (regularFiberMetric hf c hreg g) g
    (contMDiff_fiber_val hf c hreg)
    (isClosed_singleton.preimage hf.continuous).isClosedEmbedding_subtypeVal
    (regularFiberMetric_inner hf c hreg g) hcomplete

/-- The induced gradient is the ambient gradient projected to the common
kernel of the defining differentials. -/
theorem mfderiv_gradient_regularFiberMetric
    (g : RiemannianMetric (m + k) M) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (x : (f ⁻¹' {c} : Set M)) :
    letI := fiberChartedSpace (m := m) hf c hreg
    letI := isManifold_fiber (m := m) hf c hreg
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace (𝓡 (m + k)) (x : M)) := by
      unfold TangentSpace
      infer_instance
    mfderiv (𝓡 m) (𝓡 (m + k)) ((↑) : (f ⁻¹' {c} : Set M) → M) x
        ((regularFiberMetric hf c hreg g).gradient (fun y => φ y) x) =
      (Submodule.span ℝ (Set.range (fun i : Fin k =>
        g.gradient (fun y => f y i) (x : M))))ᗮ.starProjection (g.gradient φ (x : M)) := by
  let := fiberChartedSpace (m := m) hf c hreg
  let := isManifold_fiber (m := m) hf c hreg
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (m + k)) (x : M)) := by
    unfold TangentSpace
    infer_instance
  have h := mfderiv_gradient_comp_eq_starProjection (regularFiberMetric hf c hreg g) g
    ((contMDiff_fiber_val hf c hreg x).mdifferentiableAt (by simp))
    ((hφ (x : M)).mdifferentiableAt (by simp)) (regularFiberMetric_inner hf c hreg g x)
  rw [range_mfderiv_fiber_val hf c hreg x,
    ker_mfderiv_pi_eq_orthogonal_span_gradients g (fun i y => f y i)
      (contMDiff_pi_space.mp hf) (x : M)] at h
  exact h

end PoincareMT.RiemannianMetric
