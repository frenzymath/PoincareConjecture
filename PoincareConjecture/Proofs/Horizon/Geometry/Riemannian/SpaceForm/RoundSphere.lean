import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Immersion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Euclidean
import Mathlib.Geometry.Manifold.Instances.Sphere







noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff Bundle

namespace Poincare.Geometry.Riemannian.SpaceForm
open PoincareConjecture

abbrev UnitSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1


noncomputable def roundSphereMetric (n : ℕ) :
    RiemannianMetric n (UnitSphere n) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨by simp⟩
  exact RiemannianMetric.Induced.pullbackMetric
    (RiemannianMetric.euclideanMetric (n + 1))
    ((↑) : UnitSphere n → EuclideanSpace ℝ (Fin (n + 1)))
    contMDiff_coe_sphere (fun x => injective_mvfderiv_subtypeVal_sphere x)

@[simp] theorem roundSphereMetric_inner {n : ℕ} (x : UnitSphere n)
    (v w : TangentSpace (𝓡 n) x) :
    (roundSphereMetric n).inner x v w =
      (RiemannianMetric.euclideanMetric (n + 1)).inner (x : EuclideanSpace ℝ (Fin (n + 1)))
        (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
          ((↑) : UnitSphere n → EuclideanSpace ℝ (Fin (n + 1))) x v)
        (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
          ((↑) : UnitSphere n → EuclideanSpace ℝ (Fin (n + 1))) x w) := by
  rfl

end Poincare.Geometry.Riemannian.SpaceForm
