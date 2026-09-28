import PoincareConjecture.Proofs.M09.CenteredCoordinateDifferential








set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem mvfderiv_vector_centeredChart_of_eventuallyEq (p : M) (f : M → V) (φ : E → V)
    (hφ : DifferentiableAt ℝ φ ((chartAt E p) p))
    (heq : f =ᶠ[𝓝 p] (fun q ↦ φ ((chartAt E p) q))) (X : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) f p X = fderiv ℝ φ ((chartAt E p) p) X := by
  have hc := (mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt (mem_chart_source E p)
  have h := (hφ.mdifferentiableAt.hasMFDerivAt.comp p hc.hasMFDerivAt).mfderiv
  rw [mfderiv_eq_fderiv] at h
  change mfderiv (𝓡 n) (𝓘(ℝ, V)) (fun q ↦ φ ((chartAt E p) q)) p =
    (fderiv ℝ φ ((chartAt E p) p)).comp (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) p) at h
  rw [mvfderiv, heq.mfderiv_eq, h, mfderiv_chartAt_self]
  rfl

end PoincareConjecture.Proofs.M09
