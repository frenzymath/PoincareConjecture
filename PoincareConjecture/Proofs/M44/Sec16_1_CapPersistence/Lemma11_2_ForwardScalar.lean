import PoincareConjecture.Statements.M44Providers
import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.M44.Mathlib.GuardedScalarComparison

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem CapCertificate.core_subset_carrier {g : RiemannianMetric 3 M}
    (N : CapCertificate g) : N.core ⊆ N.carrier := by
  rw [N.core_eq_interior_closed_core]
  intro x hx
  have hclosed := interior_subset hx
  rw [N.closed_core_eq_complement_end] at hclosed
  exact hclosed.1

theorem CapCertificate.scalar_rate_within
    (P : M44CapPersistencePredecessors.{u}) {J : Set ℝ}
    (F : RicciFlow 3 M J) {t C : ℝ} (ht : t ∈ J)
    (N : CapCertificate (F.metric t)) (hconnection : N.connection = F.connection t)
    (hC : N.cap_constant ≤ C) {x : M} (hx : x ∈ N.carrier) :
    ∃ d : ℝ,
      HasDerivWithinAt (fun s => (F.connection s).scalarCurvature x) d J t ∧
        |d| ≤ C * (F.connection t).scalarCurvature x ^ 2 := by
  refine ⟨_, P.curvature.scalar_evolution 3 M J F t ht x, ?_⟩
  obtain ⟨bound, hbound, hrate⟩ := N.laplacian_bound
  have h := hrate x hx
  rw [hconnection] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hbound.le.trans hC) (sq_nonneg _))

theorem CapCertificate.scalar_rate
    (P : M44CapPersistencePredecessors.{u}) {J : Set ℝ}
    (F : RicciFlow 3 M J) {t C : ℝ} (ht : t ∈ J) (hJ : J ∈ 𝓝 t)
    (N : CapCertificate (F.metric t)) (hconnection : N.connection = F.connection t)
    (hC : N.cap_constant ≤ C) {x : M} (hx : x ∈ N.core) :
    ∃ d : ℝ,
      HasDerivAt (fun s => (F.connection s).scalarCurvature x) d t ∧
        |d| ≤ C * (F.connection t).scalarCurvature x ^ 2 := by
  obtain ⟨d, hd, hbound⟩ := N.scalar_rate_within P F ht hconnection hC
    (N.core_subset_carrier hx)
  exact ⟨d, hd.hasDerivAt hJ, hbound⟩

end PoincareConjecture
