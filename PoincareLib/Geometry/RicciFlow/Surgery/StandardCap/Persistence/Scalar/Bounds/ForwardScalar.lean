import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceInputs
import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Analysis.Compactness.GuardedScalarComparison

/-!
# The scalar evolution estimate on an actual cap

Definition 9.72(8), p. 231, supplies the absolute scalar evolution bound
on a cap. M04 identifies it with the time derivative on an ordinary Ricci
flow, as required in the forward use of Lemma 11.2, pp. 268-269, in
Lemma 16.8, pp. 372-373. No whole-flow derivative estimate is assumed.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

/-- Definition 9.72, p. 231: the displayed cap core lies in its cap carrier. -/
theorem CapCertificate.core_subset_carrier {g : RiemannianMetric 3 M}
    (N : CapCertificate g) : N.core ⊆ N.carrier := by
  rw [N.core_eq_interior_closed_core]
  intro x hx
  have hclosed := interior_subset hx
  rw [N.closed_core_eq_complement_end] at hclosed
  exact hclosed.1

/-- Definition 9.72(8), p. 231, and M04 scalar evolution give the
absolute scalar rate on the actual cap carrier. -/
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

/-- At an interior ordinary-flow time the cap rate is an ordinary
derivative bound (Lemma 11.2, pp. 268-269). -/
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

end PoincareMT
