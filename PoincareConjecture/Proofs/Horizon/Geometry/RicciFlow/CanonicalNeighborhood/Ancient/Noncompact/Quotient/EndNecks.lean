import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.StrongNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.End
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Bounds.Curvature










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem strong_necks_outside_slabCore (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hεhalf : epsilon < 1 / 2)
    (p : M) (x : M)
    (hx : x ∉ C.slabCore
      (epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature p))) :
    ∃ N : StrongEvolvingNeck K t epsilon, N.center = x := by
  have hr : 0 ≤ epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature p) :=
    div_nonneg (inv_nonneg.mpr hε.le) (Real.sqrt_nonneg _)
  have hxend : x ∈ (C.slabCore
      (epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature p)))ᶜ := hx
  rw [C.complement_slabCore hr] at hxend
  obtain ⟨q, rfl⟩ := hxend
  apply C.exists_strongEvolvingNeck_of_positive_height ht hε hεhalf (q.1, q.2.1)
  rw [C.scalarCurvature_eq ht (C.cover (q.1, q.2.1)) p]
  exact q.2.2.le


theorem exists_compact_core_strong_necks (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hεhalf : epsilon < 1 / 2) :
    ∃ A : Set M, IsCompact A ∧
      ∀ x ∉ A, ∃ N : StrongEvolvingNeck K t epsilon, N.center = x := by
  let p : M := Classical.arbitrary M
  refine ⟨C.slabCore (epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature p)),
    C.isCompact_slabCore _, ?_⟩
  exact C.strong_necks_outside_slabCore ht hε hεhalf p

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
