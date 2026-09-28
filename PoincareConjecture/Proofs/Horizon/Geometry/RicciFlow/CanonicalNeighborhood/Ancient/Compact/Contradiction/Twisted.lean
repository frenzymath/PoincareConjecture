import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Cap.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.EndNecks










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


theorem strong_necks_outside_interior_slabCore
    (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (p x : M)
    (hx : x ∉ interior (C.slabCore
      (epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature p)))) :
    ∃ N : StrongEvolvingNeck K t epsilon, N.center = x := by
  obtain ⟨q, rfl⟩ := C.cover_surjective x
  rw [C.cover_mem_interior_slabCore_iff, not_lt] at hx
  by_cases hq : 0 ≤ q.2
  · apply C.exists_strongEvolvingNeck_of_positive_height ht hε hhalf q
    rw [C.scalarCurvature_eq ht (C.cover q) p]
    simpa only [abs_of_nonneg hq] using hx
  · have heq : C.cover (m27TwistedProductInvolution q) = C.cover q :=
      ((C.cover_fibers q (m27TwistedProductInvolution q)).mpr (Or.inr rfl)).symm
    rw [← heq]
    apply C.exists_strongEvolvingNeck_of_positive_height ht hε hhalf
      (m27TwistedProductInvolution q)
    rw [C.scalarCurvature_eq ht (C.cover (m27TwistedProductInvolution q)) p]
    simpa only [m27TwistedProductInvolution, abs_of_neg (lt_of_not_ge hq)] using hx



theorem exists_cap_core_or_strong_neck
    (C : M27TwistedSphereLineFlowCertificate K)
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon)
    (hsmall : epsilon ≤ 1 / 200) :
    ∃ A : CapCertificate (K.flow.metric t),
      A.epsilon = epsilon ∧ A.cap_constant = twistedCapConstant P epsilon ∧
      A.connection = K.flow.connection t ∧
      ∀ x : M, x ∈ A.core ∨
        ∃ N : StrongEvolvingNeck K t epsilon, N.center = x := by
  classical
  let q : UnitTwoSphere := Classical.arbitrary _
  obtain ⟨_, a, ha⟩ := C.exists_scalarNormalized_sphere ht (q, 0)
  refine ⟨C.uniformSlabCap P ht hε hsmall q a ha, rfl, rfl, rfl, ?_⟩
  intro x
  by_cases hx : x ∈ (C.uniformSlabCap P ht hε hsmall q a ha).core
  · exact Or.inl hx
  · exact Or.inr (C.strong_necks_outside_interior_slabCore ht hε
      (by linarith) (C.cover (q, 0)) x hx)

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
