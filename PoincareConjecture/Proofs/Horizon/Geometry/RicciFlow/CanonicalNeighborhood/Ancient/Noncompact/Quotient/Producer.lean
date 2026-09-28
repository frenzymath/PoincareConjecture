import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Cap.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Tube.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.EndNecks
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Cap












set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

namespace M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}


theorem exists_strongCappedTube (C : M27TwistedSphereLineFlowCertificate K)
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon)
    (hsmall : epsilon ≤ 1 / 200) :
    Nonempty (M26StrongCappedTube K t epsilon (twistedCapConstant P epsilon)) := by
  classical
  let q : UnitTwoSphere := Classical.arbitrary _
  obtain ⟨hR, a, ha⟩ := C.exists_scalarNormalized_sphere ht (q, 0)
  let cap := C.uniformSlabCap P ht hε hsmall q a ha
  let tube := C.cappedTubeOfSlabCap ht hε hsmall q a ha cap
    (C.uniformSlabCap_carrier P ht hε hsmall q a ha)
    (C.uniformSlabCap_end_neck_carrier P ht hε hsmall q a ha)
  refine ⟨NoncompactKappa.strongCappedTubeOfCappedTube K ht tube
    rfl rfl le_rfl ?_ rfl⟩
  intro x hx
  exact C.strong_necks_outside_slabCore ht hε (by linarith)
    (C.cover (q, 0)) x hx

end M27TwistedSphereLineFlowCertificate



theorem twistedCylinder_strongCappedTube
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∃ C₀ : ℝ, 0 < C₀ ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M]
            [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              M27TwistedSphereLineFlowCertificate K →
              Nonempty (M26StrongCappedTube K 0 epsilon C₀) := by
  refine ⟨1 / 200, by norm_num, le_rfl, ?_⟩
  intro epsilon hε hsmall
  refine ⟨twistedCapConstant P epsilon, twistedCapConstant_pos P hε, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K C
  exact C.exists_strongCappedTube P le_rfl hε hsmall

end PoincareConjecture
