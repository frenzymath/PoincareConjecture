import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Normalization.Local
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Normalization.Component
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Pointwise.Classification
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Normalization.Exceptional










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {p : M} {b epsilon C : ℝ}



theorem AncientKappaNormalization.strongCanonicalNeighborhoodFromNormalization
    (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (N : M27StrongCanonicalNeighborhood A.target 0 p epsilon C) :
    M27StrongCanonicalNeighborhood K b p epsilon C := by
  cases N with
  | neck neck hcenter => exact .neck (A.strongNeckFromNormalization hb neck hcenter) rfl
  | cap cap => exact .cap (A.canonicalCapFromNormalization hb cap)
  | component component => exact .component (A.canonicalComponentFromNormalization hb component)
  | round component => exact .round (A.epsilonRoundComponentFromNormalization hb component)



theorem strongCanonicalNeighborhood_of_normalized_classification
    (P : M27KappaAlternativePredecessors.{u})
    (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (hepsilon : 0 < epsilon) (hC : 0 < C)
    (N : M27KappaNine93Conclusion A.target epsilon C)
    (hexception : ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate A.target)) :
    M27StrongCanonicalNeighborhood K b p epsilon (canonicalComponentConstant C) := by
  exact A.strongCanonicalNeighborhoodFromNormalization hb
    (strongCanonicalNeighborhood_of_classification P A.target hepsilon hC N hexception p)



theorem strongCanonicalNeighborhood_of_normalized_classification_of_nonexceptional
    (P : M27KappaAlternativePredecessors.{u})
    (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (hepsilon : 0 < epsilon) (hC : 0 < C)
    (N : M27KappaNine93Conclusion A.target epsilon C)
    (hexception : ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K)) :
    M27StrongCanonicalNeighborhood K b p epsilon (canonicalComponentConstant C) :=
  strongCanonicalNeighborhood_of_normalized_classification P A hb hepsilon hC N
    (fun h => hexception (A.projectivePlaneLine_of_target P.classificationServices h))



theorem strongCanonicalNeighborhoods_of_uniform_classification
    (P : M27KappaAlternativePredecessors.{u})
    {epsilon C : ℝ} (hepsilon : 0 < epsilon) (hC : 0 < C)
    (hclassification : ∀ {N : Type u} [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
      [MeasurableSpace N] [BorelSpace N] [T2Space N] [T3Space N]
      [SecondCountableTopology N] [ConnectedSpace N]
      (L : AncientKappaSolution 3 N), M27KappaNine93Conclusion L epsilon C)
    (K : AncientKappaSolution 3 M)
    (hexception : ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K))
    (b : ℝ) (hb : b ≤ 0) (p : M) :
    M27StrongCanonicalNeighborhood K b p epsilon (canonicalComponentConstant C) := by
  obtain ⟨A⟩ := P.normalization M K p b hb
  exact strongCanonicalNeighborhood_of_normalized_classification_of_nonexceptional
    P A hb hepsilon hC (hclassification A.target) hexception

end PoincareConjecture
