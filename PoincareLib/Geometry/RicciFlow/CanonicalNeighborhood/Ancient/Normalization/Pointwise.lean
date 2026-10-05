import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Normalization.Local
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Normalization.Component
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Pointwise.Classification
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Normalization.Exceptional

/-!
# Canonical neighborhoods pulled back from a normalized ancient slice

The four neighborhood branches return to the original flow without changing
epsilon or the component constant. The seven-alternative classification then
applies at any normalization point whose normalized flow is nonexceptional.
Reference: Morgan--Tian, Corollary 9.94, p. 243.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {p : M} {b epsilon C : ℝ}

/-- Scalar normalization preserves every canonical-neighborhood branch at its
basepoint, including the evolving neck's full backward time interval. -/
theorem AncientKappaNormalization.strongCanonicalNeighborhoodFromNormalization
    (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (N : M27StrongCanonicalNeighborhood A.target 0 p epsilon C) :
    M27StrongCanonicalNeighborhood K b p epsilon C := by
  cases N with
  | neck neck hcenter => exact .neck (A.strongNeckFromNormalization hb neck hcenter) rfl
  | cap cap => exact .cap (A.canonicalCapFromNormalization hb cap)
  | component component => exact .component (A.canonicalComponentFromNormalization hb component)
  | round component => exact .round (A.epsilonRoundComponentFromNormalization hb component)

/-- Classification of the actual normalized flow yields a neighborhood at the
original spacetime point, with the same universal enlargement of the constant. -/
theorem strongCanonicalNeighborhood_of_normalized_classification
    (P : M27KappaAlternativePredecessors.{u})
    (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (hepsilon : 0 < epsilon) (hC : 0 < C)
    (N : M27KappaNine93Conclusion A.target epsilon C)
    (hexception : ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate A.target)) :
    M27StrongCanonicalNeighborhood K b p epsilon (canonicalComponentConstant C) := by
  exact A.strongCanonicalNeighborhoodFromNormalization hb
    (strongCanonicalNeighborhood_of_classification P A.target hepsilon hC N hexception p)

/-- Nonexceptionalness of the original flow suffices at every normalization
point; it need not be assumed separately for the normalized flow. -/
theorem strongCanonicalNeighborhood_of_normalized_classification_of_nonexceptional
    (P : M27KappaAlternativePredecessors.{u})
    (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (hepsilon : 0 < epsilon) (hC : 0 < C)
    (N : M27KappaNine93Conclusion A.target epsilon C)
    (hexception : ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K)) :
    M27StrongCanonicalNeighborhood K b p epsilon (canonicalComponentConstant C) :=
  strongCanonicalNeighborhood_of_normalized_classification P A hb hepsilon hC N
    (fun h => hexception (A.projectivePlaneLine_of_target P.classificationServices h))

/-- A uniform seven-way time-zero classification supplies the entire
all-time pointwise conclusion with one universal enlarged constant. -/
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

end PoincareMT
