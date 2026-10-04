import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Asymptotic.Topology
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.ProjectiveDouble
import PoincareLib.Geometry.RicciFlow.AncientKappa.Topology.PositiveCurvature

/-!
# Smooth models of nonround compact ancient slices

The original M26 services construct a closed model at a large past slice.
Its carrier is the original manifold. Positive sectional curvature and the
finite fundamental group exclude the projective connected sum, leaving the
two models required by the compact-small alternative.

Reference: Morgan--Tian, Theorem 9.89, pp. 240--241 (`MT2007`).
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

/-- Compactness supplies the topological exclusion on the original carrier. -/
theorem compact_noEmbeddedTrivialNormalProjectivePlane
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : AncientKappaSolution 3 M) (hcompact : IsCompact (univ : Set M)) :
    NoEmbeddedTrivialNormalProjectivePlane K := by
  let : CompactSpace M := ⟨hcompact⟩
  exact K.noEmbeddedTrivialNormalProjectivePlane_of_compact_positive_sectional 0
    (K.positiveSectionalCurvature_of_compact P.classificationServices hcompact 0 le_rfl)

/-- The past-slice topology is obtained directly from M26's original services;
no compact M26 or M27 conclusion is used. -/
theorem compact_nonround_sphere_or_projective
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : AncientKappaSolution 3 M) (hcompact : IsCompact (univ : Set M))
    (hnonround : ¬ IsRoundAncientKappaSolution K) :
    Nonempty (ClosedComponentCertificate .threeSphere (univ : Set M)) ∨
      Nonempty (ClosedComponentCertificate .realProjectiveThree (univ : Set M)) := by
  obtain ⟨kind, ⟨model⟩⟩ := compact_nonround_closed_model P K hcompact hnonround
    (compact_noEmbeddedTrivialNormalProjectivePlane P K hcompact)
  let : CompactSpace M := ⟨hcompact⟩
  cases kind with
  | threeSphere => exact Or.inl ⟨model⟩
  | realProjectiveThree => exact Or.inr ⟨model⟩
  | realProjectiveThreeConnectedSum =>
      exact (model.not_univ_of_projectiveDouble_of_compact_positive_sectional
        (K.flow.metric 0) (K.flow.connection 0) (K.complete 0 le_rfl)
        (K.positiveSectionalCurvature_of_compact P.classificationServices hcompact 0 le_rfl)
        rfl).elim

end PoincareMT
