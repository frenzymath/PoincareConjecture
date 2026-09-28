import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Trichotomy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Noncompact









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem positiveSectionalCurvature_of_compact
    (P : AncientKappaClassificationServices.{u}) (K : AncientKappaSolution 3 M)
    (hcompact : IsCompact (univ : Set M)) :
    ∀ t : ℝ, t ≤ 0 → M27PositiveSectionalCurvature K t := by
  let : CompactSpace M := ⟨hcompact⟩
  rcases P.curvatureTrichotomy K with hpos | hmodels
  · exact hpos
  rcases hmodels with hmodel | hmodels
  · obtain ⟨C⟩ := hmodel
    let : CompactSpace (UnitTwoSphere × ℝ) := C.identification.symm.toHomeomorph.compactSpace
    exact (noncompact_univ (UnitTwoSphere × ℝ) isCompact_univ).elim
  rcases hmodels with hmodel | hmodel
  · obtain ⟨C⟩ := hmodel
    let : CompactSpace (RealProjectiveTwo × ℝ) := C.product_homeomorph.compactSpace
    exact (noncompact_univ (RealProjectiveTwo × ℝ) isCompact_univ).elim
  · obtain ⟨C⟩ := hmodel
    exact (C.not_isCompact_univ hcompact).elim

end PoincareConjecture.AncientKappaSolution
