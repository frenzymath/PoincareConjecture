import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Statement
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Providers
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Producer
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Producer
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactAssembly
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactCoverage.Alternatives

/-!
# M26 and M27 proof entries

The source theorem constructions are intentionally owned by these numbered
entries.  Their predecessor bundles remain hypotheses, so downstream users
cannot accidentally treat a certificate as a proved predecessor service.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/- The M26 geometric construction is the Corollary 9.88/Theorem 9.89
   argument from Morgan--Tian, pp. 239--241. -/
theorem m26CanonicalNeighborhoods
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    RepairedCanonicalNeighborhoodTheory.{u} := by
  exact ⟨noncompactKappaSolutionAlternatives P, compactKappaSolutionAlternatives P⟩

theorem m26CanonicalNeighborhoodTheory
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    RepairedCanonicalNeighborhoodTheory.{u} :=
  m26CanonicalNeighborhoods P

/- The M27 construction is Theorem 9.93 and Corollary 9.94, pp. 242--243. -/
theorem m27KappaAlternatives
    (P : M27KappaAlternativePredecessors.{u}) :
    RepairedKappaAlternativeTheory.{u} := by
  exact m27KappaAlternatives_of_compact_classification P (compact_positive_classification_of_m27 P)

end PoincareMT
