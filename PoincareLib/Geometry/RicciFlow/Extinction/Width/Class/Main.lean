import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.IdentificationAdapters
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.AreaAdapters
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Infimum.FreeClassInfimum
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Topology.Main
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Main

/-!
# M61 widths proof entry

Compactness and real-infimum lemmas supply the generic family maximum and
free-class infimum properties from M60 filling continuity. Class labeling,
based/free range equality, W2 attainment and the short-family consequence
are checked applications of the chosen M59 system and M60 services.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- M61: given one chosen M59 comparison system and the applied M60 area
service, on every compact Hausdorff second-countable smooth three-manifold
and chosen metric, the filling areas of a continuous sphere family of null
C1 loops are continuous and attain a finite nonnegative maximum. The
infimum over all freely homotopic continuous null families is nonnegative,
lies below each competitor, has epsilon near-minimizers, and is unchanged
by the choice of free-class anchor. No minimizing loop family is asserted.

For a connected such manifold with chosen x and pi2(M,x)=0, the same M59
quotient labels every raw null family by exactly one based loop-space pi2
class. Each class has a normalized seed, while all raw free representatives
remain admissible. Its based width equals the free-class infimum of any
representing anchor and has the same nonnegative near-minimizer properties.

Separately, on a compact Hausdorff second-countable smooth n-manifold with
a chosen point having nontrivial pi2, the infimum of areas of all C1 non-null sphere maps is
positive and is attained by an actual non-null branched minimal sphere.
For every eta>0 on a compact metric three-manifold, there is the same
M60 threshold 0<zeta<eta/2 such that a raw null family with every loop
length below zeta has maximum filling area below eta.

Sources: Morgan--Tian Definition 18.17 and Claim 18.16, p. 430; Lemma 18.10,
pp. 424-426; Corollary 18.28, p. 434, with its corrected length<zeta
threshold. The complete derivation and unrestricted-width convention are
in `reviews/contracts/M61-round1.md`; M60's source corrections remain in
`reviews/errata/2026-09-14-sphere-area.md`. The 2015 Section 19.2 correction
does not change these definitions. No equality with the restricted legacy
class-width infimum is claimed. -/
theorem m61Widths (S : M59IdentificationSystem.{u}) (P60 : M60AreaTheory.{u}) :
    M61WidthTheory.{u} S.quotient := by
  have construction :
      (∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
        [T2Space M] [SecondCountableTopology M] (g : RiemannianMetric 3 M),
        IsCompact (Set.univ : Set M) → M60FillingAreaProperties g) →
      M61RawWidthCore.{u} := by
    intro filling
    constructor
    · intro M _ _ _ _ _ g hcompact F hnull
      exact m61FamilyWidth_from_M60 g (filling g hcompact) F hnull
    · intro M _ _ _ _ _ g hcompact F hnull
      exact m61FreeClassWidth_from_M60 g (filling g hcompact) F hnull
  have core := construction P60.filling
  refine
    { toM61RawWidthCore := core
      class_labels := ?_
      based_class := ?_
      sphere := ?_
      short_family := m61ShortFamilyWidth_from_M60 core P60.short_loop }
  · intro M _ _ _ _ _ compact connected x piTwo
    exact m61UniqueClassLabels_from_M59 (S.core compact connected x piTwo)
  · intro M _ _ _ _ _ g compact connected x piTwo alpha
    exact m61BasedClassWidth_from_M59 core (S.core compact connected x piTwo)
      g compact alpha
  · intro n M _ _ _ _ _ g compact x piTwo
    exact m61SphereWidth_from_M60 g (P60.least_sphere g compact x piTwo)

/-- Retain the chosen M59 system and its literal quotient in concrete assembly. -/
theorem m61Widths_from_predecessors :
    ∃ S : M59IdentificationSystem.{u}, M61WidthTheory.{u} S.quotient := by
  obtain ⟨S, _⟩ :=
    m59LoopClassesAndComponentTopology_from_predecessors
  exact ⟨S, m61Widths S m60AreaAndFilling_from_predecessors⟩

end PoincareMT
