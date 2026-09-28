import PoincareConjecture.Proofs.M61.ClassAdapters
import PoincareConjecture.Proofs.M61.AreaAdapters
import PoincareConjecture.Proofs.M61.Def18_17_Width.FreeClassInfimum
import PoincareConjecture.Proofs.M59
import PoincareConjecture.Proofs.M60










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture





























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


theorem m61Widths_from_predecessors :
    ∃ S : M59IdentificationSystem.{u}, M61WidthTheory.{u} S.quotient := by
  obtain ⟨S, _⟩ :=
    m59LoopClassesAndComponentTopology_from_predecessors
  exact ⟨S, m61Widths S m60AreaAndFilling_from_predecessors⟩

end PoincareConjecture
