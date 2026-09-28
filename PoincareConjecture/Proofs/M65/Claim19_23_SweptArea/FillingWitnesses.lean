import PoincareConjecture.Statements.M64Comparison

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

theorem m65FamilyFillingData_from_M64 (hM64 : M64ComparisonTheory.{u})
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (compact : IsCompact (Set.univ : Set M))
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (hnull : M61NullFamily Gamma) (z : LoopTwoSphere) :
    Nonempty (FillingAreaData g (Gamma z)) := by
  obtain ⟨N, _, hN⟩ := (hM64.2.1 M g D compact).raw_family Gamma hnull 1 zero_lt_one
  obtain ⟨A, _⟩ := hN N le_rfl
  exact ⟨A.source_filling z⟩

theorem m65ProjectedDisk_nonempty (hM64 : M64ComparisonTheory.{u})
    {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
    (compact : IsCompact (Set.univ : Set M))
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    {zeta circumference : ℝ} {P : M62.CircleProductData F circumference}
    {A : M63RawApproximation F Gamma zeta} (S : M63ProductSolutionFamily P A)
    (t : Set.Icc a b) (z : LoopTwoSphere) :
    Nonempty (LipschitzSpanningDisk (F.metric t) (S.projected t z)) := by
  obtain ⟨D⟩ := m65FamilyFillingData_from_M64 hM64 (F.metric t) (F.connection t)
    compact (S.projected t) (S.projected_null t) z
  exact D.nonempty

end PoincareConjecture
