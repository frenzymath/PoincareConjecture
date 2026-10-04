import PoincareLib.Geometry.CurveShortening.Comparison.Theory

/-!
# Actual filling witnesses from the M64 static service

The disk classes used in Claim 19.23 and Lemma 19.30, printed pp. 453-454
and 461-462, must be nonempty. M64's static approximation explicitly
supplies disks for the source family. Applying that service at an included
time gives disks for the exact projected loops, without changing the family.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

/-- Actual source disks from M64's approximation, used before the infimum
comparisons in Claim 19.23 and Lemma 19.30, pp. 453-454 and 461-462. -/
theorem m65FamilyFillingData_from_M64 (hM64 : M64ComparisonTheory.{u})
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (compact : IsCompact (Set.univ : Set M))
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (hnull : M61NullFamily Gamma) (z : LoopTwoSphere) :
    Nonempty (FillingAreaData g (Gamma z)) := by
  obtain ⟨N, _, hN⟩ := (hM64.2.1 M g D compact).raw_family Gamma hnull 1 zero_lt_one
  obtain ⟨A, _⟩ := hN N le_rfl
  exact ⟨A.source_filling z⟩

/-- Every included slice of the same projected family has genuine filling
disks; this supplies the disk hypotheses in Lemma 19.30, pp. 461-462. -/
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

end PoincareMT
