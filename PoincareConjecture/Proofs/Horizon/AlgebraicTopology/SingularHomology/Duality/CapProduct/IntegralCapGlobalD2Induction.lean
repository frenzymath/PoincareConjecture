import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralCapD2UnionInduction
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.MayerVietoris.IntegralCompactSupportOpenMVUnion
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.MayerVietoris.IntegralCompactSupportOpenMVIntersection
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralOpenUnionMayerVietoris
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CompactSupport.IntegralCompactSupportCap

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X] [RegularSpace X]

theorem integralCompactSupportCapTwo_union_isIso_of_squares
    {X : Type u} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    {CI2 CP2 CU2 CI3 CP3 : ModuleCat.{u} Int}
    {HI1 HP1 HU1 HI0 HP0 : ModuleCat.{u} Int}
    (cDiff2 : CI2 ⟶ CP2) (cSum2 : CP2 ⟶ CU2) (cConn2 : CU2 ⟶ CI3)
    (cDiff3 : CI3 ⟶ CP3)
    (hDiff1 : HI1 ⟶ HP1) (hSum1 : HP1 ⟶ HU1) (hConn1 : HU1 ⟶ HI0)
    (hDiff0 : HI0 ⟶ HP0)
    (d2I : CI2 ⟶ HI1) (d2Pair : CP2 ⟶ HP1) (d2Union : CU2 ⟶ HU1)
    (d3I : CI3 ⟶ HI0) (d3Pair : CP3 ⟶ HP0)
    (hC0 : ∀ a : CI2, cSum2 (cDiff2 a) = 0)
    (hH1 : ∀ y : HU1, hDiff0 (hConn1 y) = 0)
    (hSqDiff2 : ∀ a : CI2, d2Pair (cDiff2 a) = hDiff1 (d2I a))
    (hSqSum2 : ∀ v : CP2, d2Union (cSum2 v) = hSum1 (d2Pair v))
    (hSqConn2 : ∀ x : CU2, hConn1 (d2Union x) = -d3I (cConn2 x))
    (hSqDiff3 : ∀ z : CI3, d3Pair (cDiff3 z) = hDiff0 (d3I z))
    (hExactCUnion : ∀ x : CU2, cConn2 x = 0 → ∃ y, cSum2 y = x)
    (hExactCInter : ∀ z : CI3, cDiff3 z = 0 → ∃ x, cConn2 x = z)
    (hExactHUnion : ∀ y : HU1, hConn1 y = 0 → ∃ w, hSum1 w = y)
    (hExactHPair : ∀ w : HP1, hSum1 w = 0 → ∃ z, hDiff1 z = w)
    [IsIso d2I] [IsIso d2Pair] [IsIso d3I] [IsIso d3Pair] :
    IsIso d2Union := by
  have _ := hU
  have _ := hV
  apply moduleCapD2_union_isIso cDiff2 cSum2 cConn2 cDiff3
    hDiff1 hSum1 hConn1 hDiff0 d2I d2Pair d2Union d3I d3Pair
    hC0 hH1 hSqDiff2 hSqSum2 hSqConn2 hSqDiff3 hExactCUnion hExactCInter
    hExactHUnion hExactHPair
  · apply (ModuleCat.epi_iff_surjective _).mp
    infer_instance
  · apply (ModuleCat.epi_iff_surjective _).mp
    infer_instance
  · apply (ModuleCat.mono_iff_injective _).mp
    infer_instance
  · apply (ModuleCat.epi_iff_surjective _).mp
    infer_instance
  · apply (ModuleCat.mono_iff_injective _).mp
    infer_instance
  · apply (ModuleCat.mono_iff_injective _).mp
    infer_instance

end Poincare.Topology
