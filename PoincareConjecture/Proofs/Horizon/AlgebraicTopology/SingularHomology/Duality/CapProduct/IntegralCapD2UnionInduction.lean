import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.HomologicalAlgebra.ModuleExactDiagram







set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u

namespace Poincare.Topology

theorem moduleCapD2_union_isIso
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
    (hD2I : Function.Surjective d2I)
    (hD2PairSurj : Function.Surjective d2Pair)
    (hD2PairInj : Function.Injective d2Pair)
    (hD3I : Function.Surjective d3I)
    (hD3IInj : Function.Injective d3I)
    (hD3PairInj : Function.Injective d3Pair) :
    IsIso d2Union := by
  have hsurj : Function.Surjective d2Union := by
    intro y
    obtain ⟨z, hz⟩ := hD3I (-hConn1 y)
    have hz0 : cDiff3 z = 0 := by
      apply hD3PairInj
      rw [hSqDiff3 z, hz, map_neg, hH1, map_zero]
      simp
    obtain ⟨x, hx⟩ := hExactCInter z hz0
    have hyker : hConn1 (y - d2Union x) = 0 := by
      rw [map_sub, hSqConn2 x, hx, hz, sub_eq_add_neg]
      simp
    obtain ⟨w, hw⟩ := hExactHUnion (y - d2Union x) hyker
    obtain ⟨v, hv⟩ := hD2PairSurj w
    have hvmap : d2Union (cSum2 v) = hSum1 w := by
      rw [hSqSum2 v, hv]
    refine ⟨cSum2 v + x, ?_⟩
    rw [map_add, hvmap, hw]
    abel
  have hinj : Function.Injective d2Union := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hx0 : d2Union (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hc0 : cConn2 (x - y) = 0 := by
      apply hD3IInj
      have hs'' : 0 = -d3I (cConn2 (x - y)) := by simpa [hx0] using hSqConn2 (x - y)
      have hzero : d3I (cConn2 (x - y)) = 0 := neg_eq_zero.mp hs''.symm
      simpa using hzero
    obtain ⟨v, hv⟩ := hExactCUnion (x - y) hc0
    have hp0 : hSum1 (d2Pair v) = 0 := by
      rw [← hSqSum2 v, hv, hx0]
    obtain ⟨z, hz⟩ := hExactHPair (d2Pair v) hp0
    obtain ⟨a, ha⟩ := hD2I z
    have hpa : d2Pair (cDiff2 a) = d2Pair v := by
      rw [hSqDiff2 a, ha, hz]
    have hva : cDiff2 a = v := hD2PairInj hpa
    have hzero : x - y = 0 := by
      calc
        x - y = cSum2 v := hv.symm
        _ = cSum2 (cDiff2 a) := by rw [hva]
        _ = 0 := hC0 a
    exact hzero
  exact (ConcreteCategory.isIso_iff_bijective d2Union).mpr ⟨hinj, hsurj⟩

end Poincare.Topology
