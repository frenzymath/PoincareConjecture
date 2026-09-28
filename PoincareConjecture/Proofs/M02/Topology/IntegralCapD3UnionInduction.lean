import PoincareConjecture.Proofs.M02.Topology.ModuleExactDiagram



set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe u

namespace PoincareConjecture.Proofs.M02.Topology

theorem moduleCapD3_union_isIso
    {CI3 CP3 CU3 CI4 : ModuleCat.{u} Int}
    {HI0 HP0 HU0 : ModuleCat.{u} Int}
    (cDiff3 : CI3 ⟶ CP3) (cSum3 : CP3 ⟶ CU3) (cConn3 : CU3 ⟶ CI4)
    (hDiff0 : HI0 ⟶ HP0) (hSum0 : HP0 ⟶ HU0)
    (d3I : CI3 ⟶ HI0) (d3Pair : CP3 ⟶ HP0) (d3Union : CU3 ⟶ HU0)
    (hC0 : ∀ a : CI3, cSum3 (cDiff3 a) = 0)
    (hSqDiff3 : ∀ a : CI3, d3Pair (cDiff3 a) = hDiff0 (d3I a))
    (hSqSum3 : ∀ v : CP3, d3Union (cSum3 v) = hSum0 (d3Pair v))
    (hExactCUnion : ∀ x : CU3, cConn3 x = 0 → ∃ y, cSum3 y = x)
    (hExactHPair : ∀ w : HP0, hSum0 w = 0 → ∃ z, hDiff0 z = w)
    (hD3ISurj : Function.Surjective d3I)
    (hD3PairSurj : Function.Surjective d3Pair)
    (hD3PairInj : Function.Injective d3Pair)
    (hH0SumSurj : Function.Surjective hSum0)
    (hC4 : IsZero CI4) :
    IsIso d3Union := by
  have hsurj : Function.Surjective d3Union := by
    intro y
    obtain ⟨v, hv⟩ := hH0SumSurj y
    obtain ⟨c, hc⟩ := hD3PairSurj v
    exact ⟨cSum3 c, (hSqSum3 c).trans
      ((congrArg hSum0 hc).trans hv)⟩
  have hinj : Function.Injective d3Union := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hx0 : d3Union (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hc0 : cConn3 (x - y) = 0 :=
      (ModuleCat.isZero_iff_subsingleton.mp hC4).elim _ _
    obtain ⟨v, hv⟩ := hExactCUnion (x - y) hc0
    have hp0 : hSum0 (d3Pair v) = 0 := by
      rw [← hSqSum3 v, hv, hx0]
    obtain ⟨z, hz⟩ := hExactHPair (d3Pair v) hp0
    obtain ⟨a, ha⟩ := hD3ISurj z
    have hpa : d3Pair (cDiff3 a) = d3Pair v := by
      rw [hSqDiff3 a, ha, hz]
    have hva : cDiff3 a = v := hD3PairInj hpa
    calc
      x - y = cSum3 v := hv.symm
      _ = cSum3 (cDiff3 a) := by rw [hva]
      _ = 0 := hC0 a
  exact (ConcreteCategory.isIso_iff_bijective d3Union).mpr ⟨hinj, hsurj⟩

end PoincareConjecture.Proofs.M02.Topology
