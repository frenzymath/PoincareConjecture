import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.FiniteNerveChains
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.ChainTrace

/-!
# Zero diagonal from moved nondegenerate simplices

Normalized simplicial chains send a characteristic basis vector to the
image simplex, or zero if that simplex becomes degenerate. Thus a map
fixing no nondegenerate simplex has zero diagonal in the actual basis.
Source: Hatcher, proof of Theorem 2C.3, printed pp. 179-181.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace PoincareMT.Proofs.M59

open M02.Topology

/-- A simplicial self-map fixing no nondegenerate simplex has zero
diagonal on its normalized chains. Source: Hatcher, Theorem 2C.3,
pp. 179-181. -/
theorem normalizedIntegralChainMap_diagonal_zero {X : SSet.{u}}
    (f : X ⟶ X) (n : ℕ)
    (hfree : ∀ s : X.nonDegenerate n, f.app _ s.val ≠ s.val)
    (s : X.nonDegenerate n) :
    (normalizedIntegralChainBasis X n).repr
      ((SSet.normalizedChainComplexMap f integralCoefficient).f n
        (normalizedIntegralChainBasis X n s)) s = 0 := by
  classical
  change normalizedIntegralChainCoordinates X n
    ((SSet.normalizedChainComplexMap f integralCoefficient).f n
      (normalizedIntegralChainBasis X n s)) s = 0
  rw [normalizedIntegralChainBasis_apply]
  have hm := congrArg (fun g => g (ULift.up (1 : ℤ)))
    (SSet.ι_normalizedChainComplexMap_f f integralCoefficient s.val)
  change (SSet.normalizedChainComplexMap f integralCoefficient).f n
      (X.ιNormalizedChainComplex (R := integralCoefficient) s.val (ULift.up 1)) =
    X.ιNormalizedChainComplex (R := integralCoefficient) (f.app _ s.val) (ULift.up 1) at hm
  rw [hm]
  by_cases hs : f.app _ s.val ∈ X.nonDegenerate n
  · have hc := normalizedIntegralChainCoordinates_generator X n ⟨f.app _ s.val, hs⟩ 1
    rw [hc]
    apply Finsupp.single_eq_of_ne
    intro h
    exact hfree s (congrArg Subtype.val h).symm
  · rw [X.ιNormalizedChainComplex_eq_zero (f.app _ s.val)
      ((X.mem_degenerate_iff_notMem_nonDegenerate _).mpr hs)]
    change (normalizedIntegralChainCoordinates X n 0) s = 0
    simp only [map_zero, Finsupp.zero_apply]

/-- The finite alternating chain trace vanishes for a simplicial map
that fixes no nondegenerate simplex through the required degree.
Source: Hatcher, Theorem 2C.3, pp. 179-181. -/
theorem normalizedIntegralChainMap_alternatingTrace_zero {X : SSet.{u}}
    (f : X ⟶ X) (N : ℕ) [∀ i, Finite (X.nonDegenerate i)]
    (hfree : ∀ i ≤ N, ∀ s : X.nonDegenerate i, f.app _ s.val ≠ s.val) :
    ChainComplex.alternatingTrace
      (SSet.normalizedChainComplexMap f integralCoefficient.{u}) N = 0 := by
  apply ChainComplex.alternatingTrace_eq_zero_of_diagonal_eq_zero _ N
    (fun i => X.nonDegenerate i) (normalizedIntegralChainBasis X)
  intro i hi s
  exact normalizedIntegralChainMap_diagonal_zero f i (hfree i hi) s

end PoincareMT.Proofs.M59
