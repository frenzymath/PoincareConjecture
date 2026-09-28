import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Retention.Copies
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Maps.TargetFibers

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.NonspanningChainAnnulus

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "Ann" => squareAnnulus 8 1

open PolygonalCrossingResolution NonspanningChainHole

variable {SA SM SC D : Set P2} {pA pL pR pC : I01 → P2}
  {s : NonspanningChainGeometry SA SM SC pA pL pR pC}
  {H : NonspanningChainHole s D} (N : NonspanningChainAnnulus H)

theorem retained_double_relation {X : Type*} {f g : P2 → X} {τ : C3 → X}
    (hAM : Disjoint SA SM) (hAC : Disjoint SA SC) (hMC : Disjoint SM SC)
    (hkeep : ∀ i (x : H.sourceSet i), g (N.copy i x) = pieceMap f τ i x)
    (hτ : InjOn τ tube)
    (hAtube : (SA \ interior D) ∩ f ⁻¹' (τ '' tube) = range pA)
    (hMtube : (SM \ interior D) ∩ f ⁻¹' (τ '' tube) = range pL ∪ range pR)
    (hCtube : (SC \ interior D) ∩ f ⁻¹' (τ '' tube) = range pC)
    (hA : ∀ t : I01, f (pA t) = τ ((-1, 1), t))
    (hL : ∀ t : I01, f (pL t) = τ ((-1, -1), t))
    (hR : ∀ t : I01, f (pR t) = τ ((1, -1), t))
    (hC : ∀ t : I01, f (pC t) = τ ((1, 1), t)) :
    let j := N.retainedCopy hAM hAC hMC
    {v : P2 × P2 | v.1 ∈ Ann ∧ v.2 ∈ Ann ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
      (fun v : N.retainedSet × N.retainedSet => (j v.1, j v.2)) ''
        {v | f v.1 = f v.2 ∧ (v.1 : P2) ≠ v.2} ∧
    {z : P2 | z ∈ Ann ∧ ∃ w ∈ Ann, g z = g w ∧ z ≠ w} =
      j '' {x : N.retainedSet | ∃ y : N.retainedSet, f x = f y ∧ (x : P2) ≠ y} := by
  have hsingle : ∀ z ∈ range (N.sourceCopy (.inr false)) ∪
      range (N.sourceCopy (.inr true)), ∀ w ∈ Ann, g w = g z → w = z := by
    rintro z (⟨y, rfl⟩ | ⟨y, rfl⟩) w hw hv
    · exact (N.strip_target_fibers hkeep hτ hAtube hMtube hCtube hA hL hR hC
        false y hw).mp hv
    · exact (N.strip_target_fibers hkeep hτ hAtube hMtube hCtube hA hL hR hC
        true y hw).mp hv
  exact ⟨retained_double_relation_eq _ (N.retainedCopy_injective hAM hAC hMC)
      (N.retainedCopy_cover hAM hAC hMC) (N.retainedCopy_values hAM hAC hMC hkeep) hsingle,
    retained_double_locus_eq _ (N.retainedCopy_injective hAM hAC hMC)
      (N.retainedCopy_cover hAM hAC hMC) (N.retainedCopy_values hAM hAC hMC hkeep) hsingle⟩

end PoincareConjecture.M76.Dehn.NonspanningChainAnnulus
