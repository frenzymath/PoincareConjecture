import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.OriginalOrdinaryResolution
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedCounts

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem RetainedSquareMapFacts.ordinary_circle_resolution
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f g : V2 → X} {R : Set X}
    {K : Set V2} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j) (old : OrdinaryDoubleCurveModel e f R)
    (hf : ContinuousOn f D2) (hg : ContinuousOn g D2)
    (hPL : ∃ J : V2 → V2, FinitePiecewiseAffineOn J K ∧ ∀ x : K, J x = j x)
    (H : RetainedSourceOpenHomeomorph f g K j)
    (hwhole : ∀ i, old.pieces i ⊆ K ∨ Disjoint (old.pieces i) K)
    (i : old.Index) (hiQ : Disjoint (old.pieces i) Q2) (hiK : ¬ old.pieces i ⊆ K) :
    Nonempty (OrdinaryDoubleCurveModel e g R) ∧
      doubleBoundaryComponentCount g D2 Q2 ≤ doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 < doubleInteriorComponentCount f D2 Q2 := by
  let : Finite old.Index := old.finiteIndex
  have hK : IsCompact K := by obtain ⟨J, hJ, _⟩ := hPL; exact hJ.isCompact
  have hcross := H.exists_raw_crossings facts hf hg old.partner old.unique_partner old.crossings
  refine ⟨facts.nonempty_ordinary_model old hK hPL hwhole hcross, ?_⟩
  exact retained_double_component_interior_counts_decrease old.pieces old.mate old.partner
    rfl old.cover old.compact old.connected old.disjoint
    (fun x => (old.partner_value x).symm) (fun x => Ne.symm (old.partner_free x))
    old.unique_partner old.partner_component facts.old_subset hwhole j facts.injective
    facts.continuous facts.double_locus facts.boundary i hiQ hiK

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
