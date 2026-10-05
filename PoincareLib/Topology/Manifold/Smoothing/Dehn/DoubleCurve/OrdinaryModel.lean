import PoincareLib.Topology.Manifold.Smoothing.Dehn.DoubleCurve.Components.RetainedModels
import PoincareLib.Topology.Manifold.Smoothing.Dehn.DoubleCurve.Crossings.RawCrossingCharts

/-!
# Finite ordinary double curves of a raw PL disk

This geometric model records the literal double locus, its finite
interval or polygon components, its finite PL partner involution and
its complete local two-plane crossing charts. It is preserved by the
constructed surgeries and has no embedded-disk conclusion as a field.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

/-- The actual finite paired double-curve geometry used at each surgery
stage. All sets and partners belong to this same literal disk map. -/
structure OrdinaryDoubleCurveModel {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (f : V2 → X) (R : Set X) where
  Index : Type
  finiteIndex : Finite Index
  pieces : Index → Set V2
  mate : Index → Index
  mate_involutive : Function.Involutive mate
  cover : ⋃ i, pieces i = doubleLocusOn f D2
  compact : ∀ i, IsCompact (pieces i)
  connected : ∀ i, IsConnected (pieces i)
  disjoint : Pairwise (fun i k ↦ Disjoint (pieces i) (pieces k))
  models : ∀ i, HasRetainedComponentModel (pieces i)
  partner : doubleLocusOn f D2 ≃ₜ doubleLocusOn f D2
  partnerPL : partner.IsFinitePL
  partner_involutive : Function.Involutive partner
  partner_value : ∀ x, f (partner x) = f x
  partner_free : ∀ x, (partner x : V2) ≠ x
  partner_rim : ∀ x, (partner x : V2) ∈ Q2 ↔ (x : V2) ∈ Q2
  unique_partner : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
    f x = f y → (x : V2) ≠ y → y = (partner x : V2)
  partner_component : ∀ (i : Index) (x : doubleLocusOn f D2),
    (x : V2) ∈ pieces i → (partner x : V2) ∈ pieces (mate i)
  crossings : ∀ x ∈ D2, ∀ y ∈ D2, x ≠ y → f x = f y →
    Nonempty (RawCrossingChart e f R x y)

end PoincareMT.M76.Dehn
