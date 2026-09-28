import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedModels
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Crossings.RawCrossingCharts










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1



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

end PoincareConjecture.M76.Dehn
