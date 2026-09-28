import PoincareConjecture.Definitions.M39ComparisonMap

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M39

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  (I : RepairedComparisonMapInput D T hT)

def ComparisonLocalModel
    (f : I.parent.carrier.carrier → I.child.carrier.carrier)
    (K : Set (D.flow.slice (D.flow.event T hT).tMinus).carrier)
    (U : Set I.parent.carrier.carrier) : Prop :=
  (∃ y, Set.EqOn f (fun _ => y) U) ∨
    (Set.MapsTo I.parent.inclusion U K ∧
      (U ⊆ I.retained ∨
        ∃ i : Fin (D.flow.event T hT).cap_count,
          Set.range ((D.flow.event T hT).local_embed i) ⊆ Set.range I.child.inclusion ∧
          Set.MapsTo ((D.flow.event T hT).limit_identify.map ∘ I.parent.inclusion)
            U ((D.flow.event T hT).necks i).neck.carrier ∧
          Set.EqOn f (fun x => I.child.inverse
            ((D.flow.event T hT).local_embed i
              (((D.flow.event T hT).local_result i).collapse
                ((D.flow.event T hT).limit_identify.map (I.parent.inclusion x))))) U))

structure ComparisonExtension where
  map : ContinuousMap I.parent.carrier.carrier I.child.carrier.carrier
  retained_agreement : ∀ x ∈ I.retained,
    I.child.inclusion (map x) = (D.flow.event T hT).retention.map
      (I.parent.inclusion x)
  outside_image_in_caps : ∀ x ∉ I.retained,
    ∃ i : Fin (D.flow.event T hT).cap_count,
      I.child.inclusion (map x) ∈ ((D.flow.event T hT).caps i).carrier
  control : Set (D.flow.slice (D.flow.event T hT).tMinus).carrier
  control_compact : IsCompact control
  control_regular : control ⊆ (D.flow.event T hT).regular_limit
  local_model : ∀ x, ∃ U, IsOpen U ∧ x ∈ U ∧ ComparisonLocalModel I map control U

end PoincareConjecture.M39
