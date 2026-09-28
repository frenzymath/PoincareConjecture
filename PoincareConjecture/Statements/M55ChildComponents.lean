import PoincareConjecture.Definitions.M55ChildComponents
import PoincareConjecture.Statements.M54GroupEffects








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


















structure RepairedChildComponentsTheory : Prop where
  components : ∀ (G54 : RepairedGroupEffectsTheory.{u}),
    ∀ {A B : GeneralizedSliceCarrier.{u}}
      (C : SurgeryTopologyConclusion A B)
      (E : RepairedSurgeryGroupEffectsData C)
      (_hE : E = Classical.choice (G54.effects C)),
      (parent_groups_subsingleton :
        ∀ (i : Fin C.piece_count) (hi : C.kind i = .survivor),
          ∀ x : (C.piece i).carrier,
            Subsingleton (FundamentalGroup A.carrier
              (E.parent_basepoint i hi x))) →
      Nonempty (RepairedChildComponentsData C E)

end PoincareConjecture
