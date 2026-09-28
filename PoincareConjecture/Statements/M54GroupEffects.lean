import PoincareConjecture.Definitions.M54GroupEffects





set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture






























structure RepairedGroupEffectsTheory : Prop where
  effects : ∀ {A B : GeneralizedSliceCarrier.{u}}
      (C : SurgeryTopologyConclusion A B),
      Nonempty (RepairedSurgeryGroupEffectsData.{u} C)
  persistence : ∀ (F : SurgeryFlowData.{u}) (T : ℝ)
      (component : ∀ s : Set.Icc (0 : ℝ) T,
        SurgerySelectedComponent (F.slice s.1))
      (I : RepairedGroupPersistenceInput F T component),
      Nonempty (RepairedGroupPersistenceData F T component I)

end PoincareConjecture
