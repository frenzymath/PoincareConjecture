import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import PoincareConjecture.Definitions.Ch15.SurgeryComparison
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.GroupTheory.CoprodI











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture




structure FiniteOrCyclicFactors (n : Nat) where
  carrier : Fin n → Type u
  group : ∀ i, Group (carrier i)
  kind : ∀ i, (Finite (carrier i)) ∨
    Nonempty (carrier i ≃* Multiplicative ℤ)

def IsFiniteFreeProductCyclic (G : Type u) [Group G] : Prop :=
  ∃ n : Nat, ∃ F : FiniteOrCyclicFactors.{u} n,
    letI : ∀ i, Group (F.carrier i) := F.group
    Nonempty (G ≃* Monoid.CoprodI F.carrier)

abbrev selectedFundamentalGroup {A : GeneralizedSliceCarrier.{u}}
    (C : SurgerySelectedComponent A) : Type u :=
  FundamentalGroup C.carrier.carrier C.basepoint

structure RepairedGroupFactorData (G H : Type u)
    [Group G] [Group H] where
  factor_map : G →* H
  kernel_subgroup : Subgroup G
  kernel_eq : factor_map.ker = kernel_subgroup
  factor_surjective : Function.Surjective factor_map
  survivor_injection : H →* G
  injection_injective : Function.Injective survivor_injection
  factor_retraction : factor_map.comp survivor_injection = MonoidHom.id H

theorem RepairedGroupFactorData.target_subsingleton
    {G H : Type u} [Group G] [Group H]
    (D : RepairedGroupFactorData G H) [Subsingleton G] :
    Subsingleton H := by
  constructor
  intro a b
  apply D.injection_injective
  exact Subsingleton.elim _ _





structure RepairedSurgeryGroupEffectsData
    {A B : GeneralizedSliceCarrier.{u}}
    (C : SurgeryTopologyConclusion A B) where
  parent_basepoint : ∀ (i : Fin C.piece_count),
    C.kind i = .survivor → (C.piece i).carrier → A.carrier
  piece_effect : ∀ (i : Fin C.piece_count) (hi : C.kind i = .survivor)
      (x : (C.piece i).carrier),
    RepairedGroupFactorData
      (FundamentalGroup A.carrier (parent_basepoint i hi x))
      (FundamentalGroup (C.piece i).carrier x)



structure RepairedGroupPersistenceInput (F : SurgeryFlowData.{u}) (T : ℝ)
    (component : ∀ s : Set.Icc (0 : ℝ) T,
      SurgerySelectedComponent (F.slice s.1)) where
  terminal_mem : T ∈ F.time_domain
  time_nonnegative : 0 ≤ T
  time_subset : Set.Icc (0 : ℝ) T ⊆ F.time_domain
  surgery_times : Finset ℝ
  surgery_times_eq : (↑surgery_times : Set ℝ) =
    F.surgery_times ∩ Set.Icc 0 T
  initial_group :
    Subsingleton
      (selectedFundamentalGroup
        (component ⟨0, ⟨le_rfl, time_nonnegative⟩⟩))
  regular_group_equivalence : ∀ (a b : Set.Icc (0 : ℝ) T) (_hab : a.1 < b.1)
      (_hdisjoint : Disjoint F.surgery_times (Set.Ioc a.1 b.1)),
      Nonempty (selectedFundamentalGroup (component a) ≃*
        selectedFundamentalGroup (component b))
  event_factor : ∀ (s : Set.Icc (0 : ℝ) T)
      (hs : s.1 ∈ F.surgery_times)
      (hpost : Nonempty (F.slice s.1).carrier),
      letI := hpost
      Nonempty (RepairedGroupFactorData
        (selectedFundamentalGroup
          (component ⟨(F.event s.1 hs).tMinus,
            ⟨(F.event s.1 hs).tMinus_nonnegative,
              (F.event s.1 hs).tMinus_lt.le.trans s.2.2⟩⟩))
        (selectedFundamentalGroup (component s)))

structure RepairedGroupPersistenceData (F : SurgeryFlowData.{u}) (T : ℝ)
    (component : ∀ s : Set.Icc (0 : ℝ) T,
      SurgerySelectedComponent (F.slice s.1))
    (I : RepairedGroupPersistenceInput F T component) where
  persists : ∀ s : Set.Icc (0 : ℝ) T,
    Subsingleton (selectedFundamentalGroup (component s))

end PoincareConjecture
