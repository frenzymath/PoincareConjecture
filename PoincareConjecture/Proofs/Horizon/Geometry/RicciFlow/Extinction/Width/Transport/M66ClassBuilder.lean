import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.ConstantFamily
import PoincareConjecture.Definitions.M66

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareConjecture

noncomputable def m66ClassData_of_m59_representation
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {a b : ℝ}
    (input : M65RawFlowInput M a b)
    (hab : a < b)
    (connected : IsConnected (Set.univ : Set M))
    (basepoint : M)
    (pi_two : Subsingleton (HomotopyGroup.Pi 2 M basepoint))
    (S : M59IdentificationSystem.{u})
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop basepoint))
    (hrep : M61Represents S.quotient basepoint alpha input.family)
    (loop_pi_three : HomotopyGroup.Pi 2
      (C1FreeLoopSpace (M := M)) (constantC1Loop basepoint) ≃*
      HomotopyGroup.Pi 3 M basepoint)
    (hnonzero : loop_pi_three alpha ≠ 1)
    (scalar_infimum_attained : ∀ t : Set.Icc a b, ∃ x : M,
      (input.flow.connection t.1).scalarCurvature x =
        flowScalarCurvatureInfimum input.flow t.1)
    (scalar_infimum_continuous : Continuous (fun t : Set.Icc a b =>
      flowScalarCurvatureInfimum input.flow t.1)) :
    M66ClassData input := by
  let witness := Classical.choose hrep
  let hwitness := Classical.choose_spec hrep
  let Gamma : FreeTwoSphereFamily (M := M) := witness
  have hnormalized : M59NormalizedAt S.quotient basepoint Gamma := hwitness.1
  have hclass : familySigmaClass Gamma = ⟨basepoint, alpha⟩ := hwitness.2.1
  have hhom : input.family.Homotopic (m59FamilyMap Gamma) := hwitness.2.2
  have halpha : alpha ≠ 1 := by
    intro h
    apply hnonzero
    rw [h]
    exact loop_pi_three.map_one
  have hGamma_nontrivial :
      ¬ (m59FamilyMap Gamma).Homotopic (constantLoopFamily basepoint) :=
    m67_raw_nontrivial_of_normalized_family S input.compact connected basepoint
      pi_two alpha Gamma hnormalized hclass halpha
  refine {
    strict_time := hab
    connected := connected
    basepoint := basepoint
    pi_two_subsingleton := pi_two
    raw_nontrivial := ?_
    scalar_infimum_attained := scalar_infimum_attained
    scalar_infimum_continuous := scalar_infimum_continuous }
  intro hconst
  apply hGamma_nontrivial
  exact hhom.symm.trans hconst

end PoincareConjecture
