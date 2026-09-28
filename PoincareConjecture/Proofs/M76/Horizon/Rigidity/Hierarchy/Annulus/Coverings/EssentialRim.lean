import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.BoundaryRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Mathlib.FiniteFiberGroups
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.IntegerWinding

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem nontrivial_hamiltonZero_boundary_rim_group
    (phi : C(H0, H0)) (R : Set X0) (theta : C0)
    (hcover : IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta))
    (x : ↥(frontier R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta})) :
    Nontrivial (FundamentalGroup
      (frontier R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta} : Set X0) x) := by
  let S := frontier R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}
  have hS : IsClosed S := isClosed_frontier.inter
    (isClosed_singleton.preimage (hamiltonZeroSecondCircleMap phi).continuous)
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    (isCompact_hamiltonZeroAmbient.of_isClosed_subset hS (subset_univ _))
  let : Infinite (FundamentalGroup C0 (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta x)) :=
    (HamiltonIntervalTorus.circleFundamentalGroupEquivInt p (by norm_num) _).toEquiv.infinite_iff.mpr
      inferInstance
  exact hcover.nontrivial_fundamentalGroup_of_compact x

theorem hamiltonZero_boundary_rim_injective_and_phase_nontrivial
    (phi : C(H0, H0)) {R : Set X0} (hR : IsClosed R) (theta : C0)
    (hcover : IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta)) :
    let hsub : frontier R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta} ⊆
        R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta} :=
      inter_subset_inter_left _ hR.frontier_subset
    ∀ x : ↥(frontier R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}),
      Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hsub) x) ∧
      Nontrivial (FundamentalGroup (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta} : Set X0)
        (Set.inclusion hsub x)) := by
  intro hsub x
  have hinj : Function.Injective (FundamentalGroup.map
      ((hamiltonZeroSecondPhaseCircleMap phi R theta).comp (ContinuousMap.inclusion hsub)) x) :=
    hcover.injective_path_homotopic_map x x
  rw [FundamentalGroup.map_comp] at hinj
  have hi : Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hsub) x) :=
    Function.Injective.of_comp hinj
  let : Nontrivial (FundamentalGroup
      (frontier R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta} : Set X0) x) :=
    nontrivial_hamiltonZero_boundary_rim_group phi R theta hcover x
  exact ⟨hi, hi.nontrivial⟩

end PoincareConjecture.M76
