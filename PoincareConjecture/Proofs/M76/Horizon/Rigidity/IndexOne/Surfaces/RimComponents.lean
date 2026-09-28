import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.SourceAnnulusMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.ComponentGroups

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "D" => closedBall (0 : Fin 1 → ℝ) 1
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem sourceBoundaryCircle_mem_component
    (phi : C(H, H)) (theta : C) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (b : D) (hb : ‖(b : Fin 1 → ℝ)‖ = 1) {S : Set X}
    (hcomponent : ∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S)
    (hbase : (sourceBoundaryCircle phi theta F b hb 0 : X) ∈ S) (c : C) :
    (sourceBoundaryCircle phi theta F b hb c : X) ∈ S := by
  let f : C → X := fun z => (sourceBoundaryCircle phi theta F b hb z : X)
  have hf : Continuous f := continuous_subtype_val.comp
    (sourceBoundaryCircle phi theta F b hb).continuous
  have hsub : range f ⊆ sourceSurface phi theta := by
    rintro _ ⟨z, rfl⟩
    exact (sourceBoundaryCircle phi theta F b hb z).property
  have hrange := (isPreconnected_range hf).subset_connectedComponentIn
    (mem_range_self (f := f) 0) hsub
  rw [hcomponent _ hbase] at hrange
  exact hrange (mem_range_self c)

noncomputable def sourceBoundaryCircleInComponent
    (phi : C(H, H)) (theta : C) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (b : D) (hb : ‖(b : Fin 1 → ℝ)‖ = 1) {S : Set X}
    (hcomponent : ∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S)
    (hbase : (sourceBoundaryCircle phi theta F b hb 0 : X) ∈ S) : C(C, S) where
  toFun c := ⟨sourceBoundaryCircle phi theta F b hb c,
    sourceBoundaryCircle_mem_component phi theta F b hb hcomponent hbase c⟩
  continuous_toFun := (continuous_subtype_val.comp
    (sourceBoundaryCircle phi theta F b hb).continuous).subtype_mk _

theorem sourceBoundaryCircleInComponent_pi1_bijective
    (phi : C(H, H)) (theta : C) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (b : D) (hb : ‖(b : Fin 1 → ℝ)‖ = 1) {S : Set X}
    (hSF : S ⊆ sourceSurface phi theta)
    (hcomponent : ∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S)
    (hbase : (sourceBoundaryCircle phi theta F b hb 0 : X) ∈ S)
    (hinj : ∀ x : sourceSurface phi theta, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) x))
    (c : C) :
    Function.Bijective (FundamentalGroup.map
      (sourceBoundaryCircleInComponent phi theta F b hb hcomponent hbase) c) := by
  apply FundamentalGroup.map_bijective_of_factor_through_whole_component hSF hcomponent
    (sourceBoundaryCircle phi theta F b hb) _ rfl c
  exact sourceBoundaryCircle_pi1_bijective_of_ambient_injective phi theta F b hb c (hinj _)

end PoincareConjecture.M76.HamiltonIntervalTorus
