import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SecondCoordinateLifts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.Mathlib.HomotopicGroupInjection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.ComplementarySlabContraction
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.TopologicalAdapters

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

noncomputable def hamiltonZeroSecondPhaseCircleMap
    (phi : C(H0, H0)) (R : Set X0) (theta : C0) :
    C((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta} : Set X0), C0) :=
  ⟨fun x => (hamiltonZeroHierarchyCoordinates (phi (hamiltonZeroAmbientEquiv x))).1.1,
    (hamiltonZeroHierarchyCoordinates.continuous.comp
      (phi.continuous.comp (hamiltonZeroAmbientEquiv.continuous.comp continuous_subtype_val))).fst.fst⟩

theorem hamiltonZeroSecondPhaseCircleMap_ambient
    (phi : C(H0, H0)) (R : Set X0) (theta : C0)
    (x : ↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta})) :
    hamiltonZeroSecondPhaseCircleMap phi R theta x = (Q0 (hamiltonZeroAmbientMap phi x)).1.1 := by
  change _ = (hamiltonZeroHierarchyCoordinates (hamiltonZeroAmbientEquiv
    (hamiltonZeroAmbientEquiv.symm (phi (hamiltonZeroAmbientEquiv x))))).1.1
  rw [hamiltonZeroAmbientEquiv.apply_symm_apply]
  rfl

theorem hamiltonZeroSecondPhaseCircleMap_pi1_injective
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} {c alpha beta : ℝ}
    (ha : c < alpha) (hab : alpha ≤ beta) (hb : beta < c + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (theta : C0) (x : ↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta} : Set X0), X0)) x)) :
    Function.Injective (FundamentalGroup.map (hamiltonZeroSecondPhaseCircleMap phi R theta) x) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let S := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}
  let inc : C(S, X0) := ⟨Subtype.val, continuous_subtype_val⟩
  let ambient : C(X0, H0) := hamiltonZeroAmbientEquiv
  let coords : C(H0, (C0 × C0) × C0) := hamiltonZeroHierarchyCoordinates
  let f := coords.comp (phi.comp (ambient.comp inc))
  have hf : Function.Injective (FundamentalGroup.map f x) := by
    change Function.Injective (FundamentalGroup.map (coords.comp (phi.comp (ambient.comp inc))) x)
    rw [FundamentalGroup.map_comp, FundamentalGroup.map_comp, FundamentalGroup.map_comp]
    exact (hamiltonZeroHierarchyCoordinates.fundamentalGroupMulEquiv
      (phi (ambient (inc x)))).injective.comp
      ((F.fundamentalGroup_map_bijective (ambient (inc x))).1.comp
        ((hamiltonZeroAmbientEquiv.fundamentalGroupMulEquiv (inc x)).injective.comp hinj))
  obtain ⟨H, _⟩ := AddCircle.exists_shifted_closedArc_normal_contraction p ha hb
    (show alpha ∈ Icc alpha beta from ⟨le_rfl, hab⟩) f (fun y => hR y.property.1)
  let sectionMap : C(C0, (C0 × C0) × C0) :=
    ⟨fun z => ((z, theta), (alpha : C0)),
      (continuous_id.prodMk continuous_const).prodMk continuous_const⟩
  have hfactor : sectionMap.comp (hamiltonZeroSecondPhaseCircleMap phi R theta) =
      ⟨fun y => ((f y).1, (alpha : C0)), f.continuous.fst.prodMk continuous_const⟩ := by
    apply ContinuousMap.ext
    intro y
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact y.property.2.symm
    · rfl
  have hg := FundamentalGroup.map_injective_of_homotopy H.toHomotopy x hf
  rw [← hfactor, FundamentalGroup.map_comp] at hg
  exact Function.Injective.of_comp hg

theorem hamiltonZeroSecondPhaseCircleMap_pi1_injective_of_region
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} {c alpha beta : ℝ}
    (ha : c < alpha) (hab : alpha ≤ beta) (hb : beta < c + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (theta : C0)
    (hinjR : ∀ x : R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x))
    (hinjS : ∀ x : ↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}),
      Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion
        (inter_subset_left : R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta} ⊆ R)) x)) :
    ∀ x, Function.Injective (FundamentalGroup.map (hamiltonZeroSecondPhaseCircleMap phi R theta) x) := by
  intro x
  apply hamiltonZeroSecondPhaseCircleMap_pi1_injective phi F ha hab hb hR theta x
  let inclusion : C(R, X0) := ⟨Subtype.val, continuous_subtype_val⟩
  let phaseInclusion := ContinuousMap.inclusion
    (inter_subset_left : R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta} ⊆ R)
  change Function.Injective (FundamentalGroup.map (inclusion.comp phaseInclusion) x)
  rw [FundamentalGroup.map_comp]
  exact (hinjR (phaseInclusion x)).comp (hinjS x)

end PoincareConjecture.M76
