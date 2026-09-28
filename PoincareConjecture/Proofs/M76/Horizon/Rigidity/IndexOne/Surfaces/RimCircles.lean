import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.EssentialRims
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.General.LatticeHandleBoundaryGroups



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

def originalIntervalEndpoint (side : Bool) : D :=
  ⟨fun _ => if side then 1 else -1, by cases side <;> simp⟩

theorem originalIntervalEndpoint_norm (side : Bool) :
    ‖(originalIntervalEndpoint side : Fin 1 → ℝ)‖ = 1 := by
  cases side <;> simp [originalIntervalEndpoint]

theorem originalIntervalEndpoint_injective : Function.Injective originalIntervalEndpoint := by
  intro a b h
  have h0 := congrArg (fun z : D => z.val 0) h
  cases a <;> cases b
  · rfl
  · norm_num [originalIntervalEndpoint] at h0
  · norm_num [originalIntervalEndpoint] at h0
  · rfl

theorem eq_originalIntervalEndpoint (b : D) (hb : ‖(b : Fin 1 → ℝ)‖ = 1) :
    ∃ side, b = originalIntervalEndpoint side := by
  have hconst : (b : Fin 1 → ℝ) = fun _ => b.val 0 := by
    funext i
    exact congrArg b.val (Subsingleton.elim i 0)
  have hn : |b.val 0| = 1 := by
    rw [hconst, pi_norm_const, Real.norm_eq_abs] at hb
    exact hb
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with hp | hm
  · refine ⟨true, Subtype.ext ?_⟩
    simpa [originalIntervalEndpoint, hp] using hconst
  · refine ⟨false, Subtype.ext ?_⟩
    simpa [originalIntervalEndpoint, hm] using hconst

def sourceRimCircle (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (b : D) :
    Set ↥(sourceSurface phi theta ∩ frontier R) :=
  {x | ((sourceRimCoordinates phi theta F x : D × C)).1 = b}

theorem sourceRimCircle_isClopen (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (b : D) :
    IsClopen (sourceRimCircle phi theta F b) := by
  let E := {a : D | ‖(a : Fin 1 → ℝ)‖ = 1}
  let : Finite E := (finite_unit_rim_of_card_eq_one (by simp : Fintype.card (Fin 1) = 1)).to_subtype
  let : DiscreteTopology E := Finite.instDiscreteTopology
  let label : ↥(sourceSurface phi theta ∩ frontier R) → E := fun x =>
    ⟨(sourceRimCoordinates phi theta F x).val.1,
      (sourceRimCoordinates phi theta F x).property⟩
  have hc : Continuous label := by fun_prop
  exact (isClopen_discrete {a : E | (a : D) = b}).preimage hc


noncomputable def sourceRimCircleCoordinates (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (b : D)
    (hb : ‖(b : Fin 1 → ℝ)‖ = 1) : C ≃ₜ sourceRimCircle phi theta F b where
  toFun c := ⟨(sourceRimCoordinates phi theta F).symm ⟨(b, c), hb⟩, by
    simp [sourceRimCircle]⟩
  invFun x := (sourceRimCoordinates phi theta F x.val).val.2
  left_inv c := by simp
  right_inv x := by
    apply Subtype.ext
    apply (sourceRimCoordinates phi theta F).injective
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    exact Prod.ext x.property.symm rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem sourceRimCircleCoordinates_original_point (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (b : D)
    (hb : ‖(b : Fin 1 → ℝ)‖ = 1) (c : C) :
    ((sourceRimCircleCoordinates phi theta F b hb c).val : X) =
      (sourceBoundaryCircle phi theta F b hb c : X) := rfl

theorem sourceRimCircle_disjoint (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) {b b' : D} (hbb : b ≠ b') :
    Disjoint (sourceRimCircle phi theta F b) (sourceRimCircle phi theta F b') := by
  apply disjoint_left.mpr
  intro x hx hx'
  exact hbb (hx.symm.trans hx')

theorem sourceRimCircle_cover (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    (⋃ b : {a : D | ‖(a : Fin 1 → ℝ)‖ = 1}, sourceRimCircle phi theta F b.val) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨⟨(sourceRimCoordinates phi theta F x).val.1,
    (sourceRimCoordinates phi theta F x).property⟩, rfl⟩

theorem sourceRimCircle_two_cover (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    (⋃ side : Bool, sourceRimCircle phi theta F (originalIntervalEndpoint side)) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨side, hside⟩ := eq_originalIntervalEndpoint
    (sourceRimCoordinates phi theta F x).val.1
    (sourceRimCoordinates phi theta F x).property
  exact mem_iUnion.mpr ⟨side, hside⟩

theorem sourceRimCircle_two_disjoint (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    Pairwise (fun a b : Bool => Disjoint
      (sourceRimCircle phi theta F (originalIntervalEndpoint a))
      (sourceRimCircle phi theta F (originalIntervalEndpoint b))) := by
  intro a b hab
  exact sourceRimCircle_disjoint phi theta F (fun h => hab
    (originalIntervalEndpoint_injective h))

end PoincareConjecture.M76.HamiltonIntervalTorus
