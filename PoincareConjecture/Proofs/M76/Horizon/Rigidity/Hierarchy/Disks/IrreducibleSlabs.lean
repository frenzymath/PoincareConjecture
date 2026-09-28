import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.IrreducibleSlabs
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ThirdCoordinateSlab








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem isPLIrreducible_hamiltonZero_third_slab_of_boundary_meeting_components
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    (phi : C(H0, H0)) {R : Set X0} (hI : IsPLIrreducible e R)
    {u v : ℝ} {a b : C0}
    (he : PLDomain e (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p u v))
    (hfront : frontier (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p u v) =
      ((R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v) ∩
        frontier R) ∪
        ((R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {a}) ∪
          (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {b})))
    (hcomponents : ∀ theta ∈ ({a, b} : Set C0),
      ∀ x ∈ R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {theta},
        (connectedComponentIn (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {theta}) x ∩
          frontier R).Nonempty) :
    IsPLIrreducible e (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p u v) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let F : Bool → Set X0 := fun side =>
    R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {if side then b else a}
  let M (i : Σ side : Bool, F side) := connectedComponentIn (F i.1) i.2
  have hMfront (i : Σ side : Bool, F side) : M i ⊆ frontier
      (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v) := by
    intro x hx
    have hxF := connectedComponentIn_subset (F i.1) i.2 hx
    rw [hfront]
    apply Or.inr
    rcases i with ⟨side, y⟩
    cases side
    · exact Or.inl hxF
    · exact Or.inr hxF
  apply hI.of_boundary_meeting_cut he inter_subset_left M hMfront
  · intro x hx hxint
    rw [hfront] at hx
    rcases hx with hxold | hxa | hxb
    · exact (hxold.2.2 hxint).elim
    · exact ⟨⟨false, ⟨x, hxa⟩⟩, mem_connectedComponentIn hxa⟩
    · exact ⟨⟨true, ⟨x, hxb⟩⟩, mem_connectedComponentIn hxb⟩
  · intro i
    exact isPreconnected_connectedComponentIn
  · rintro ⟨side, x⟩
    cases side
    · exact hcomponents a (Or.inl rfl) x x.property
    · exact hcomponents b (Or.inr rfl) x x.property

theorem isPLIrreducible_hamiltonZero_complementary_third_slabs
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    (phi : C(H0, H0)) {R : Set X0} (hI : IsPLIrreducible e R) {a b : ℝ}
    (hslabs : ∀ side : Bool,
      let N := R ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
        ((R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(a : C0)}) ∪
          (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(b : C0)})))
    (hcomponents : ∀ theta ∈ ({a, b} : Set ℝ),
      ∀ x ∈ R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(theta : C0)},
        (connectedComponentIn (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(theta : C0)}) x ∩
          frontier R).Nonempty) :
    ∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) := by
  intro side
  apply isPLIrreducible_hamiltonZero_third_slab_of_boundary_meeting_components phi hI
    (hslabs side).1 (hslabs side).2
  intro theta htheta
  rcases htheta with rfl | rfl
  · exact hcomponents a (Or.inl rfl)
  · exact hcomponents b (Or.inr rfl)

end PoincareConjecture.M76

