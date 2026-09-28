import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleMap









set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

theorem hamiltonZero_phase_boundary_geometry
    {E : Type*} [TopologicalSpace E]
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (K : Bool → Set E) (theta : Bool → C0)
    (H : ∀ side, K side ≃ₜ (hamiltonZeroCircleMap phi ⁻¹' {theta side} : Set X0))
    (c : Bool → E × ℝ → X0)
    (hzero : ∀ side, ∀ x : K side, c side (x, 0) = H side x)
    {R : Set X0} (hfront : frontier R = hamiltonZeroCircleMap phi ⁻¹' {theta false, theta true}) :
    (∀ side, (K side).Nonempty) ∧
      (∀ side, c side '' (K side ×ˢ ({0} : Set ℝ)) = hamiltonZeroCircleMap phi ⁻¹' {theta side}) ∧
      (c false '' (K false ×ˢ ({0} : Set ℝ))) ∪
        (c true '' (K true ×ˢ ({0} : Set ℝ))) = frontier R := by
  have hnonempty (side : Bool) : (K side).Nonempty := by
    obtain ⟨x, hx⟩ := surjective_hamiltonZeroCircleMap phi F (theta side)
    let y := (H side).symm ⟨x, hx⟩
    exact ⟨y, y.property⟩
  have himage (side : Bool) : c side '' (K side ×ˢ ({0} : Set ℝ)) =
      hamiltonZeroCircleMap phi ⁻¹' {theta side} := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      rw [ht0, hzero side ⟨x, hx⟩]
      exact (H side ⟨x, hx⟩).property
    · intro hy
      obtain ⟨x, hx⟩ := (H side).surjective ⟨y, hy⟩
      exact ⟨(x, 0), ⟨x.property, rfl⟩,
        (hzero side x).trans (congrArg Subtype.val hx)⟩
  refine ⟨hnonempty, himage, ?_⟩
  rw [himage false, himage true, hfront]
  ext x
  simp only [mem_union, mem_preimage, mem_insert_iff, mem_singleton_iff]

end PoincareConjecture.M76
