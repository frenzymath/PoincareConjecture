import PoincareConjecture.Proofs.M76.Wall.Mathlib.ProtectedFrontier
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

theorem piecewiseAffine_compatible_restrOpen_right
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A B : OpenPartialHomeomorph X E)
    (hAB : A.symm.trans B ∈ piecewiseAffineGroupoid E)
    {U : Set X} (hU : IsOpen U) :
    A.symm.trans (B.restrOpen U hU) ∈ piecewiseAffineGroupoid E := by
  obtain ⟨hf, hg⟩ := (mem_piecewiseAffineGroupoid_iff E _).mp hAB
  apply (mem_piecewiseAffineGroupoid_iff E _).mpr
  exact ⟨hf.mono (A.symm.trans (B.restrOpen U hU)).open_source
      (fun _ hx => ⟨hx.1, hx.2.1⟩),
    hg.mono (A.symm.trans (B.restrOpen U hU)).open_target
      (fun _ hx => ⟨hx.1.1, hx.2⟩)⟩

end OpenPartialHomeomorph

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {P R : Set X}

theorem PLDomain.inter_of_frontier_subset_interior
    (hP : PLDomain e P) (hR : PLDomain e R)
    (hB : frontier R ⊆ interior P) : PLDomain e (P ∩ R) := by
  refine ⟨hR.cover, hR.compatible, hP.closed.inter hR.closed, ?_⟩
  intro x hx
  rw [Set.frontier_inter_of_frontier_subset_interior hP.closed hR.closed hB] at hx
  rcases hx with hxR | hxP
  · obtain ⟨ell, v, B, hv, hxB, hzero, hBe, hBR⟩ := hR.halfspace x hxR
    let C := B.restrOpen (interior P) isOpen_interior
    refine ⟨ell, v, C, hv, ⟨hxB, hB hxR⟩, hzero, ?_, ?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right B (hBe i) isOpen_interior
    · intro y hy
      change (y ∈ P ∧ y ∈ R) ↔ 0 ≤ ell (B y)
      exact ⟨fun h => (hBR y hy.1).mp h.2,
        fun h => ⟨interior_subset hy.2, (hBR y hy.1).mpr h⟩⟩
  · obtain ⟨ell, v, B, hv, hxB, hzero, hBe, hBP⟩ := hP.halfspace x hxP.1
    have hxRi : x ∈ interior R :=
      Set.frontier_inter_subset_interior_of_frontier_subset_interior hB hxP
    let C := B.restrOpen (interior R) isOpen_interior
    refine ⟨ell, v, C, hv, ⟨hxB, hxRi⟩, hzero, ?_, ?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right B (hBe i) isOpen_interior
    · intro y hy
      change (y ∈ P ∧ y ∈ R) ↔ 0 ≤ ell (B y)
      exact ⟨fun h => (hBP y hy.1).mp h.1,
        fun h => ⟨(hBP y hy.1).mpr h, interior_subset hy.2⟩⟩

end PoincareConjecture.M76
