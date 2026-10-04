import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Regions.Mathlib.ProtectedFrontier
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs

/-!
# The original halfspace charts on a protected intersection

The whole old boundary is inside the containing interior, so each
boundary chart is an open restriction of an original chart of one
factor. This retains the frozen PLDomain equations on the actual
intersection. See Hamilton 1976, Lemma 2, pp. 64--65, and M76 Wall
derivation 002. No sphere type or compression is concluded here.
-/

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

/-- An open restriction of the second chart retains compatibility
with the entire first chart. Both actual coordinate directions are
restricted to their own domains. See Wall derivation 002. -/
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

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {P R : Set X}

/-- When the containing domain protects the entire old frontier,
their literal intersection has the unchanged PL atlas and actual
halfspace charts on its full boundary. See Hamilton Lemma 2 and
Wall derivation 002. -/
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

end PoincareMT.M76
