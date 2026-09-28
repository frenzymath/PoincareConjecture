import PoincareConjecture.Proofs.M76.Triangulation.HamiltonOriginalChartBall
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
  {α : Type*}

local notation "X" => LatticeHandleAmbient ι κ L
local notation "R" => latticeHandleDomain ι κ L
local notation "V3" => (Fin 3 → ℝ)

omit [DiscreteTopology L] in

theorem HamiltonDehnEnclosingRegion.interior_nonempty
    {e : α → OpenPartialHomeomorph X V3} {T : Set X}
    (region : HamiltonDehnEnclosingRegion ι κ L e T) :
    (interior region.region).Nonempty := by
  let z : X := (0, QuotientAddGroup.mk (0 : κ → ℝ))
  have hzR : z ∈ R := ⟨mem_closedBall_self zero_le_one, mem_univ _⟩
  have hzCore : z ∈ hamiltonHandleBlock ι κ L 1 :=
    ⟨(0, 0), ⟨mem_closedBall_self zero_le_one, mem_closedBall_self zero_le_one⟩, rfl⟩
  have hzIntR : z ∈ interior R := by
    rw [latticeHandleDomain, interior_prod_eq, interior_univ,
      interior_closedBall _ one_ne_zero]
    exact ⟨mem_ball_self zero_lt_one, mem_univ _⟩
  have hzRel : (⟨z, hzR⟩ : R) ∈
      interior ((Subtype.val : R → X) ⁻¹' region.region) :=
    region.core_relative_interior hzCore
  obtain ⟨O, hO, hrel⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior ((Subtype.val : R → X) ⁻¹' region.region)))
  have hzO : z ∈ O := by
    change (⟨z, hzR⟩ : R) ∈ (Subtype.val : R → X) ⁻¹' O
    rwa [hrel]
  have hOD : O ∩ interior R ⊆ region.region := by
    intro x hx
    have hxRel : (⟨x, interior_subset hx.2⟩ : R) ∈
        interior ((Subtype.val : R → X) ⁻¹' region.region) := by
      rw [← hrel]
      exact hx.1
    exact (interior_subset hxRel :
      (⟨x, interior_subset hx.2⟩ : R) ∈ (Subtype.val : R → X) ⁻¹' region.region)
  exact ⟨z, interior_mono hOD ((hO.inter isOpen_interior).interior_eq.symm ▸ ⟨hzO, hzIntR⟩)⟩

theorem HamiltonDehnEnclosingRegion.markedProtectedBall
    {e : α → OpenPartialHomeomorph X V3} {T : Set X}
    (region : HamiltonDehnEnclosingRegion ι κ L e T)
    (he : PLDomain e R)
    (h : OpenPartialHomeomorph ((ι → ℝ) × (κ → ℝ)) V3)
    (retained : HamiltonRetainedBlockChart ι κ L e h)
    (hindex : Fintype.card ι = 1 ∨ Fintype.card ι = 2) :
    Nonempty (HamiltonMarkedProtectedBall ι κ L e region.region) := by
  have hchart : region.region ⊆ (e retained.index).source := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := region.subset_outer hy
    exact retained.contains x hx
  obtain ⟨ball⟩ := region.sphere.ball_of_original_chart he.compatible region.compact
    region.interior_nonempty retained.index hchart
  refine ⟨{
    ball := ball
    subset_domain := ?_
    position := Or.inr ⟨hindex, region.core_subset, region.subset_outer,
      region.subset_outer_open, region.core_relative_interior, region.old_boundary_eq⟩
  }⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := region.subset_outer hy
  exact ⟨hx.1, mem_univ _⟩

end PoincareConjecture.M76
