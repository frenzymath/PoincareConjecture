import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.CoordinateBounds
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.CoreSide









set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.Dehn

theorem protected_product_region_bounds
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    {U K : Set ((ι → ℝ) × (κ → ℝ))}
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hK : IsClosed K)
    (hinside : K ⊆ (closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2) \
      (closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 1))
    (houter : K ⊆ closedBall (0 : ι → ℝ) 1 ×ˢ ball (0 : κ → ℝ) 2)
    (htraceK : K ∩ (sphere (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ))) ⊆
      sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2))
    (hfront : frontier U = K ∪
      (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2))) :
    closure U ⊆ closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2 ∧
    closure U ⊆ closedBall (0 : ι → ℝ) 1 ×ˢ ball (0 : κ → ℝ) 2 ∧
    closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 1 ⊆ closure U ∧
    ((Subtype.val : (closedBall (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ))) →
      (ι → ℝ) × (κ → ℝ)) ⁻¹'
      (closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 1) ⊆
      interior (Subtype.val ⁻¹' closure U)) ∧
    closure U ∩ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ))) =
      sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2) := by
  have hfrontBounds : frontier U ⊆
      closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2 := by
    intro x hx
    rcases hfront.subset hx with hx | hx
    · exact (hinside hx).1
    · exact ⟨sphere_subset_closedBall hx.1, closedBall_subset_closedBall (by norm_num) hx.2⟩
  have hbounds := closure_subset_product_cube_of_frontier_subset
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2) hU hbounded hfrontBounds
  have hstrict := closure_subset_transverse_ball_of_frontier_subset
    (by norm_num : (0 : ℝ) < 2) hU hbounded (show frontier U ⊆
      (univ : Set (ι → ℝ)) ×ˢ ball (0 : κ → ℝ) 2 from by
      intro x hx
      rcases hfront.subset hx with hx | hx
      · exact ⟨mem_univ _, (houter hx).2⟩
      · exact ⟨mem_univ _, closedBall_subset_ball (by norm_num) hx.2⟩)
  have hUR : U ⊆ closedBall (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) :=
    fun x hx ↦ ⟨(hbounds (subset_closure hx)).1, mem_univ _⟩
  have hdis : Disjoint K
      (closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 1) :=
    Set.disjoint_left.mpr fun x hx ↦ (hinside hx).2
  have hcore : closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 1 ⊆ closure U := by
    apply product_core_subset_closure_of_frontier_patch (by norm_num) (by norm_num) hU hUR
    · apply Set.disjoint_left.mpr
      intro x hx hxcore
      rcases hfront.subset hx with hx | hx
      · exact (hinside hx).2 ⟨ball_subset_closedBall hxcore.1, ball_subset_closedBall hxcore.2⟩
      · exact (not_lt_of_ge (mem_sphere_zero_iff_norm.mp hx.1).ge)
          (mem_ball_zero_iff.mp hxcore.1)
    · refine ⟨(fun _ : ι ↦ (1 : ℝ), 0), ?_, mem_univ _, mem_ball_self (by norm_num)⟩
      apply hfront.symm.subset
      right
      constructor
      · simp
      · exact mem_closedBall_self (by norm_num)
  refine ⟨hbounds, (fun x hx ↦ ⟨(hbounds hx).1, (hstrict hx).2⟩), hcore,
    product_core_relative_interior_of_frontier_decomposition
      (by norm_num) hU hUR hK hdis hfront hcore, ?_⟩
  apply closure_old_boundary_of_frontier_trace hU hUR
  rw [hfront]
  have hRfront : frontier (closedBall (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ))) =
      sphere (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) := by
    simp only [frontier_prod_eq, frontier_univ, closure_univ,
      frontier_closedBall _ (by norm_num : (1 : ℝ) ≠ 0), prod_empty, empty_union]
  rw [hRfront]
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx.1 with hxK | hxA
    · exact htraceK ⟨hxK, hx.2⟩
    · exact hxA
  · exact fun x hx ↦ ⟨Or.inr hx, hx.1, mem_univ _⟩

end PoincareConjecture.M76.Dehn
