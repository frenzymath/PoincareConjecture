import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BoundedSide
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

open Set Metric

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [ProperSpace E] [Nontrivial E]

omit [ProperSpace E] [Nontrivial E] in
private theorem image_unitBall_interior (F : E ≃ₜ E) :
    interior (F '' closedBall (0 : E) 1) = F '' ball (0 : E) 1 := by
  rw [← F.image_interior, interior_closedBall (0 : E) (by norm_num : (1 : Real) ≠ 0)]

omit [ProperSpace E] [Nontrivial E] in
private theorem image_unitBall_frontier (F : E ≃ₜ E) :
    frontier (F '' closedBall (0 : E) 1) = F '' sphere (0 : E) 1 := by
  rw [← F.image_frontier, frontier_closedBall (0 : E) (by norm_num : (1 : Real) ≠ 0)]

omit [Nontrivial E] in

theorem isConnected_compl_image_ball (F : E ≃ₜ E) (hdim : 1 < Module.rank Real E) :
    IsConnected (F '' ball (0 : E) 1)ᶜ := by
  have hconn := F.toOpenPartialHomeomorph.isConnected_compl_image_closedBall hdim
    (by intro x _; exact mem_univ x)
  have hcl : closure (F '' closedBall (0 : E) 1)ᶜ = (F '' ball (0 : E) 1)ᶜ := by
    rw [closure_compl, image_unitBall_interior]
  rw [← hcl]
  exact hconn.closure

theorem image_closedBall_subset_image_ball_of_sphere_subset
    (F G : E ≃ₜ E) (hdim : 1 < Module.rank Real E)
    (hboundary : G '' sphere (0 : E) 1 ⊆ F '' ball (0 : E) 1) :
    G '' closedBall (0 : E) 1 ⊆ F '' ball (0 : E) 1 := by
  have hFcompact : IsCompact (F '' closedBall (0 : E) 1) :=
    (isCompact_closedBall 0 1).image F.continuous
  have hGcompact : IsCompact (G '' closedBall (0 : E) 1) :=
    (isCompact_closedBall 0 1).image G.continuous
  have hunbounded : ¬ Bornology.IsBounded (F '' ball (0 : E) 1)ᶜ := by
    intro hbound
    apply NormedSpace.unbounded_univ Real E
    have hinner := hFcompact.isBounded.subset (image_mono ball_subset_closedBall)
    simpa only [union_compl_self] using hinner.union hbound
  have hmeet : ((F '' ball (0 : E) 1)ᶜ ∩ (G '' closedBall (0 : E) 1)ᶜ).Nonempty := by
    by_contra hn
    apply hunbounded
    apply hGcompact.isBounded.subset
    intro x hx
    by_contra hxG
    exact hn ⟨x, hx, hxG⟩
  have hsub : (F '' ball (0 : E) 1)ᶜ ⊆ (G '' closedBall (0 : E) 1)ᶜ := by
    apply Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier
      hGcompact.isClosed.isOpen_compl
      (F.isConnected_compl_image_ball hdim).isPreconnected
      ?_ hmeet
    rw [frontier_compl, image_unitBall_frontier]
    exact disjoint_left.mpr (fun x hx hxG => hx (hboundary hxG))
  intro x hxG
  by_contra hxF
  exact hsub hxF hxG

omit [Nontrivial E] in
private theorem sphere_subset_ball_or_exterior
    (F G : E ≃ₜ E) (hdim : 1 < Module.rank Real E)
    (hdisjoint : Disjoint (F '' sphere (0 : E) 1) (G '' sphere (0 : E) 1)) :
    G '' sphere (0 : E) 1 ⊆ F '' ball (0 : E) 1 ∨
      G '' sphere (0 : E) 1 ⊆ (F '' closedBall (0 : E) 1)ᶜ := by
  have hK : IsClosed (F '' closedBall (0 : E) 1) :=
    ((isCompact_closedBall 0 1).image F.continuous).isClosed
  have hconn : IsPreconnected (G '' sphere (0 : E) 1) :=
    ((isConnected_sphere hdim 0 zero_le_one).image G G.continuous.continuousOn).isPreconnected
  apply hconn.subset_or_subset (F.isOpenMap _ isOpen_ball) hK.isOpen_compl
  · exact disjoint_left.mpr fun x hx hx' => hx' ((image_mono ball_subset_closedBall) hx)
  · intro x hx
    by_cases hxF : x ∈ F '' ball (0 : E) 1
    · exact Or.inl hxF
    · right
      intro hxK
      have hfront : x ∈ frontier (F '' closedBall (0 : E) 1) := by
        rw [hK.frontier_eq, image_unitBall_interior]
        exact ⟨hxK, hxF⟩
      rw [image_unitBall_frontier] at hfront
      exact disjoint_left.mp hdisjoint hfront hx

theorem disjoint_or_nested_image_closedBall
    (F G : E ≃ₜ E) (hdim : 1 < Module.rank Real E)
    (hdisjoint : Disjoint (F '' sphere (0 : E) 1) (G '' sphere (0 : E) 1)) :
    Disjoint (F '' closedBall (0 : E) 1) (G '' closedBall (0 : E) 1) ∨
      F '' closedBall (0 : E) 1 ⊆ G '' ball (0 : E) 1 ∨
      G '' closedBall (0 : E) 1 ⊆ F '' ball (0 : E) 1 := by
  rcases sphere_subset_ball_or_exterior F G hdim hdisjoint with hGin | hGout
  · exact Or.inr (Or.inr (F.image_closedBall_subset_image_ball_of_sphere_subset G hdim hGin))
  rcases sphere_subset_ball_or_exterior G F hdim hdisjoint.symm with hFin | hFout
  · exact Or.inr (Or.inl (G.image_closedBall_subset_image_ball_of_sphere_subset F hdim hFin))
  left
  have hK : IsClosed (F '' closedBall (0 : E) 1) :=
    ((isCompact_closedBall 0 1).image F.continuous).isClosed
  have hsub : G '' closedBall (0 : E) 1 ⊆ (F '' closedBall (0 : E) 1)ᶜ := by
    apply Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier hK.isOpen_compl
      ((isConnected_closedBall zero_le_one).image G G.continuous.continuousOn).isPreconnected
    · rw [frontier_compl, image_unitBall_frontier]
      exact disjoint_left.mpr (fun x hx hxF => hFout hxF hx)
    · obtain ⟨x, hx⟩ := ((isConnected_sphere hdim (0 : E) zero_le_one).image
        G G.continuous.continuousOn).nonempty
      exact ⟨x, (image_mono sphere_subset_closedBall) hx, hGout hx⟩
  exact disjoint_left.mpr fun x hxF hxG => hsub hxG hxF

end Homeomorph

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [ProperSpace E] [Nontrivial E]

theorem exists_innermost_image_closedBall
    {ι : Type*} (F : ι -> E ≃ₜ E) (hdim : 1 < Module.rank Real E)
    {s : Set ι} (hs : s.Finite) (hne : s.Nonempty)
    (hdisjoint : s.Pairwise fun i j =>
      Disjoint (F i '' sphere (0 : E) 1) (F j '' sphere (0 : E) 1)) :
    ∃ i ∈ s, ∀ j ∈ s, j ≠ i ->
      Disjoint (F i '' closedBall (0 : E) 1) (F j '' sphere (0 : E) 1) := by
  obtain ⟨i, hi, hmin⟩ := Set.Finite.exists_minimalFor
    (fun i => F i '' closedBall (0 : E) 1) s hs hne
  refine ⟨i, hi, ?_⟩
  intro j hj hji
  rcases (F i).disjoint_or_nested_image_closedBall (F j) hdim
      (hdisjoint hi hj hji.symm) with hsep | hij | hji'
  · exact hsep.mono_right (image_mono sphere_subset_closedBall)
  · apply disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨y, hy, rfl⟩ := hij hxi
    obtain ⟨z, hz, heq⟩ := hxj
    have hzy : z = y := (F j).injective heq
    subst z
    exact (ne_of_lt (mem_ball_zero_iff.mp hy)) (mem_sphere_zero_iff_norm.mp hz)
  · have hreverse := hmin hj (hji'.trans (image_mono ball_subset_closedBall))
    obtain ⟨x, hx⟩ := ((isConnected_sphere hdim (0 : E) zero_le_one).image
      (F i) (F i).continuous.continuousOn).nonempty
    have hxin := hji' (hreverse ((image_mono sphere_subset_closedBall) hx))
    obtain ⟨y, hy, rfl⟩ := hxin
    obtain ⟨z, hz, heq⟩ := hx
    have hzy : z = y := (F i).injective heq
    subst z
    exact ((ne_of_lt (mem_ball_zero_iff.mp hy)) (mem_sphere_zero_iff_norm.mp hz)).elim

end Poincare.Manifold.Schoenflies
