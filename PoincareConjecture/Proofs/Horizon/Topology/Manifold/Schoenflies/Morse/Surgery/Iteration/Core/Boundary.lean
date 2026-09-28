import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Caps

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real}

private instance : Std.Symm (fun (D E : SphereSurgeryCoreCap v g B) =>
    Disjoint (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)) where
  symm _ _ h := h.symm

theorem closed_disk_diff_open_disk (D : SphereSurgeryCoreCap v g B) :
    D.chart '' closedBall 0 1 \ D.chart '' ball 0 1 = D.chart '' sphere (0 : E2) 1 := by
  have hc : IsClosed (D.chart '' closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn
      (D.chart.continuousOn.mono D.source)).isClosed
  rw [D.chart.image_ball_eq_interior D.source rfl, ← hc.frontier_eq,
    ← D.chart.image_sphere_eq_frontier D.source rfl]

theorem isConnected_boundary (D : SphereSurgeryCoreCap v g B) :
    IsConnected (D.chart '' sphere (0 : E2) 1) :=
  (isConnected_sphere (E := E2) (by rw [← Module.finrank_eq_rank]; norm_num)
    0 zero_le_one).image D.chart
    (D.chart.continuousOn.mono (sphere_subset_closedBall.trans D.source))

theorem isClosed_boundary (D : SphereSurgeryCoreCap v g B) :
    IsClosed (D.chart '' sphere (0 : E2) 1) :=
  ((isCompact_sphere 0 1).image_of_continuousOn
    (D.chart.continuousOn.mono (sphere_subset_closedBall.trans D.source))).isClosed

variable (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hC : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)

include hpair hC

theorem core_inter_closed_disk (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L) :
    C ∩ (D.chart '' closedBall 0 1) = D.chart '' sphere (0 : E2) 1 := by
  rw [← D.closed_disk_diff_open_disk]
  ext p
  constructor
  · rintro ⟨hpC, hpD⟩
    refine ⟨hpD, ?_⟩
    rw [hC] at hpC
    exact fun hpo => hpC (mem_iUnion_of_mem D (mem_iUnion_of_mem hD hpo))
  · rintro ⟨hpD, hpo⟩
    refine ⟨?_, hpD⟩
    rw [hC]
    rintro hp
    simp only [mem_iUnion] at hp
    obtain ⟨E, hE, hpE⟩ := hp
    by_cases heq : D = E
    · subst E
      exact hpo hpE
    · exact Set.disjoint_left.mp (hpair.forall hD hE heq) hpD
        (image_mono ball_subset_closedBall hpE)

theorem frontier_core : frontier C = ⋃ D ∈ L, D.chart '' sphere (0 : E2) 1 := by
  classical
  have hfinite : {D : SphereSurgeryCoreCap v g B | D ∈ L}.Finite := by
    simpa only [List.coe_toFinset] using L.toFinset.finite_toSet
  have hopen : IsOpen (⋃ D ∈ L, D.chart '' ball 0 1) :=
    isOpen_iUnion (fun D => isOpen_iUnion (fun _ =>
      D.chart.isOpen_image_of_subset_source isOpen_ball
        (ball_subset_closedBall.trans D.source)))
  have hclosure : closure (⋃ D ∈ L, D.chart '' ball 0 1) =
      ⋃ D ∈ L, D.chart '' closedBall 0 1 := by
    have heq := hfinite.closure_biUnion (fun D => D.chart '' ball 0 1)
    simp only [mem_ofPred_eq] at heq
    rw [heq]
    congr 2
    ext D
    rw [ParallelDisks.closure_image_ball zero_lt_one D.chart D.source]
  rw [hC, frontier_compl, hopen.frontier_eq, hclosure]
  ext p
  constructor
  · rintro ⟨hp, hpnot⟩
    simp only [mem_iUnion] at hp
    obtain ⟨D, hD, hpD⟩ := hp
    apply mem_iUnion_of_mem D
    apply mem_iUnion_of_mem hD
    apply (core_inter_closed_disk L hpair hC D hD).subset
    exact ⟨hC ▸ hpnot, hpD⟩
  · intro hp
    simp only [mem_iUnion] at hp
    obtain ⟨D, hD, hpD⟩ := hp
    have hpCD := (core_inter_closed_disk L hpair hC D hD).superset hpD
    refine ⟨mem_iUnion_of_mem D (mem_iUnion_of_mem hD hpCD.2), ?_⟩
    simpa only [hC, mem_compl_iff] using hpCD.1

theorem connectedComponentIn_frontier (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L)
    {p : S2} (hp : p ∈ D.chart '' sphere (0 : E2) 1) :
    connectedComponentIn (frontier C) p = D.chart '' sphere (0 : E2) 1 := by
  classical
  let J : Set (SphereSurgeryCoreCap v g B) := {E | E ∈ L ∧ E ≠ D}
  let V : Set S2 := ⋃ E ∈ J, E.chart '' sphere (0 : E2) 1
  have hfinite : {E : SphereSurgeryCoreCap v g B | E ∈ L}.Finite := by
    simpa only [List.coe_toFinset] using L.toFinset.finite_toSet
  have hJ : J.Finite := hfinite.subset (fun _ h => h.1)
  have hV : IsClosed V := hJ.isClosed_biUnion (fun E _ => E.isClosed_boundary)
  have hdis : Disjoint (D.chart '' sphere (0 : E2) 1) V := by
    apply Set.disjoint_left.mpr
    intro q hq hqV
    simp only [V, mem_iUnion] at hqV
    obtain ⟨E, hE, hqE⟩ := hqV
    exact Set.disjoint_left.mp (hpair.forall hD hE.1 hE.2.symm)
      (image_mono sphere_subset_closedBall hq) (image_mono sphere_subset_closedBall hqE)
  have hcover : frontier C ⊆ D.chart '' sphere (0 : E2) 1 ∪ V := by
    rw [frontier_core L hpair hC]
    intro q hq
    simp only [mem_iUnion] at hq
    obtain ⟨E, hE, hqE⟩ := hq
    by_cases heq : E = D
    · exact Or.inl (heq ▸ hqE)
    · exact Or.inr (mem_iUnion_of_mem E (mem_iUnion_of_mem ⟨hE, heq⟩ hqE))
  have hDF : D.chart '' sphere (0 : E2) 1 ⊆ frontier C := by
    rw [frontier_core L hpair hC]
    exact fun _ h => mem_iUnion_of_mem D (mem_iUnion_of_mem hD h)
  apply Subset.antisymm
  · have hK := isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (F := frontier C) (x := p))
      (D.chart '' sphere (0 : E2) 1) V D.isClosed_boundary hV
      ((connectedComponentIn_subset _ _).trans hcover)
      (by rw [hdis.inter_eq, inter_empty])
    rcases hK with hK | hK
    · exact hK
    · exact False.elim (Set.disjoint_left.mp hdis hp (hK (mem_connectedComponentIn (hDF hp))))
  · exact D.isConnected_boundary.isPreconnected.subset_connectedComponentIn hp hDF

omit hpair hC in
theorem height_eq_on_boundary (D : SphereSurgeryCoreCap v g B) :
    ∀ p ∈ D.chart '' sphere (0 : E2) 1, inner Real v (g p) = D.center := by
  rintro p ⟨x, hx, rfl⟩
  rw [D.parametrization_eq x (sphere_subset_closedBall hx)]
  exact D.boundary_height x hx

omit hpair in
theorem range_eq_core_union_caps :
    range g = g '' C ∪ ⋃ D ∈ L, D.parametrization '' closedBall 0 1 := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    by_cases hp : p ∈ C
    · exact Or.inl (mem_image_of_mem _ hp)
    · right
      rw [hC, mem_compl_iff, not_not] at hp
      simp only [mem_iUnion] at hp
      obtain ⟨D, hD, x, hx, rfl⟩ := hp
      apply mem_iUnion_of_mem D
      apply mem_iUnion_of_mem hD
      exact ⟨x, ball_subset_closedBall hx, (D.parametrization_eq x
        (ball_subset_closedBall hx)).symm⟩
  · rintro (⟨p, _, rfl⟩ | hp)
    · exact mem_range_self _
    · simp only [mem_iUnion] at hp
      obtain ⟨D, _, x, hx, rfl⟩ := hp
      exact ⟨D.chart x, D.parametrization_eq x hx⟩

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
