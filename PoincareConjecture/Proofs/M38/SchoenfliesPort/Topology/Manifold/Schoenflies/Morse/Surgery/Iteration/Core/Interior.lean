import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Boundary







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 -> E3} {B : Set Real}

theorem closed_disk_ne_univ (D : SphereSurgeryCoreCap v g B) :
    D.chart '' closedBall 0 1 ≠ univ := by
  intro heq
  have hfront := D.chart.image_sphere_eq_frontier D.source rfl
  rw [heq, frontier_univ] at hfront
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr (show (0 : Real) ≤ 1 by norm_num)
  have : D.chart x ∈ D.chart '' sphere (0 : E2) 1 := mem_image_of_mem _ hx
  simp only [hfront, mem_empty_iff_false] at this



theorem interior_core_nonempty
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hC : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ) :
    (interior C).Nonempty := by
  classical
  let V : Set S2 := ⋃ D ∈ L, D.chart '' closedBall 0 1
  have hfinite : {D : SphereSurgeryCoreCap v g B | D ∈ L}.Finite := by
    simpa only [List.coe_toFinset] using L.toFinset.finite_toSet
  have hclosed (D : SphereSurgeryCoreCap v g B) :
      IsClosed (D.chart '' closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn
      (D.chart.continuousOn.mono D.source)).isClosed
  have hV : IsClosed V := hfinite.isClosed_biUnion (fun D _ => hclosed D)
  have hproper : V ≠ univ := by
    intro hcover
    by_cases hL : L = []
    · have hempty : V = ∅ := by simp [V, hL]
      exact Set.univ_nonempty.ne_empty (hcover ▸ hempty)
    obtain ⟨D, hD⟩ := List.exists_mem_of_ne_nil L hL
    let J : Set (SphereSurgeryCoreCap v g B) := {E | E ∈ L ∧ E ≠ D}
    let W : Set S2 := ⋃ E ∈ J, E.chart '' closedBall 0 1
    have hJ : J.Finite := hfinite.subset (fun _ h => h.1)
    have hW : IsClosed W := hJ.isClosed_biUnion (fun E _ => hclosed E)
    have hdis : Disjoint (D.chart '' closedBall 0 1) W := by
      apply Set.disjoint_left.mpr
      intro p hp hpW
      simp only [W, mem_iUnion] at hpW
      obtain ⟨E, hE, hpE⟩ := hpW
      exact Set.disjoint_left.mp (hpair.forall hD hE.1 hE.2.symm) hp hpE
    have hcover' : (univ : Set S2) ⊆ D.chart '' closedBall 0 1 ∪ W := by
      intro p hp
      have hpV : p ∈ V := hcover ▸ hp
      simp only [V, mem_iUnion] at hpV
      obtain ⟨E, hE, hpE⟩ := hpV
      by_cases heq : E = D
      · exact Or.inl (heq ▸ hpE)
      · exact Or.inr (mem_iUnion_of_mem E (mem_iUnion_of_mem ⟨hE, heq⟩ hpE))
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_univ
      (D.chart '' closedBall 0 1) W (hclosed D) hW hcover'
      (by rw [hdis.inter_eq, inter_empty]) with h | h
    · exact D.closed_disk_ne_univ (Set.eq_univ_of_univ_subset h)
    · exact Set.disjoint_left.mp hdis
        (mem_image_of_mem D.chart (mem_closedBall_self zero_le_one)) (h (mem_univ _))
  have hne : Vᶜ.Nonempty := Set.nonempty_compl.mpr hproper
  apply hne.mono
  apply interior_maximal ?_ hV.isOpen_compl
  intro p hp
  rw [hC]
  intro hpo
  apply hp
  simp only [V, mem_iUnion] at hpo ⊢
  obtain ⟨D, hD, x, hx, hxp⟩ := hpo
  exact ⟨D, hD, x, ball_subset_closedBall hx, hxp⟩

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

end

end M38Schoenflies
