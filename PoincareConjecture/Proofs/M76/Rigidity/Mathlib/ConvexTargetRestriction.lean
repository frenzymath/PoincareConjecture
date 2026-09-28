import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false

open Set Metric

namespace OpenPartialHomeomorph

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_convex_target_avoiding (H : OpenPartialHomeomorph X E)
    {p : X} (hp : p ∈ H.source) (hzero : H p = 0)
    {S : Set X} (hS : IsClosed S) (hpS : p ∉ S) :
    ∃ G : OpenPartialHomeomorph X E,
      p ∈ G.source ∧ G p = 0 ∧ Convex ℝ G.target ∧
      G.source ⊆ H.source ∧ G.target ⊆ H.target ∧ Disjoint G.source S ∧
      (∀ x, G x = H x) ∧ ∀ y, G.symm y = H.symm y := by
  have hopen : IsOpen (H.target ∩ H.symm ⁻¹' Sᶜ) :=
    H.isOpen_inter_preimage_symm hS.isOpen_compl
  have hmem : (0 : E) ∈ H.target ∩ H.symm ⁻¹' Sᶜ := by
    have hzT : (0 : E) ∈ H.target := hzero ▸ H.map_source hp
    refine ⟨hzT, ?_⟩
    change H.symm 0 ∉ S
    rw [← hzero, H.left_inv hp]
    exact hpS
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  let G := H.trans (OpenPartialHomeomorph.ofSet (ball (0 : E) ρ) isOpen_ball)
  have hGt : G.target = ball (0 : E) ρ := by
    change ball (0 : E) ρ ∩ H.target = ball (0 : E) ρ
    exact inter_eq_left.mpr (fun y hy => (hball hy).1)
  have hpG : p ∈ G.source := by
    refine ⟨hp, ?_⟩
    change H p ∈ ball (0 : E) ρ
    rw [hzero]
    exact mem_ball_self hρ
  refine ⟨G, hpG, hzero, hGt.symm ▸ convex_ball (0 : E) ρ,
    (fun _ hx => hx.1), ?_, ?_, (fun _ => rfl), fun _ => rfl⟩
  · intro y hy
    exact (hball (hGt.subset hy)).1
  · apply disjoint_left.mpr
    intro x hx hxS
    have havoid := (hball hx.2).2
    change H.symm (H x) ∉ S at havoid
    rw [H.left_inv hx.1] at havoid
    exact havoid hxS

end OpenPartialHomeomorph
