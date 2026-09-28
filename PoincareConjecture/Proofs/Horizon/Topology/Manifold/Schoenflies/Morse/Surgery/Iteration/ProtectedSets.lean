import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.ProtectedGerms



noncomputable section
set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace SphereSurgeryStep

variable {f : S2 -> E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)




theorem protected_preconnected_survives {K : Set S2} (hK : IsPreconnected K)
    (hfar : ∀ p ∈ K, R < |inner Real v (f p) - c|) :
    (K ⊆ S.eMinus '' ball 0 1 ∧ ∀ p ∈ K, S.fMinus =ᶠ[𝓝 p] f) ∨
      (K ⊆ S.ePlus '' ball 0 1 ∧ ∀ p ∈ K, S.fPlus =ᶠ[𝓝 p] f) := by
  have hcover : K ⊆ S.eMinus '' ball 0 1 ∪ S.ePlus '' ball 0 1 := by
    intro p hp
    exact (S.protected_point_survives (hfar p hp)).imp And.left And.left
  have hdis : Disjoint (S.eMinus '' ball 0 1) (S.ePlus '' ball 0 1) :=
    S.retained_disjoint.mono (image_mono ball_subset_closedBall)
      (image_mono ball_subset_closedBall)
  rcases hK.subset_or_subset
    (S.eMinus.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans S.eMinus_source))
    (S.ePlus.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans S.ePlus_source)) hdis hcover with hM | hP
  · refine Or.inl ⟨hM, ?_⟩
    intro p hp
    apply S.protected_minus_eventuallyEq
    rw [S.retainedMinus_eq p (image_mono ball_subset_closedBall (hM hp)),
      S.height_preserving]
    exact hfar p hp
  · refine Or.inr ⟨hP, ?_⟩
    intro p hp
    apply S.protected_plus_eventuallyEq
    rw [S.retainedPlus_eq p (image_mono ball_subset_closedBall (hP hp)),
      S.height_preserving]
    exact hfar p hp

end SphereSurgeryStep

namespace SphereSurgeryTree

variable {f : S2 -> E3} {v : E3} {A : Finset Real} {B : Set Real}


theorem eq_of_mem_leaves_of_eq_at_protected_height (tree : SphereSurgeryTree v A f)
    (hprotects : tree.Protects B) {g g' : S2 -> E3}
    (hg : g ∈ tree.leaves) (hg' : g' ∈ tree.leaves) {p q : S2}
    (hp : inner Real v (g p) ∈ B) (heq : g p = g' q) : g = g' := by
  induction tree with
  | leaf =>
    simp only [leaves, List.mem_singleton] at hg hg'
    exact hg.trans hg'.symm
  | branch hc hsep S minus plus ihM ihP =>
    have hq : inner Real v (g' q) ∈ B := heq ▸ hp
    rcases List.mem_append.mp hg with hgM | hgP <;>
      rcases List.mem_append.mp hg' with hg'M | hg'P
    · exact ihM hprotects.2.1 hgM hg'M
    · have hM := (minus.protected_germ_of_mem_leaves hprotects.2.1 hgM hp).self_of_nhds
      have hP := (plus.protected_germ_of_mem_leaves hprotects.2.2 hg'P hq).self_of_nhds
      have hMP : S.fMinus p = S.fPlus q := hM.symm.trans (heq.trans hP)
      exact (Set.disjoint_left.mp S.children_disjoint (mem_range_self p)
        ⟨q, hMP.symm⟩).elim
    · have hP := (plus.protected_germ_of_mem_leaves hprotects.2.2 hgP hp).self_of_nhds
      have hM := (minus.protected_germ_of_mem_leaves hprotects.2.1 hg'M hq).self_of_nhds
      have hMP : S.fMinus q = S.fPlus p := hM.symm.trans (heq.symm.trans hP)
      exact (Set.disjoint_left.mp S.children_disjoint (mem_range_self q)
        ⟨p, hMP.symm⟩).elim
    · exact ihP hprotects.2.2 hgP hg'P



theorem exists_protected_preconnected_set_in_leaf (tree : SphereSurgeryTree v A f)
    (hprotects : tree.Protects B) {K : Set S2} (hK : IsPreconnected K)
    (hheight : ∀ p ∈ K, inner Real v (f p) ∈ B) :
    ∃ g ∈ tree.leaves, ∀ p ∈ K, g =ᶠ[𝓝 p] f := by
  induction tree with
  | leaf hf hav => exact ⟨_, by simp [leaves], fun _ _ => Filter.EventuallyEq.rfl⟩
  | branch hc hsep S minus plus ihM ihP =>
    rcases S.protected_preconnected_survives hK
      (fun p hp => hprotects.1 _ (hheight p hp)) with ⟨_, hM⟩ | ⟨_, hP⟩
    · have hchild : ∀ p ∈ K, inner Real v (S.fMinus p) ∈ B := by
        intro p hp
        rw [(hM p hp).self_of_nhds]
        exact hheight p hp
      obtain ⟨g, hg, hgm⟩ := ihM hprotects.2.1 hchild
      exact ⟨g, List.mem_append_left _ hg, fun p hp => (hgm p hp).trans (hM p hp)⟩
    · have hchild : ∀ p ∈ K, inner Real v (S.fPlus p) ∈ B := by
        intro p hp
        rw [(hP p hp).self_of_nhds]
        exact hheight p hp
      obtain ⟨g, hg, hgp⟩ := ihP hprotects.2.2 hchild
      exact ⟨g, List.mem_append_right _ hg, fun p hp => (hgp p hp).trans (hP p hp)⟩

end SphereSurgeryTree

end Poincare.Manifold.Schoenflies
