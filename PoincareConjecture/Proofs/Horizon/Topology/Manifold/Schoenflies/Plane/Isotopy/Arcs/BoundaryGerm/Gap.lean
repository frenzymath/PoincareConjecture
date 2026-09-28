import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.Connector







noncomputable section
set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm

private theorem subset_compl_of_preconnected_gap
    {X : Type*} [TopologicalSpace X] {C G : Set X}
    (hC : IsClosed C) (hG : IsPreconnected G)
    (havoid : Disjoint G (frontier C))
    (hcontact : (closure G \ C).Nonempty) : G ⊆ Cᶜ := by
  have hsplit : G ⊆ interior C ∨ G ⊆ Cᶜ := by
    apply hG.subset_or_subset isOpen_interior hC.isOpen_compl
      (disjoint_left.mpr fun _ hx hy => hy (interior_subset hx))
    intro x hx
    by_cases hin : x ∈ interior C
    · exact Or.inl hin
    · right
      intro hxC
      exact disjoint_left.mp havoid hx (by rw [hC.frontier_eq]; exact ⟨hxC, hin⟩)
  rcases hsplit with hin | hout
  · obtain ⟨x, hxG, hxC⟩ := hcontact
    exact (hxC ((closure_minimal (hin.trans interior_subset) hC) hxG)).elim
  · exact hout



theorem preconnected_gap_subset_compl_of_disjoint_closed
    {X : Type*} [TopologicalSpace X] {C₀ C₁ G : Set X}
    (hC₀ : IsClosed C₀) (hC₁ : IsClosed C₁) (hdis : Disjoint C₀ C₁)
    (hG : IsPreconnected G)
    (havoid : Disjoint G (frontier C₀ ∪ frontier C₁))
    (hcontact₀ : (closure G ∩ C₀).Nonempty)
    (hcontact₁ : (closure G ∩ C₁).Nonempty) : G ⊆ (C₀ ∪ C₁)ᶜ := by
  have hout₀ : G ⊆ C₀ᶜ := by
    apply subset_compl_of_preconnected_gap hC₀ hG
      (havoid.mono_right subset_union_left)
    obtain ⟨x, hxG, hxC⟩ := hcontact₁
    exact ⟨x, hxG, fun hx => disjoint_left.mp hdis hx hxC⟩
  have hout₁ : G ⊆ C₁ᶜ := by
    apply subset_compl_of_preconnected_gap hC₁ hG
      (havoid.mono_right subset_union_right)
    obtain ⟨x, hxG, hxC⟩ := hcontact₀
    exact ⟨x, hxG, fun hx => disjoint_left.mp hdis hxC hx⟩
  exact fun x hx hmem => hmem.elim (hout₀ hx) (hout₁ hx)



theorem connector_image_subset_compl_of_disjoint_closed
    {X : Type*} [TopologicalSpace X] {C₀ C₁ : Set X}
    (hC₀ : IsClosed C₀) (hC₁ : IsClosed C₁) (hdis : Disjoint C₀ C₁)
    {β : Real → X} (hβ : ContinuousOn β (Icc 0 1))
    (hβ₀ : β 0 ∈ C₀) (hβ₁ : β 1 ∈ C₁)
    (havoid : Disjoint (β '' Ioo 0 1) (frontier C₀ ∪ frontier C₁)) :
    β '' Ioo 0 1 ⊆ (C₀ ∪ C₁)ᶜ := by
  have hend {t : Real} (ht : t ∈ Icc 0 1) :
      β t ∈ closure (β '' Ioo 0 1) := by
    have hc : closure (Ioo (0 : Real) 1) = Icc 0 1 := closure_Ioo zero_ne_one
    have hβc : ContinuousOn β (closure (Ioo 0 1)) := hc ▸ hβ
    exact hβc.image_closure (mem_image_of_mem β (hc.symm ▸ ht))
  exact preconnected_gap_subset_compl_of_disjoint_closed hC₀ hC₁ hdis
    (isPreconnected_Ioo.image β (hβ.mono Ioo_subset_Icc_self)) havoid
    ⟨β 0, hend (by simp), hβ₀⟩ ⟨β 1, hend (by simp), hβ₁⟩



theorem exists_closedBall_disjoint_of_preconnected_gap
    {X : Type*} [PseudoMetricSpace X] {C₀ C₁ G : Set X}
    (hC₀ : IsClosed C₀) (hC₁ : IsClosed C₁) (hdis : Disjoint C₀ C₁)
    (hG : IsPreconnected G)
    (havoid : Disjoint G (frontier C₀ ∪ frontier C₁))
    (hcontact₀ : (closure G ∩ C₀).Nonempty)
    (hcontact₁ : (closure G ∩ C₁).Nonempty) {x : X} (hx : x ∈ G) :
    ∃ r : Real, 0 < r ∧ Disjoint (closedBall x r) (C₀ ∪ C₁) := by
  have hxout := preconnected_gap_subset_compl_of_disjoint_closed
    hC₀ hC₁ hdis hG havoid hcontact₀ hcontact₁ hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hC₀.union hC₁).isOpen_compl x hxout
  refine ⟨r / 2, by positivity, disjoint_left.mpr ?_⟩
  intro y hy hyC
  exact hball (closedBall_subset_ball (by linarith : r / 2 < r) hy) hyC

end Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm
