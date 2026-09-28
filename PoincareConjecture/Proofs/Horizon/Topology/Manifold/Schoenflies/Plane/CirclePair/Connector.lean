import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Disk
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Nesting








noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

private theorem connector_image_subset_interior_or_compl
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsClosed K)
    {β : Real → X} (hβ : ContinuousOn β (Icc 0 1))
    (havoid : Disjoint (β '' Ioo 0 1) (frontier K)) :
    β '' Ioo 0 1 ⊆ interior K ∨ β '' Ioo 0 1 ⊆ Kᶜ := by
  apply (isPreconnected_Ioo.image β (hβ.mono Ioo_subset_Icc_self)).subset_or_subset
    isOpen_interior hK.isOpen_compl
    (disjoint_left.mpr fun _ hx hy => hy (interior_subset hx))
  intro x hx
  by_cases hin : x ∈ interior K
  · exact Or.inl hin
  · right
    intro hxK
    exact disjoint_left.mp havoid hx (by rw [hK.frontier_eq]; exact ⟨hxK, hin⟩)

private theorem connector_endpoint_mem_closure
    {X : Type*} [TopologicalSpace X] {β : Real → X}
    (hβ : ContinuousOn β (Icc 0 1)) {t : Real} (ht : t ∈ Icc 0 1) :
    β t ∈ closure (β '' Ioo 0 1) := by
  have hc : closure (Ioo (0 : Real) 1) = Icc 0 1 := closure_Ioo zero_ne_one
  have hβc : ContinuousOn β (closure (Ioo 0 1)) := hc ▸ hβ
  exact hβc.image_closure (mem_image_of_mem β (hc.symm ▸ ht))

private theorem connector_image_subset_interior_of_endpoint
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsClosed K)
    {β : Real → X} (hβ : ContinuousOn β (Icc 0 1))
    (havoid : Disjoint (β '' Ioo 0 1) (frontier K))
    {t : Real} (ht : t ∈ Icc 0 1) (hmem : β t ∈ interior K) :
    β '' Ioo 0 1 ⊆ interior K := by
  rcases connector_image_subset_interior_or_compl hK hβ havoid with h | h
  · exact h
  · have hend := closure_mono h (connector_endpoint_mem_closure hβ ht)
    rw [closure_compl] at hend
    exact (hend hmem).elim

private theorem connector_image_subset_compl_of_endpoint
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsClosed K)
    {β : Real → X} (hβ : ContinuousOn β (Icc 0 1))
    (havoid : Disjoint (β '' Ioo 0 1) (frontier K))
    {t : Real} (ht : t ∈ Icc 0 1) (hmem : β t ∉ K) :
    β '' Ioo 0 1 ⊆ Kᶜ := by
  rcases connector_image_subset_interior_or_compl hK hβ havoid with h | h
  · have hend := closure_mono h (connector_endpoint_mem_closure hβ ht)
    exact (hmem ((closure_minimal interior_subset hK) hend)).elim
  · exact h




theorem exists_filled_planar_circle_pair_with_connector_region
    (γ₀ γ₁ : S1 → E2)
    (hγ₀ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ₀)
    (hγ₁ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ₁)
    (hdisjoint : Disjoint (range γ₀) (range γ₁))
    (β : Real → E2) (hβ : ContinuousOn β (Icc 0 1))
    (hβ₀ : β 0 ∈ range γ₀) (hβ₁ : β 1 ∈ range γ₁)
    (havoid : Disjoint (β '' Ioo 0 1) (range γ₀ ∪ range γ₁)) :
    ∃ A₀ A₁ : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      A₀ '' sphere (0 : E2) 1 = range γ₀ ∧
      A₁ '' sphere (0 : E2) 1 = range γ₁ ∧
      let K₀ := A₀ '' closedBall (0 : E2) 1
      let K₁ := A₁ '' closedBall (0 : E2) 1
      let U₀ := A₀ '' ball (0 : E2) 1
      let U₁ := A₁ '' ball (0 : E2) 1
      (Disjoint K₀ K₁ ∧ β '' Ioo 0 1 ⊆ (K₀ ∪ K₁)ᶜ) ∨
      (K₁ ⊆ U₀ ∧ β '' Ioo 0 1 ⊆ U₀ \ K₁) ∨
      (K₀ ⊆ U₁ ∧ β '' Ioo 0 1 ⊆ U₁ \ K₀) := by
  obtain ⟨A₀, hA₀, hK₀, hfront₀, hinterior₀⟩ :=
    exists_smooth_disk_of_smooth_circle γ₀ hγ₀
  obtain ⟨A₁, hA₁, hK₁, hfront₁, hinterior₁⟩ :=
    exists_smooth_disk_of_smooth_circle γ₁ hγ₁
  have hdim : 1 < Module.rank Real E2 := by
    rw [← Module.finrank_eq_rank]
    norm_num
  have hboundaries : Disjoint (A₀ '' sphere (0 : E2) 1)
      (A₁ '' sphere (0 : E2) 1) := by rw [hA₀, hA₁]; exact hdisjoint
  have havoid₀ : Disjoint (β '' Ioo 0 1) (frontier (A₀ '' closedBall (0 : E2) 1)) := by
    rw [hfront₀]
    exact havoid.mono_right subset_union_left
  have havoid₁ : Disjoint (β '' Ioo 0 1) (frontier (A₁ '' closedBall (0 : E2) 1)) := by
    rw [hfront₁]
    exact havoid.mono_right subset_union_right
  have hβK₀ : β 0 ∈ A₀ '' closedBall (0 : E2) 1 :=
    image_mono sphere_subset_closedBall (hA₀.symm ▸ hβ₀)
  have hβK₁ : β 1 ∈ A₁ '' closedBall (0 : E2) 1 :=
    image_mono sphere_subset_closedBall (hA₁.symm ▸ hβ₁)
  have hβU₀ : β 0 ∉ A₀ '' ball (0 : E2) 1 := by
    rw [← hinterior₀]
    have hm : β 0 ∈ frontier (A₀ '' closedBall (0 : E2) 1) := hfront₀.symm ▸ hβ₀
    exact hm.2
  have hβU₁ : β 1 ∉ A₁ '' ball (0 : E2) 1 := by
    rw [← hinterior₁]
    have hm : β 1 ∈ frontier (A₁ '' closedBall (0 : E2) 1) := hfront₁.symm ▸ hβ₁
    exact hm.2
  refine ⟨A₀, A₁, hA₀, hA₁, ?_⟩
  dsimp only
  rcases A₀.toHomeomorph.disjoint_or_nested_image_closedBall A₁.toHomeomorph hdim
      hboundaries with hsep | hnest | hnest
  · left
    have hout₀ := connector_image_subset_compl_of_endpoint hK₀.isClosed hβ havoid₀
      (t := 1) (by simp) (fun hx => disjoint_left.mp hsep hx hβK₁)
    have hout₁ := connector_image_subset_compl_of_endpoint hK₁.isClosed hβ havoid₁
      (t := 0) (by simp) (fun hx => disjoint_left.mp hsep hβK₀ hx)
    exact ⟨hsep, fun x hx hmem => hmem.elim (hout₀ hx) (hout₁ hx)⟩
  · right
    right
    have hin := connector_image_subset_interior_of_endpoint hK₁.isClosed hβ havoid₁
      (t := 0) (by simp) (hinterior₁.symm ▸ hnest hβK₀)
    have hout := connector_image_subset_compl_of_endpoint hK₀.isClosed hβ havoid₀
      (t := 1) (by simp) (fun hx => hβU₁ (hnest hx))
    exact ⟨hnest, fun x hx => ⟨hinterior₁ ▸ hin hx, hout hx⟩⟩
  · right
    left
    have hin := connector_image_subset_interior_of_endpoint hK₀.isClosed hβ havoid₀
      (t := 1) (by simp) (hinterior₀.symm ▸ hnest hβK₁)
    have hout := connector_image_subset_compl_of_endpoint hK₁.isClosed hβ havoid₁
      (t := 0) (by simp) (fun hx => hβU₀ (hnest hx))
    exact ⟨hnest, fun x hx => ⟨hinterior₀ ▸ hin hx, hout hx⟩⟩

end Poincare.Manifold.Schoenflies
