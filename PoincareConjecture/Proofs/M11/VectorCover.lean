import Mathlib.Geometry.Manifold.VectorBundle.Basic





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ p, TopologicalSpace (E p)]
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]

noncomputable def linearPretrivialization (U : TopologicalSpace.Opens B)
    (e : ∀ p, p ∈ U → E p ≃L[ℝ] F) : Pretrivialization F (π F E) := by
  classical
  exact {
    toFun v := (v.proj, if h : v.proj ∈ U then e v.proj h v.2 else 0)
    invFun v := TotalSpace.mk' F v.1 (if h : v.1 ∈ U then (e v.1 h).symm v.2 else 0)
    source := (π F E) ⁻¹' U
    target := (U : Set B) ×ˢ univ
    map_source' := fun _ h ↦ ⟨h, mem_univ _⟩
    map_target' := fun _ h ↦ h.1
    left_inv' := by
      rintro ⟨p, v⟩ hp
      have hp' : p ∈ U := hp
      change TotalSpace.mk' F p
        (if h : p ∈ U then (e p h).symm (if h : p ∈ U then e p h v else 0) else 0) =
          TotalSpace.mk' F p v
      simp only [dif_pos hp', ContinuousLinearEquiv.symm_apply_apply]
    right_inv' := by
      rintro ⟨p, v⟩ hp
      have hp' : p ∈ U := hp.1
      change (p, if h : p ∈ U then e p h (if h : p ∈ U then (e p h).symm v else 0)
        else 0) = (p, v)
      simp only [dif_pos hp', ContinuousLinearEquiv.apply_symm_apply]
    open_target := U.isOpen.prod isOpen_univ
    baseSet := U
    open_baseSet := U.isOpen
    source_eq := rfl
    target_eq := rfl
    proj_toFun := fun _ _ ↦ rfl
  }

theorem linearPretrivialization_apply (U : TopologicalSpace.Opens B)
    (e : ∀ p, p ∈ U → E p ≃L[ℝ] F) (p : B) (hp : p ∈ U) (v : E p) :
    linearPretrivialization U e (TotalSpace.mk' F p v) = (p, e p hp v) := by
  classical
  change (p, if h : p ∈ U then e p h v else 0) = (p, e p hp v)
  rw [dif_pos hp]

theorem linearPretrivialization_symm (U : TopologicalSpace.Opens B)
    (e : ∀ p, p ∈ U → E p ≃L[ℝ] F) (p : B) (hp : p ∈ U) (v : F) :
    (linearPretrivialization U e).symm p v = (e p hp).symm v := by
  classical
  rw [Pretrivialization.symm_apply _ hp]
  change (if h : p ∈ U then (e p h).symm v else 0) = (e p hp).symm v
  rw [dif_pos hp]

theorem linearPretrivialization_isLinear (U : TopologicalSpace.Opens B)
    (e : ∀ p, p ∈ U → E p ≃L[ℝ] F) :
    (linearPretrivialization U e).IsLinear ℝ := by
  constructor
  intro p hp
  change p ∈ U at hp
  have heq : (fun v : E p ↦ (linearPretrivialization U e ⟨p, v⟩).2) = e p hp := by
    funext v
    rw [linearPretrivialization_apply U e p hp]
  rw [heq]
  exact (e p hp).toLinearMap.isLinear

theorem linearPretrivialization_isInducing (U : TopologicalSpace.Opens B)
    (e : ∀ p, p ∈ U → E p ≃L[ℝ] F) (p : B) (hp : p ∈ U) :
    Topology.IsInducing (linearPretrivialization U e ∘ TotalSpace.mk' F p) := by
  have heq : linearPretrivialization U e ∘ TotalSpace.mk' F p =
      (fun v : E p ↦ (p, e p hp v)) :=
    funext (linearPretrivialization_apply U e p hp)
  rw [heq, Topology.isInducing_const_prod]
  exact (e p hp).toHomeomorph.isInducing

variable {ι : Type*}
  (U : ι → TopologicalSpace.Opens B) (e : ∀ i p, p ∈ U i → E p ≃L[ℝ] F)
  (hc : ∀ p : B, ∃ i, p ∈ U i) (L : ι → ι → B → F →L[ℝ] F)
  (hL : ∀ i j, ContinuousOn (L i j) ((U i : Set B) ∩ U j))
  (hcompat : ∀ i j p (hp : p ∈ (U i : Set B) ∩ U j) v,
    L i j p v = e j p hp.2 ((e i p hp.1).symm v))

noncomputable def linearVectorPrebundle : VectorPrebundle ℝ F E where
  pretrivializationAtlas := range (fun i ↦ linearPretrivialization (U i) (e i))
  pretrivialization_linear' := by
    rintro _ ⟨i, rfl⟩
    exact linearPretrivialization_isLinear (U i) (e i)
  pretrivializationAt p := linearPretrivialization (U (Classical.choose (hc p)))
    (e (Classical.choose (hc p)))
  mem_base_pretrivializationAt p := Classical.choose_spec (hc p)
  pretrivialization_mem_atlas p := ⟨Classical.choose (hc p), rfl⟩
  exists_coordChange := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    refine ⟨L i j, hL i j, ?_⟩
    intro p hp v
    rw [linearPretrivialization_symm (U i) (e i) p hp.1,
      linearPretrivialization_apply (U j) (e j) p hp.2]
    exact hcompat i j p hp v
  totalSpaceMk_isInducing p :=
    linearPretrivialization_isInducing _ _ p (Classical.choose_spec (hc p))

theorem linearVectorPrebundle_smooth
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ V H} [ChartedSpace H B]
    (hs : ∀ i j, ContMDiffOn J 𝓘(ℝ, F →L[ℝ] F) ∞ (L i j) ((U i : Set B) ∩ U j)) :
    (linearVectorPrebundle U e hc L hL hcompat).IsContMDiff J ∞ := by
  constructor
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  refine ⟨L i j, hs i j, ?_⟩
  intro p hp v
  rw [linearPretrivialization_symm (U i) (e i) p hp.1,
    linearPretrivialization_apply (U j) (e j) p hp.2]
  exact hcompat i j p hp v

end PoincareConjecture.Proofs.M11
