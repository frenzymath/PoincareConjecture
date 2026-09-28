import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CollaredDomain
import PoincareConjecture.Proofs.Horizon.Topology.Maps.OpenPartialHomeomorph.Compact

noncomputable section
set_option autoImplicit false

open Set PoincareConjecture
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem ball_neighborhood_in_coordinates
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
    (e : OpenPartialHomeomorph M E3) (het : e.target = univ)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hregular : closure (interior K) = K)
    (c : OpenPartialHomeomorph RoundCylinderSpace M)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hcs : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hct : c.target ⊆ e.source)
    (hfront : frontier K = range (fun q : UnitTwoSphere => c (q, 0)))
    (hside : ∀ y ∈ c.target, y ∈ K ↔ 0 ≤ (c.symm y).2) :
    ∃ b : OpenPartialHomeomorph E3 M,
      Metric.closedBall 0 1 ⊆ b.source ∧ b.target ⊆ e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.closedBall 0 1 = K := by
  let L := e '' K
  have hL : IsCompact L := hK.image_of_continuousOn (e.continuousOn.mono hKs)
  have himage : e.IsImage K L := e.isImage_image_of_subset_source hKs
  have hLi : interior L = e '' interior K := by
    have h := himage.interior.image_eq
    rw [inter_eq_right.mpr (interior_subset.trans hKs), het, univ_inter] at h
    exact h.symm
  have hLregular : closure (interior L) = L := by
    rw [hLi]
    obtain ⟨_, _, hclosure, _⟩ := e.image_region_of_isCompact_closure
      isOpen_interior (hregular.symm ▸ hK) (hregular.symm ▸ hKs)
    simpa only [hregular] using hclosure
  have hLf : frontier L = e '' frontier K := by
    have h := himage.frontier.image_eq
    rw [inter_eq_right.mpr (hK.isClosed.frontier_subset.trans hKs), het, univ_inter] at h
    exact h.symm
  let j := c.trans e
  have hjs : univ ×ˢ Ioo (-δ) δ ⊆ j.source := by
    intro z hz
    exact ⟨hcs hz, hct (c.map_source (hcs hz))⟩
  have hjf : frontier L = range (fun q : UnitTwoSphere => j (q, 0)) := by
    rw [hLf, hfront, ← range_comp]
    rfl
  have hjside (y : E3) (hy : y ∈ j.target) : y ∈ L ↔ 0 ≤ (j.symm y).2 := by
    rw [← himage.symm_apply_mem_iff hy.1]
    exact hside _ hy.2
  obtain ⟨f, hfs, _, hf, hfi, hfL⟩ := ball_neighborhood_of_compact_collar_side
    hL hLregular j (he.comp (hc.mono inter_subset_left) inter_subset_right)
    (hci.comp (hei.mono inter_subset_left) inter_subset_right) hδ hjs hjf hjside
  let b := f.trans e.symm
  have hbs : Metric.closedBall (0 : E3) 1 ⊆ b.source := by
    intro x hx
    refine ⟨hfs hx, ?_⟩
    change f x ∈ e.target
    rw [het]
    exact mem_univ _
  refine ⟨b, hbs, inter_subset_left,
    hei.comp (hf.mono inter_subset_left) inter_subset_right,
    hfi.comp (he.mono inter_subset_left) inter_subset_right, ?_⟩
  change (e.symm ∘ f) '' Metric.closedBall 0 1 = K
  rw [image_comp, hfL]
  exact e.toPartialEquiv.symm_image_image_of_subset_source hKs

end Poincare.Manifold.Schoenflies
