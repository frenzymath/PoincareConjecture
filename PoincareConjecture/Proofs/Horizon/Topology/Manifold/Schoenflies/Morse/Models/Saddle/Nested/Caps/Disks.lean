import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Caps.Components
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapSlice.Region

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

def capCircle (i : Fin 3) : Set S2 :=
  ![outerSourceCircle, innerSourceCircle, height ⁻¹' {(13/10 : Real)}] i

theorem frontier_capRegion_subset (i : Fin 3) : frontier (capRegion i) ⊆ capCircle i := by
  fin_cases i
  · exact frontier_southernCap_subset
  · exact frontier_northernCap_subset
  · exact frontier_upperCap_subset

theorem capRegion_disjoint_circle (i : Fin 3) : Disjoint (capRegion i) (capCircle i) := by
  have houter : outerSourceCircle ⊆ height ⁻¹' {(1 : Real)} := by
    rw [lower_height_level_eq_sourceCircles]
    exact subset_union_left
  have hinner : innerSourceCircle ⊆ height ⁻¹' {(1 : Real)} := by
    rw [lower_height_level_eq_sourceCircles]
    exact subset_union_right
  fin_cases i
  · exact disjoint_left.mpr (fun p hp hc => (ne_of_lt hp.1) (houter hc))
  · exact disjoint_left.mpr (fun p hp hc => (ne_of_lt hp.1) (hinner hc))
  · exact disjoint_left.mpr (fun p hp hc => (ne_of_gt hp) hc)

theorem exists_smooth_capCircle (i : Fin 3) :
    ∃ γ : S1 → S2, ContMDiff (𝓡 1) (𝓡 2) ∞ γ ∧ Injective γ ∧
      (∀ x, Injective (mfderiv (𝓡 1) (𝓡 2) γ x)) ∧ range γ=capCircle i := by
  have houter : outerSourceCircle ⊆ height ⁻¹' {(1 : Real)} := by
    rw [lower_height_level_eq_sourceCircles]
    exact subset_union_left
  have hinner : innerSourceCircle ⊆ height ⁻¹' {(1 : Real)} := by
    rw [lower_height_level_eq_sourceCircles]
    exact subset_union_right
  fin_cases i
  · obtain ⟨p, hp⟩ := isConnected_outerSourceCircle.nonempty
    obtain ⟨γ, hg, hi, hd, hr⟩ := exists_smooth_circle_regularLevelComponent
      height_contMDiff 1 height_one_regular p (houter hp)
    exact ⟨γ, hg, hi, hd, hr.trans (connectedComponentIn_lower_of_mem_outer hp)⟩
  · obtain ⟨p, hp⟩ := isConnected_innerSourceCircle.nonempty
    obtain ⟨γ, hg, hi, hd, hr⟩ := exists_smooth_circle_regularLevelComponent
      height_contMDiff 1 height_one_regular p (hinner hp)
    exact ⟨γ, hg, hi, hd, hr.trans (connectedComponentIn_lower_of_mem_inner hp)⟩
  · exact exists_smooth_circle_upper_height_level

theorem exists_cap_disk_neighborhood (i : Fin 3) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      d '' closedBall 0 1=closure (capRegion i) ∧
      d '' ball 0 1=capRegion i ∧ d '' sphere (0 : E2) 1=capCircle i := by
  obtain ⟨γ, hg, hi, hd, hr⟩ := exists_smooth_capCircle i
  have hproper : closure (capRegion i) ≠ univ := by
    obtain ⟨j, hji⟩ : ∃ j : Fin 3, j ≠ i := exists_ne i
    obtain ⟨q, hq⟩ := (capRegion_connected j).nonempty
    have hdis := (capRegion_disjoint hji.symm).closure_left (capRegion_open j)
    intro heq
    exact disjoint_left.mp hdis (heq.symm ▸ mem_univ q) hq
  have hfront : frontier (closure (capRegion i)) ⊆ range γ := by
    rw [hr]
    exact frontier_closure_subset.trans (frontier_capRegion_subset i)
  have hne : (interior (closure (capRegion i)) \ range γ).Nonempty := by
    obtain ⟨p, hp⟩ := (capRegion_connected i).nonempty
    refine ⟨p, (capRegion_open i).subset_interior_iff.mpr subset_closure hp, ?_⟩
    rw [hr]
    exact disjoint_left.mp (capRegion_disjoint_circle i) hp
  obtain ⟨d, hs, hds, hdi, hclosed, hedge⟩ :=
    exists_disk_neighborhood_of_frontier_subset_circle hg hi hd isClosed_closure hproper hfront hne
  rw [hr] at hedge
  refine ⟨d, hs, hds, hdi, hclosed, ?_, hedge⟩
  apply Subset.antisymm
  · rintro p ⟨x, hx, rfl⟩
    have hxc : d x ∈ closure (capRegion i) :=
      hclosed ▸ mem_image_of_mem d (ball_subset_closedBall hx)
    by_contra hxo
    have hxf : d x ∈ frontier (capRegion i) := by
      rw [(capRegion_open i).frontier_eq]
      exact ⟨hxc, hxo⟩
    obtain ⟨y, hy, hyx⟩ := hedge.symm ▸ frontier_capRegion_subset i hxf
    have hxy := d.injOn (hs (sphere_subset_closedBall hy)) (hs (ball_subset_closedBall hx)) hyx
    rw [hxy, mem_sphere_zero_iff_norm] at hy
    have hlt := mem_ball_zero_iff.mp hx
    linarith
  · intro p hp
    obtain ⟨x, hx, hxp⟩ := hclosed.symm ▸ subset_closure hp
    refine ⟨x, mem_ball_zero_iff.mpr ?_, hxp⟩
    apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx)
    intro heq
    have hedgep : p ∈ capCircle i := by
      rw [← hedge]
      exact ⟨x, mem_sphere_zero_iff_norm.mpr heq, hxp⟩
    exact disjoint_left.mp (capRegion_disjoint_circle i) hp hedgep

end Poincare.Manifold.Schoenflies.Saddle.Nested
