import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCircleDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

attribute [local instance] sourceCircle_stereographic_dimension



theorem exists_sphere_disc_plane_chart
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (hclosed : closedBall (0 : E2) 1 ⊆ e.source)
    (he : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target) :
    ∃ v : UnitTwoSphere, v ∉ e '' closedBall (0 : E2) 1 ∧
      ∃ D : BallNeighborhoodChart E2 E2,
        D.chart = e.trans (stereographic' 2 v) ∧
        D.chart.source = {X : E2 | X ∈ e.source ∧ e X ≠ v} ∧
        D.chart.target = {w : E2 |
          (stereographic' 2 v).symm w ∈ e.target} ∧
        (∀ X : E2, D.chart X = stereographic' 2 v (e X)) ∧
        (∀ w : E2, D.chart.symm w =
          e.symm ((stereographic' 2 v).symm w)) ∧
        (∀ X : E2, X ∈ D.chart.source →
          (stereographic' 2 v).symm (D.chart X) = e X) ∧
        (stereographic' 2 v).symm '' D.closedRegion =
          e '' closedBall (0 : E2) 1 := by
  let θ : E2 := EuclideanSpace.single (0 : Fin 2) 1
  have hθ : ‖θ‖ = (1 : ℝ) := by simp [θ]
  have hθsource : θ ∈ e.source :=
    hclosed (mem_closedBall_zero_iff.mpr hθ.le)
  obtain ⟨δ, hδ, hδsource⟩ := Metric.isOpen_iff.mp e.open_source θ hθsource
  let X : E2 := (1 + δ / 2) • θ
  have hXnorm : ‖X‖ = 1 + δ / 2 := by
    change ‖(1 + δ / 2) • θ‖ = 1 + δ / 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith only [hδ]), hθ, mul_one]
  have hXdist : dist X θ = δ / 2 := by
    have hdifference : X - θ = (δ / 2) • θ := by
      dsimp only [X]
      rw [add_smul, one_smul]
      abel
    rw [dist_eq_norm, hdifference, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith only [hδ]), hθ, mul_one]
  have hXsource : X ∈ e.source := hδsource (by
    rw [mem_ball, hXdist]
    linarith only [hδ])
  let v : UnitTwoSphere := e X
  have hv : v ∉ e '' closedBall (0 : E2) 1 := by
    rintro ⟨Y, hY, hYv⟩
    have hYX : Y = X := e.injOn (hclosed hY) hXsource hYv
    have hYn := mem_closedBall_zero_iff.mp hY
    rw [hYX, hXnorm] at hYn
    linarith only [hYn, hδ]
  let σ := stereographic' 2 v
  have hdomain : closedBall (0 : E2) 1 ⊆ (e.trans σ).source := by
    intro Y hY
    refine ⟨hclosed hY, ?_⟩
    change e Y ∈ (stereographic' 2 v).source
    rw [stereographic'_source]
    change e Y ≠ v
    exact fun h => hv ⟨Y, hY, h⟩
  have hforward : ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E2) ∞
      (e.trans σ) (e.trans σ).source :=
    (stereographic'_contMDiffOn v).comp (he.mono inter_subset_left)
      (fun _ hY => hY.2)
  have hinverse : ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E2) ∞
      (e.trans σ).symm (e.trans σ).target :=
    hei.comp (stereographic'_symm_contMDiff v).contMDiffOn (fun _ hw => hw.2)
  let D : BallNeighborhoodChart E2 E2 := {
    chart := e.trans σ
    closedBall_subset_source := hdomain
    smooth := hforward.contDiffOn
    smooth_symm := hinverse.contDiffOn }
  have hDs : D.chart.source = {Y : E2 | Y ∈ e.source ∧ e Y ≠ v} := by
    ext Y
    change (Y ∈ e.source ∧ e Y ∈ (stereographic' 2 v).source) ↔ _
    rw [stereographic'_source]
    simp only [mem_compl_iff, mem_singleton_iff, mem_ofPred_eq]
  have hDt : D.chart.target = {w : E2 | σ.symm w ∈ e.target} := by
    ext w
    change (w ∈ (stereographic' 2 v).target ∧ σ.symm w ∈ e.target) ↔ _
    rw [stereographic'_target]
    simp only [mem_univ, true_and, mem_ofPred_eq]
  have hrecovery (Y : E2) (hY : Y ∈ D.chart.source) :
      σ.symm (D.chart Y) = e Y := σ.left_inv hY.2
  refine ⟨v, hv, D, rfl, hDs, hDt, fun _ => rfl, fun _ => rfl, hrecovery, ?_⟩
  change σ.symm '' (D.chart '' closedBall (0 : E2) 1) = _
  rw [image_image]
  apply image_congr
  intro Y hY
  exact hrecovery Y (D.closedBall_subset_source hY)

end PoincareConjecture.M25.Topology3D
