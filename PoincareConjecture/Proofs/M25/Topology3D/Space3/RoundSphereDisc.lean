import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCircleDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ScaledBallChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereDiscCoordinates

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

attribute [local instance] space3_stereographic_dimension

noncomputable def roundSphereDiscChart (v : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
    OpenPartialHomeomorph E2 UnitTwoSphere :=
  (scaledBallNeighborhoodChart r hr).chart.trans (stereographic' 2 v).symm

theorem roundSphereDiscChart_source (v : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
    (roundSphereDiscChart v r hr).source = univ := by
  ext x
  change (x ∈ (univ : Set E2) ∧
    (scaledBallNeighborhoodChart r hr).chart x ∈ (stereographic' 2 v).target) ↔ x ∈ univ
  rw [stereographic'_target]
  simp

theorem roundSphereDiscChart_contMDiff (v : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
    ContMDiff 𝓘(ℝ, E2) (𝓡 2) ∞ (roundSphereDiscChart v r hr) := by
  have h : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞
      (roundSphereDiscChart v r hr) (roundSphereDiscChart v r hr).source :=
    (stereographic'_symm_contMDiff v).comp_contMDiffOn
      ((scaledBallNeighborhoodChart r hr).smooth.contMDiffOn.mono inter_subset_left)
  rw [roundSphereDiscChart_source] at h
  exact contMDiffOn_univ.mp h

theorem roundSphereDiscChart_symm_contMDiffOn (v : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ (roundSphereDiscChart v r hr).symm
      (roundSphereDiscChart v r hr).target :=
  (scaledBallNeighborhoodChart r hr).smooth_symm.contMDiffOn.comp
    ((stereographic'_contMDiffOn v).mono inter_subset_left) (fun _ hx => hx.2)

theorem roundSphereDiscChart_image_closedBall (v : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
    (roundSphereDiscChart v r hr) '' closedBall 0 1 =
      (stereographic' 2 v).symm '' closedBall 0 r := by
  change (fun x => (stereographic' 2 v).symm ((scaledBallNeighborhoodChart r hr).chart x)) ''
    closedBall 0 1 = _
  rw [← image_image (stereographic' 2 v).symm (scaledBallNeighborhoodChart r hr).chart]
  change (stereographic' 2 v).symm '' (scaledBallNeighborhoodChart r hr).closedRegion = _
  rw [scaledBallNeighborhoodChart_closedRegion]

theorem roundSphereDiscChart_image_sphere (v : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
    (roundSphereDiscChart v r hr) '' sphere 0 1 =
      (stereographic' 2 v).symm '' sphere 0 r := by
  change (fun x => (stereographic' 2 v).symm ((scaledBallNeighborhoodChart r hr).chart x)) ''
    sphere 0 1 = _
  rw [← image_image (stereographic' 2 v).symm (scaledBallNeighborhoodChart r hr).chart]
  change (stereographic' 2 v).symm '' (scaledBallNeighborhoodChart r hr).boundary = _
  rw [scaledBallNeighborhoodChart_boundary]

end PoincareConjecture.M25.Topology3D
