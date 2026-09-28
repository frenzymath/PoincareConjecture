import PoincareConjecture.Proofs.M36.CenteredNeckMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

open M36

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem terminalCurvature_neck_sphere_geometry (N : EpsilonNeck g) :
    ContMDiff (𝓡 2) (𝓡 3) ∞ (fun theta => N.coordinate_map (theta, 0)) ∧
      range (fun theta => N.coordinate_map (theta, 0)) = N.central_sphere ∧
      IsCompact N.central_sphere ∧ N.central_sphere.Nonempty := by
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hf : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun theta => N.coordinate_map (theta, 0)) := by
    intro theta
    exact (neck_coordinate_contMDiffAt N ⟨mem_univ _, hzero⟩).comp theta
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hrange : range (fun theta => N.coordinate_map (theta, 0)) = N.central_sphere := by
    rw [N.central_sphere_eq]
    ext x
    constructor
    · rintro ⟨theta, rfl⟩
      exact ⟨(theta, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨theta, s⟩, hs, rfl⟩
      have h0 : s = 0 := hs.2
      exact ⟨theta, by rw [h0]⟩
  refine ⟨hf, hrange, ?_, ⟨N.center, N.center_on_central_sphere⟩⟩
  rw [← hrange]
  exact isCompact_range hf.continuous

theorem terminalCurvature_neck_sphere_horizontal
    (N : EpsilonNeck g) (theta : UnitTwoSphere)
    (v : EuclideanSpace ℝ (Fin 3)) (hv : cylinderHeightCovector v = 0) :
    mfderiv (𝓡 2) (𝓡 3) (fun theta => N.coordinate_map (theta, 0)) theta
      (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) theta).symm 0
        (cylinderHorizontalProjection v)) =
      mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 v := by
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hmap := (neck_coordinate_contMDiffAt N (z := (theta, 0))
    ⟨mem_univ theta, hzero⟩).mdifferentiableAt
    (by simp)
  have hinc : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun theta : UnitTwoSphere => (theta, (0 : ℝ))) theta :=
    ((contMDiff_id (n := ∞)).prodMk contMDiff_const).mdifferentiableAt (by simp)
  have hd := mfderiv_comp theta hmap hinc
  have hi := mfderiv_prodMk
    (mdifferentiableAt_id (I := 𝓡 2) (x := theta))
    (mdifferentiableAt_const (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) (x := theta) (c := (0 : ℝ)))
  rw [mfderiv_id, mfderiv_const] at hi
  simp only [id_eq] at hi
  rw [hi] at hd
  rw [centeredNeckLift_mfderiv N theta 0 (zero_mem_centeredNeckDomain N hzero),
    centeredCylinderLift_zero, map_zero, hv]
  change (mfderiv (𝓡 2) (𝓡 3)
    (N.coordinate_map ∘ fun theta : UnitTwoSphere => (theta, (0 : ℝ))) theta) _ = _
  rw [hd]
  rfl

end PoincareConjecture.M47
