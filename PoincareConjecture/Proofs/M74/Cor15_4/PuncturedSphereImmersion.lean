import PoincareConjecture.Proofs.M74.Cor15_4.PuncturedSphereCollar
import PoincareConjecture.Proofs.M54.ConnectedSum.Coordinates
import PoincareConjecture.Proofs.M74.ServiceMirror
import PoincareConjecture.Proofs.M74.Mathlib.SphereNormalize










set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

open M74

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)

private theorem collar_radial_norm {p : RoundCylinderSpace}
    (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) : ‖(1 + p.2) • p.1.1‖ = 1 + p.2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hp.2.1]),
    mem_sphere_zero_iff_norm.mp p.1.2, mul_one]

private theorem collar_radial_ball {p : RoundCylinderSpace}
    (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) : (1 + p.2) • p.1.1 ∈ ball 0 2 := by
  rw [mem_ball_zero_iff, collar_radial_norm hp]
  linarith [hp.2.2]

private theorem collar_radial_nonzero {p : RoundCylinderSpace}
    (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) : (1 + p.2) • p.1.1 ≠ 0 := by
  apply norm_pos_iff.mp
  rw [collar_radial_norm hp]
  linarith [hp.2.1]

private theorem collar_inverse_coordinate {p : RoundCylinderSpace}
    (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
    B.inverse ((B.punctureChart d).symm (B.punctureCollar d p)) = (1 + p.2) • p.1.1 := by
  rw [punctureCollar, (B.punctureChart d).left_inv
    ((B.map_mem_punctureChart_source_iff d (collar_radial_ball hp)).mpr
      (collar_radial_nonzero hp)), B.left_inverse (collar_radial_ball hp)]



theorem punctureCollar_mfderiv_injective {p : RoundCylinderSpace}
    (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
    Function.Injective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (B.punctureCollar d) p) := by
  let c : StandardCapSpace → StandardCapSpace := fun y => B.inverse ((B.punctureChart d).symm y)
  let G : StandardCapSpace → RoundCylinderSpace := fun y =>
    (sphereNormalize p.1 (c y), ‖c y‖ - 1)
  have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c (B.punctureCollar d p) := by
    apply ContMDiffAt.comp _ _ (B.punctureChart_symm_contMDiff d).contMDiffAt
    have hsource := (B.map_mem_punctureChart_source_iff d (collar_radial_ball hp)).mpr
      (collar_radial_nonzero hp)
    change ContMDiffAt (𝓡 3) (𝓡 3) ∞ B.inverse
      ((B.punctureChart d).symm ((B.punctureChart d) (B.map ((1 + p.2) • p.1.1))))
    rw [(B.punctureChart d).left_inv hsource]
    exact B.inverse_smooth.contMDiffAt
      (B.chartRegion_open.mem_nhds (mem_image_of_mem _ (collar_radial_ball hp)))
  have hcne : c (B.punctureCollar d p) ≠ 0 := by
    rw [show c (B.punctureCollar d p) = (1 + p.2) • p.1.1 from B.collar_inverse_coordinate d hp]
    exact collar_radial_nonzero hp
  have hG : ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ G (B.punctureCollar d p) :=
    ((sphereNormalize_contMDiffAt p.1 hcne).comp _ hc).prodMk
      ((((contDiffAt_norm ℝ hcne).contMDiffAt).comp _ hc).sub contMDiffAt_const)
  have hleft : ∀ q ∈ univ ×ˢ Ioo (-1 : ℝ) 1, G (B.punctureCollar d q) = q := by
    intro q hq
    change (sphereNormalize p.1 (c (B.punctureCollar d q)), ‖c (B.punctureCollar d q)‖ - 1) = q
    rw [show c (B.punctureCollar d q) = (1 + q.2) • q.1.1 from B.collar_inverse_coordinate d hq,
      sphereNormalize_pos_smul p.1 q.1 (by linarith [hq.2.1]), collar_radial_norm hq]
    simp
  have hopen : IsOpen (univ ×ˢ Ioo (-1 : ℝ) 1 : Set RoundCylinderSpace) :=
    isOpen_univ.prod isOpen_Ioo
  have hF := (B.punctureCollar_contMDiffOn d).contMDiffAt (hopen.mem_nhds hp)
  have hevent : G ∘ B.punctureCollar d =ᶠ[𝓝 p] id :=
    Filter.eventually_of_mem (hopen.mem_nhds hp) hleft
  have hderiv := mfderiv_comp p (hG.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))
  rw [hevent.mfderiv_eq, mfderiv_id] at hderiv
  intro v w hvw
  have h := congrArg (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) G (B.punctureCollar d p)) hvw
  change ((mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) G (B.punctureCollar d p)).comp
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (B.punctureCollar d) p)) v =
    ((mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) G (B.punctureCollar d p)).comp
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (B.punctureCollar d) p)) w at h
  rw [← hderiv] at h
  exact h



theorem punctureCollar_isCollarEmbedding :
    M25.Topology3D.IsCollarEmbedding (B.punctureCollar d) :=
  ⟨B.punctureCollar_contMDiffOn d, B.punctureCollar_injOn d,
    fun _ hp => B.punctureCollar_mfderiv_injective d hp⟩

end PoincareConjecture.SurgeryBallEmbedding
