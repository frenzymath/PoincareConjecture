import PoincareConjecture.Proofs.M74.Cor15_4.SchoenfliesBallSide










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

open M25.Topology3D

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)



noncomputable def schoenfliesExteriorBall
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4))
    (Ψ : StandardCapSpace → StandardCapSpace) (hΨ : ContDiff ℝ ∞ Ψ)
    (hleft : ∀ x ∈ ball 0 D.radius, Ψ (D.chart x) = x) :
    Diffeomorph (𝓡 3) (𝓡 3)
      (⟨B.closedBallᶜ, B.closedBall_closed.isOpen_compl⟩ : TopologicalSpace.Opens A.carrier)
      (⟨ball (0 : StandardCapSpace) (D.radial (1 / 2)), isOpen_ball⟩ :
        TopologicalSpace.Opens StandardCapSpace) ∞ := by
  let U : TopologicalSpace.Opens A.carrier := ⟨B.closedBallᶜ, B.closedBall_closed.isOpen_compl⟩
  let V : TopologicalSpace.Opens StandardCapSpace := ⟨ball 0 (D.radial (1 / 2)), isOpen_ball⟩
  let e := B.punctureChart d
  have hrR : D.radial (1 / 2) < D.radius := D.radial_lt _ (by norm_num)
  have hright (x : StandardCapSpace) : D.chart (Ψ x) = x := by
    obtain ⟨z, hz, rfl⟩ : x ∈ D.chart '' ball 0 D.radius := by
      rw [B.shiftedSchoenflies_chart_image_univ d D]
      trivial
    rw [hleft z hz]
  have hpre (y : U) : Ψ (e y.1) ∈ ball 0 (D.radial (1 / 2)) := by
    have hy : e y.1 ∈ D.chart '' ball 0 (D.radial (1 / 2)) := by
      rw [B.shiftedSchoenflies_original_ball_image d D]
      exact mem_image_of_mem _ y.2
    obtain ⟨z, hz, hzy⟩ := hy
    rw [← hzy, hleft z (ball_subset_ball hrR.le hz)]
    exact hz
  have hinv (x : V) : e.symm (D.chart x.1) ∈ B.closedBallᶜ := by
    have hx : D.chart x.1 ∈ e '' B.closedBallᶜ := by
      rw [← B.shiftedSchoenflies_original_ball_image d D]
      exact mem_image_of_mem _ x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← hyx, e.left_inv (B.closedBall_compl_subset_punctureChart_source d hy)]
    exact hy
  let F : U → V := fun y => ⟨Ψ (e y.1), hpre y⟩
  let G : V → U := fun x => ⟨e.symm (D.chart x.1), hinv x⟩
  refine {
    toFun := F
    invFun := G
    left_inv := ?_
    right_inv := ?_
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · intro y
    apply Subtype.ext
    change e.symm (D.chart (Ψ (e y.1))) = y.1
    rw [hright, e.left_inv (B.closedBall_compl_subset_punctureChart_source d y.2)]
  · intro x
    apply Subtype.ext
    change Ψ (e (e.symm (D.chart x.1))) = x.1
    rw [e.right_inv (by simp [e]), hleft _ (ball_subset_ball hrR.le x.2)]
  · apply (ContMDiff.subtypeVal_comp_iff V F).mp
    intro y
    have he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun y : U => e y.1) y :=
      ((B.punctureChart_contMDiffOn d).contMDiffAt
        (e.open_source.mem_nhds (B.closedBall_compl_subset_punctureChart_source d y.2))).comp y
          contMDiff_subtype_val.contMDiffAt
    exact hΨ.contMDiff.contMDiffAt.comp y he
  · apply (ContMDiff.subtypeVal_comp_iff U G).mp
    intro x
    have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun x : V => D.chart x.1) x :=
      contMDiffAt_subtype_iff.mpr
        (D.chart_smooth.contDiffAt
          (isOpen_ball.mem_nhds (ball_subset_ball hrR.le x.2))).contMDiffAt
    exact (B.punctureChart_symm_contMDiff d).contMDiffAt.comp x hc



theorem schoenfliesExteriorBall_apply
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4))
    (Ψ : StandardCapSpace → StandardCapSpace) (hΨ : ContDiff ℝ ∞ Ψ)
    (hleft : ∀ x ∈ ball 0 D.radius, Ψ (D.chart x) = x)
    (y : (⟨B.closedBallᶜ, B.closedBall_closed.isOpen_compl⟩ :
      TopologicalSpace.Opens A.carrier)) :
    (B.schoenfliesExteriorBall d D Ψ hΨ hleft y).1 = Ψ (B.punctureChart d y.1) := rfl

end PoincareConjecture.SurgeryBallEmbedding

namespace PoincareConjecture.M74



noncomputable def restrictDiffeomorphBall
    (K : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞)
    (hK : ∀ x, ‖K x‖ = ‖x‖) (R : ℝ) :
    Diffeomorph (𝓡 3) (𝓡 3)
      (⟨ball (0 : StandardCapSpace) R, isOpen_ball⟩ : TopologicalSpace.Opens StandardCapSpace)
      (⟨ball (0 : StandardCapSpace) R, isOpen_ball⟩ : TopologicalSpace.Opens StandardCapSpace)
      ∞ := by
  let U : TopologicalSpace.Opens StandardCapSpace := ⟨ball 0 R, isOpen_ball⟩
  have hi (x : StandardCapSpace) : ‖K.symm x‖ = ‖x‖ := by
    have h := hK (K.symm x)
    rw [K.apply_symm_apply] at h
    exact h.symm
  let F : U → U := fun x => ⟨K x.1, by
    change K x.1 ∈ ball 0 R
    rw [mem_ball_zero_iff, hK]
    exact mem_ball_zero_iff.mp x.2⟩
  let G : U → U := fun x => ⟨K.symm x.1, by
    change K.symm x.1 ∈ ball 0 R
    rw [mem_ball_zero_iff, hi]
    exact mem_ball_zero_iff.mp x.2⟩
  refine {
    toFun := F
    invFun := G
    left_inv := fun x => Subtype.ext (K.symm_apply_apply x.1)
    right_inv := fun x => Subtype.ext (K.apply_symm_apply x.1)
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · exact (ContMDiff.subtypeVal_comp_iff U F).mp (K.contMDiff.comp contMDiff_subtype_val)
  · exact (ContMDiff.subtypeVal_comp_iff U G).mp (K.symm.contMDiff.comp contMDiff_subtype_val)



theorem restrictDiffeomorphBall_apply
    (K : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞)
    (hK : ∀ x, ‖K x‖ = ‖x‖) (R : ℝ)
    (x : (⟨ball (0 : StandardCapSpace) R, isOpen_ball⟩ :
      TopologicalSpace.Opens StandardCapSpace)) :
    (restrictDiffeomorphBall K hK R x).1 = K x.1 := rfl



theorem restrictDiffeomorphBall_symm_apply
    (K : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞)
    (hK : ∀ x, ‖K x‖ = ‖x‖) (R : ℝ)
    (x : (⟨ball (0 : StandardCapSpace) R, isOpen_ball⟩ :
      TopologicalSpace.Opens StandardCapSpace)) :
    ((restrictDiffeomorphBall K hK R).symm x).1 = K.symm x.1 := rfl

end PoincareConjecture.M74
