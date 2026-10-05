import PoincareLib.Topology.Manifold.Surgery.Reduction.Assembly.SchoenfliesBallSide
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth Euclidean coordinates on a punctured sphere

Restrict the supplied Schoenflies chart to the ball whose image is the
actual surgery exterior. Mathlib's smooth open-ball parametrization gives
a genuine diffeomorphism, with controlled inverse and smoothness domains.
This is the Euclidean-coordinate step in MT Corollary 15.4(2), pp. 358-359.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.SurgeryBallEmbedding

open M25.Topology3D

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)

/-- Restrict the global service chart and use the standard smooth ball
parametrization (MT Corollary 15.4(2), pp. 358-359). The displayed inverse
is exactly the inverse supplied by the service. -/
noncomputable def puncturedSphereEuclideanOfInverse
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4))
    (Ψ : StandardCapSpace → StandardCapSpace) (hΨ : ContDiff ℝ ∞ Ψ)
    (hleft : ∀ x ∈ ball 0 D.radius, Ψ (D.chart x) = x) :
    Diffeomorph (𝓡 3) (𝓡 3)
      (⟨B.closedBallᶜ, B.closedBall_closed.isOpen_compl⟩ : TopologicalSpace.Opens A.carrier)
      StandardCapSpace ∞ := by
  let U : TopologicalSpace.Opens A.carrier := ⟨B.closedBallᶜ, B.closedBall_closed.isOpen_compl⟩
  let e := B.punctureChart d
  let r := D.radial (1 / 2)
  let b : OpenPartialHomeomorph StandardCapSpace StandardCapSpace :=
    OpenPartialHomeomorph.univBall 0 r
  have hr : 0 < r := D.radial_pos _ (by norm_num)
  have hrR : r < D.radius := D.radial_lt _ (by norm_num)
  have hbsource (x : StandardCapSpace) : x ∈ b.source := by simp [b]
  have hbtarget : b.target = ball 0 r := OpenPartialHomeomorph.univBall_target _ hr
  have hb (x : StandardCapSpace) : b x ∈ ball 0 r := by
    rw [← hbtarget]
    exact b.map_source (hbsource x)
  have hright (x : StandardCapSpace) : D.chart (Ψ x) = x := by
    obtain ⟨z, hz, rfl⟩ : x ∈ D.chart '' ball 0 D.radius := by
      rw [B.shiftedSchoenflies_chart_image_univ d D]
      trivial
    rw [hleft z hz]
  have hpre (y : U) : Ψ (e y.1) ∈ ball 0 r := by
    have hy : e y.1 ∈ D.chart '' ball 0 r := by
      rw [B.shiftedSchoenflies_original_ball_image d D]
      exact mem_image_of_mem _ y.2
    obtain ⟨z, hz, hzy⟩ := hy
    rw [← hzy, hleft z (ball_subset_ball hrR.le hz)]
    exact hz
  have hF (x : StandardCapSpace) : e.symm (D.chart (b x)) ∈ B.closedBallᶜ := by
    have hx : D.chart (b x) ∈ e '' B.closedBallᶜ := by
      rw [← B.shiftedSchoenflies_original_ball_image d D]
      exact mem_image_of_mem _ (hb x)
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← hyx, e.left_inv (B.closedBall_compl_subset_punctureChart_source d hy)]
    exact hy
  let F : StandardCapSpace → U := fun x => ⟨e.symm (D.chart (b x)), hF x⟩
  refine {
    toFun := fun y => b.symm (Ψ (e y.1))
    invFun := F
    left_inv := ?_
    right_inv := ?_
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · intro y
    apply Subtype.ext
    change e.symm (D.chart (b (b.symm (Ψ (e y.1))))) = y.1
    rw [b.right_inv (hbtarget.symm ▸ hpre y), hright,
      e.left_inv (B.closedBall_compl_subset_punctureChart_source d y.2)]
  · intro x
    change b.symm (Ψ (e (e.symm (D.chart (b x))))) = x
    rw [e.right_inv (by simp [e]), hleft _ (ball_subset_ball hrR.le (hb x)),
      b.left_inv (hbsource x)]
  · intro y
    have he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun y : U => e y.1) y :=
      ((B.punctureChart_contMDiffOn d).contMDiffAt
        (e.open_source.mem_nhds (B.closedBall_compl_subset_punctureChart_source d y.2))).comp y
          contMDiff_subtype_val.contMDiffAt
    have hbsm : ContMDiffAt (𝓡 3) (𝓡 3) ∞ b.symm (Ψ (e y.1)) :=
      (OpenPartialHomeomorph.contDiffOn_univBall_symm.contDiffAt
        (isOpen_ball.mem_nhds (hpre y))).contMDiffAt
    change ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun y : U => b.symm (Ψ (e y.1))) y
    exact hbsm.comp y (hΨ.contMDiff.contMDiffAt.comp y he)
  · apply (ContMDiff.subtypeVal_comp_iff U F).mp
    have hc : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x => D.chart (b x)) := by
      intro x
      exact (D.chart_smooth.contDiffAt
        (isOpen_ball.mem_nhds (ball_subset_ball hrR.le (hb x)))).contMDiffAt.comp x
          OpenPartialHomeomorph.contDiff_univBall.contMDiff.contMDiffAt
    exact (B.punctureChart_symm_contMDiff d).comp hc

/-- Euclidean coordinates retain the explicit service inverse formula
(MT Corollary 15.4(2), pp. 358-359). -/
theorem puncturedSphereEuclideanOfInverse_apply
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4))
    (Ψ : StandardCapSpace → StandardCapSpace) (hΨ : ContDiff ℝ ∞ Ψ)
    (hleft : ∀ x ∈ ball 0 D.radius, Ψ (D.chart x) = x)
    (y : (⟨B.closedBallᶜ, B.closedBall_closed.isOpen_compl⟩ :
      TopologicalSpace.Opens A.carrier)) :
    B.puncturedSphereEuclideanOfInverse d D Ψ hΨ hleft y =
      (OpenPartialHomeomorph.univBall (0 : StandardCapSpace) (D.radial (1 / 2))).symm
        (Ψ (B.punctureChart d y.1)) := rfl

include d in
/-- The explicit Schoenflies service supplies a genuine Euclidean
diffeomorphism of the punctured sphere (MT Corollary 15.4(2), pp. 358-359). -/
theorem nonempty_puncturedSphereEuclidean (hS : SchoenfliesService) :
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3)
      (⟨B.closedBallᶜ, B.closedBall_closed.isOpen_compl⟩ : TopologicalSpace.Opens A.carrier)
      StandardCapSpace ∞) := by
  obtain ⟨D⟩ := hS (B.shiftedPunctureCollar d) (B.shiftedPunctureCollar_isCollarEmbedding d)
    (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨Ψ, hΨ, hleft⟩ := D.chart_inverse
  rw [B.shiftedSchoenflies_chart_image_univ d D] at hΨ
  exact ⟨B.puncturedSphereEuclideanOfInverse d D Ψ (contDiffOn_univ.mp hΨ) hleft⟩

end PoincareMT.SurgeryBallEmbedding
