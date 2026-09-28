import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.OpenPartialHomeomorph.Composition











noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology

namespace Poincare.AncientVolume.ScalarRatio

variable {A B : Type*} [MetricSpace A] [MetricSpace B]
  (p : A) {R ρ : ℝ} (hR : 0 < R)
  (e : Metric.closedBall p R → B) (he : Isometry e)
  (hρ : 0 < ρ) (hρR : ρ < R)
  (hcover : Metric.ball (e ⟨p, Metric.mem_closedBall_self hR.le⟩) ρ ⊆ range e)



def ballIsometryOfClosedBallCoverage :
    Metric.ball p ρ ≃ᵢ Metric.ball (e ⟨p, Metric.mem_closedBall_self hR.le⟩) ρ := by
  let F : Metric.ball p ρ → Metric.ball (e ⟨p, Metric.mem_closedBall_self hR.le⟩) ρ :=
    fun x => ⟨e ⟨x.1, x.property.le.trans hρR.le⟩, by
      change dist (e ⟨x.1, x.property.le.trans hρR.le⟩)
        (e ⟨p, Metric.mem_closedBall_self hR.le⟩) < ρ
      rw [he.dist_eq]
      exact x.property⟩
  have hF : Isometry F := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    exact he.dist_eq _ _
  have hsur : Function.Surjective F := by
    intro y
    obtain ⟨x, hx⟩ := hcover y.property
    have hxball : x.1 ∈ Metric.ball p ρ := by
      have hd := he.dist_eq x ⟨p, Metric.mem_closedBall_self hR.le⟩
      change dist (e x) (e ⟨p, Metric.mem_closedBall_self hR.le⟩) = dist x.1 p at hd
      change dist x.1 p < ρ
      rw [← hd, hx]
      exact y.property
    exact ⟨⟨x.1, hxball⟩, Subtype.ext hx⟩
  exact { Equiv.ofBijective F ⟨hF.injective, hsur⟩ with isometry_toFun := hF }

theorem ballIsometryOfClosedBallCoverage_apply (x : Metric.ball p ρ) :
    (ballIsometryOfClosedBallCoverage p hR e he hρR hcover x).1 =
      e ⟨x.1, x.property.le.trans hρR.le⟩ := rfl


def openChartOfClosedBallCoverage : OpenPartialHomeomorph A B := by
  let S : Opens A := ⟨Metric.ball p ρ, Metric.isOpen_ball⟩
  let T : Opens B := ⟨Metric.ball (e ⟨p, Metric.mem_closedBall_self hR.le⟩) ρ, Metric.isOpen_ball⟩
  have hS : Nonempty S := ⟨⟨p, Metric.mem_ball_self hρ⟩⟩
  have hT : Nonempty T := ⟨⟨e ⟨p, Metric.mem_closedBall_self hR.le⟩, Metric.mem_ball_self hρ⟩⟩
  let F := (ballIsometryOfClosedBallCoverage p hR e he hρR hcover).toHomeomorph.toOpenPartialHomeomorph
  exact (S.openPartialHomeomorphSubtypeCoe hS).symm.trans'
    (F.trans' (T.openPartialHomeomorphSubtypeCoe hT) rfl) rfl

theorem openChartOfClosedBallCoverage_source :
    (openChartOfClosedBallCoverage p hR e he hρ hρR hcover).source = Metric.ball p ρ := by
  dsimp only [openChartOfClosedBallCoverage, OpenPartialHomeomorph.trans', PartialEquiv.trans']
  simp

theorem openChartOfClosedBallCoverage_target :
    (openChartOfClosedBallCoverage p hR e he hρ hρR hcover).target =
      Metric.ball (e ⟨p, Metric.mem_closedBall_self hR.le⟩) ρ := by
  dsimp only [openChartOfClosedBallCoverage, OpenPartialHomeomorph.trans', PartialEquiv.trans']
  simp

theorem openChartOfClosedBallCoverage_apply {x : A} (hx : x ∈ Metric.ball p ρ) :
    openChartOfClosedBallCoverage p hR e he hρ hρR hcover x =
      e ⟨x, hx.le.trans hρR.le⟩ := by
  let S : Opens A := ⟨Metric.ball p ρ, Metric.isOpen_ball⟩
  have hS : Nonempty S := ⟨⟨p, Metric.mem_ball_self hρ⟩⟩
  have hi : (S.openPartialHomeomorphSubtypeCoe hS).symm x = ⟨x, hx⟩ := by
    exact (S.openPartialHomeomorphSubtypeCoe hS).left_inv (x := ⟨x, hx⟩) (by simp)
  change (ballIsometryOfClosedBallCoverage p hR e he hρR hcover
    ((S.openPartialHomeomorphSubtypeCoe hS).symm x)).1 = _
  rw [hi]
  rfl

theorem openChartOfClosedBallCoverage_center :
    openChartOfClosedBallCoverage p hR e he hρ hρR hcover p =
      e ⟨p, Metric.mem_closedBall_self hR.le⟩ :=
  openChartOfClosedBallCoverage_apply p hR e he hρ hρR hcover (Metric.mem_ball_self hρ)

theorem openChartOfClosedBallCoverage_dist {x y : A}
    (hx : x ∈ Metric.ball p ρ) (hy : y ∈ Metric.ball p ρ) :
    dist (openChartOfClosedBallCoverage p hR e he hρ hρR hcover x)
      (openChartOfClosedBallCoverage p hR e he hρ hρR hcover y) = dist x y := by
  rw [openChartOfClosedBallCoverage_apply p hR e he hρ hρR hcover hx,
    openChartOfClosedBallCoverage_apply p hR e he hρ hρR hcover hy]
  exact he.dist_eq _ _

theorem openChartOfClosedBallCoverage_symm_dist {x y : B}
    (hx : x ∈ Metric.ball (e ⟨p, Metric.mem_closedBall_self hR.le⟩) ρ)
    (hy : y ∈ Metric.ball (e ⟨p, Metric.mem_closedBall_self hR.le⟩) ρ) :
    dist ((openChartOfClosedBallCoverage p hR e he hρ hρR hcover).symm x)
      ((openChartOfClosedBallCoverage p hR e he hρ hρR hcover).symm y) = dist x y := by
  let F := openChartOfClosedBallCoverage p hR e he hρ hρR hcover
  have hxT : x ∈ F.target := by rwa [openChartOfClosedBallCoverage_target]
  have hyT : y ∈ F.target := by rwa [openChartOfClosedBallCoverage_target]
  have hxS : F.symm x ∈ Metric.ball p ρ := by
    rw [← openChartOfClosedBallCoverage_source p hR e he hρ hρR hcover]
    exact F.map_target hxT
  have hyS : F.symm y ∈ Metric.ball p ρ := by
    rw [← openChartOfClosedBallCoverage_source p hR e he hρ hρR hcover]
    exact F.map_target hyT
  have hd := openChartOfClosedBallCoverage_dist p hR e he hρ hρR hcover hxS hyS
  change dist (F (F.symm x)) (F (F.symm y)) = dist (F.symm x) (F.symm y) at hd
  rw [F.right_inv hxT, F.right_inv hyT] at hd
  exact hd.symm

end Poincare.AncientVolume.ScalarRatio
