import PoincareConjecture.Proofs.M36.StandardBalls
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

abbrev SurgeryBall (g₀ : StandardInitialMetric) (L : ℝ) :=
  ULift.{u} (Metric.ball (0 : StandardCapSpace) (radialEuclideanRadius g₀ L))

def surgeryBallInclusion (g₀ : StandardInitialMetric) (L : ℝ)
    (y : SurgeryBall.{u} g₀ L) : StandardCapSpace := y.down.val

theorem surgeryBallInclusion_isOpenEmbedding (g₀ : StandardInitialMetric) (L : ℝ) :
    Topology.IsOpenEmbedding (surgeryBallInclusion.{u} g₀ L) :=
  Metric.isOpen_ball.isOpenEmbedding_subtypeVal.comp Homeomorph.ulift.isOpenEmbedding

noncomputable instance surgeryBallChartedSpace (g₀ : StandardInitialMetric) (L : ℝ)
    [Nonempty (SurgeryBall.{u} g₀ L)] :
    ChartedSpace StandardCapSpace (SurgeryBall.{u} g₀ L) :=
  (surgeryBallInclusion_isOpenEmbedding g₀ L).singletonChartedSpace

instance surgeryBallIsManifold (g₀ : StandardInitialMetric) (L : ℝ)
    [Nonempty (SurgeryBall.{u} g₀ L)] :
    IsManifold (𝓡 3) ∞ (SurgeryBall.{u} g₀ L) :=
  (surgeryBallInclusion_isOpenEmbedding g₀ L).isManifold_singleton

instance surgeryBallSecondCountable (g₀ : StandardInitialMetric) (L : ℝ) :
    SecondCountableTopology (SurgeryBall.{u} g₀ L) :=
  Homeomorph.ulift.secondCountableTopology

noncomputable def surgeryBallCarrier (g₀ : StandardInitialMetric) (L : ℝ)
    [Nonempty (SurgeryBall.{u} g₀ L)] :
    GeneralizedSliceCarrier.{u} where
  carrier := SurgeryBall.{u} g₀ L
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance

noncomputable def surgeryBallTip (g₀ : StandardInitialMetric) {L : ℝ} (hL : 0 < L) :
    SurgeryBall.{u} g₀ L :=
  ⟨⟨0, Metric.mem_ball_self ((radialEuclideanRadius_pos_iff g₀ L).mpr hL)⟩⟩

@[simp]
theorem surgeryBallInclusion_tip (g₀ : StandardInitialMetric) {L : ℝ} (hL : 0 < L) :
    surgeryBallInclusion g₀ L (surgeryBallTip.{u} g₀ hL) = 0 := rfl

theorem surgeryBallInclusion_range (g₀ : StandardInitialMetric) (L : ℝ) :
    Set.range (surgeryBallInclusion.{u} g₀ L) =
      Metric.ball 0 (radialEuclideanRadius g₀ L) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.down.property
  · intro hx
    exact ⟨⟨⟨x, hx⟩⟩, rfl⟩

theorem surgeryBallInclusion_radial_lt (g₀ : StandardInitialMetric) (L : ℝ)
    (y : SurgeryBall.{u} g₀ L) :
    radialArclength g₀ ‖surgeryBallInclusion g₀ L y‖ < L := by
  have hy : ‖surgeryBallInclusion g₀ L y‖ < radialEuclideanRadius g₀ L := by
    simpa only [Metric.mem_ball, dist_zero_right, surgeryBallInclusion] using y.down.property
  simpa only [radialArclength_euclideanRadius] using radialArclength_strictMono g₀ hy

theorem surgeryBallInclusion_contMDiff (g₀ : StandardInitialMetric)
    (L : ℝ) [Nonempty (SurgeryBall.{u} g₀ L)] :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (surgeryBallInclusion.{u} g₀ L) :=
  contMDiff_isOpenEmbedding (surgeryBallInclusion_isOpenEmbedding g₀ L)

noncomputable def surgeryBallChart (g₀ : StandardInitialMetric) (L : ℝ)
    [Nonempty (SurgeryBall.{u} g₀ L)] :
    StandardCapSpace → SurgeryBall.{u} g₀ L :=
  (surgeryBallInclusion_isOpenEmbedding g₀ L).toOpenPartialHomeomorph
    (surgeryBallInclusion g₀ L) |>.symm

theorem surgeryBallChart_left_inverse (g₀ : StandardInitialMetric) (L : ℝ)
    [Nonempty (SurgeryBall.{u} g₀ L)] :
    Function.LeftInverse (surgeryBallChart.{u} g₀ L) (surgeryBallInclusion g₀ L) :=
  fun _ => (surgeryBallInclusion_isOpenEmbedding g₀ L).toOpenPartialHomeomorph_left_inv _

theorem surgeryBallChart_right_inverse (g₀ : StandardInitialMetric) (L : ℝ)
    [Nonempty (SurgeryBall.{u} g₀ L)]
    {x : StandardCapSpace} (hx : x ∈ Metric.ball 0 (radialEuclideanRadius g₀ L)) :
    surgeryBallInclusion g₀ L (surgeryBallChart.{u} g₀ L x) = x := by
  apply (surgeryBallInclusion_isOpenEmbedding g₀ L).toOpenPartialHomeomorph_right_inv
  rw [surgeryBallInclusion_range]
  exact hx

theorem surgeryBallChart_contMDiffOn (g₀ : StandardInitialMetric)
    (L : ℝ) [Nonempty (SurgeryBall.{u} g₀ L)] :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (surgeryBallChart.{u} g₀ L)
      (Metric.ball 0 (radialEuclideanRadius g₀ L)) := by
  simpa only [surgeryBallInclusion_range, surgeryBallChart, surgeryBallChartedSpace] using
    (contMDiffOn_isOpenEmbedding_symm (I := 𝓡 3) (n := ∞)
      (surgeryBallInclusion_isOpenEmbedding.{u} g₀ L))

theorem surgeryBallChart_zero (g₀ : StandardInitialMetric) {L : ℝ}
    [Nonempty (SurgeryBall.{u} g₀ L)] (hL : 0 < L) :
    surgeryBallChart.{u} g₀ L 0 = surgeryBallTip g₀ hL :=
  surgeryBallChart_left_inverse g₀ L (surgeryBallTip g₀ hL)

noncomputable def surgeryBallHomeomorph (g₀ : StandardInitialMetric)
    {L : ℝ} (hL : 0 < L) : SurgeryBall.{u} g₀ L ≃ₜ ULift.{u} StandardCapSpace := by
  let eball := OpenPartialHomeomorph.unitBallBall (0 : StandardCapSpace)
    (radialEuclideanRadius g₀ L) ((radialEuclideanRadius_pos_iff g₀ L).mpr hL)
  let e : StandardCapSpace ≃ₜ Metric.ball (0 : StandardCapSpace)
      (radialEuclideanRadius g₀ L) := Homeomorph.unitBall.trans eball.toHomeomorphSourceTarget
  exact Homeomorph.ulift.trans (e.symm.trans Homeomorph.ulift.symm)

end PoincareConjecture.M36
