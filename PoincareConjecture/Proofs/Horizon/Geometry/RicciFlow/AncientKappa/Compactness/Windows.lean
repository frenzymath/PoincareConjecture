import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Estimates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.LocalControl
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

namespace BasedKappaSolution

variable {kappa a b : ℝ} (B : BasedKappaSolution kappa)

local instance : TopologicalSpace B.carrier.carrier := B.carrier.topologicalSpace
local instance : MeasurableSpace B.carrier.carrier := B.carrier.measurableSpace
local instance : BorelSpace B.carrier.carrier := B.carrier.borelSpace
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) B.carrier.carrier :=
  B.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ B.carrier.carrier := B.carrier.isManifold
local instance : T2Space B.carrier.carrier := B.carrier.t2Space
local instance : T3Space B.carrier.carrier := B.carrier.t3Space
local instance : SecondCountableTopology B.carrier.carrier := B.carrier.secondCountable
local instance : ConnectedSpace B.carrier.carrier := B.connectedSpace

def shiftedWindowFlow (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) :
    RicciFlow 3 B.carrier.carrier (Ioo a b) :=
  B.flow.flow.translate (-1)
    (by rintro _ ⟨t, ht, rfl⟩; change t + -1 ≤ 0; linarith [ht.2])
    ordConnected_Ioo
    (by refine ⟨a / 2, ⟨?_, ?_⟩, b / 2, ⟨?_, ?_⟩, ?_⟩ <;> linarith)

noncomputable def basedWindow (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) :
    BasedFlow 3 a b B.carrier where
  base := B.base
  flow := B.shiftedWindowFlow ha hb hb1
  volumeMeasure := B.carrier.metricHausdorffVolume
    ((B.shiftedWindowFlow ha hb hb1).metric 0)
  spacetimeVectorField := fun _ _ ↦ (1, 0)
  spacetimeVectorField_time := fun _ _ ↦ rfl
  spacetimeVectorField_spatial_zero := fun _ _ ↦ rfl

theorem basedWindow_zeroBall (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) (r : ℝ) :
    (B.basedWindow ha hb hb1).zeroBall r = (B.flow.flow.metric (-1)).ball B.base r := by
  simp only [BasedFlow.zeroBall, basedWindow, shiftedWindowFlow,
    RicciFlow.translate, FlowCarrier.metricBall, zero_add]

theorem basedWindow_zeroBall_compact
    (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) (r : ℝ) :
    IsCompact (closure ((B.basedWindow ha hb hb1).zeroBall r)) := by
  rw [B.basedWindow_zeroBall ha hb hb1]
  exact (B.flow.flow.metric (-1)).isCompact_closure_ball_of_metricComplete
    (B.flow.complete (-1) (by norm_num)) B.base r

end BasedKappaSolution

namespace NormalizedKappaSolutionSequence

variable {kappa a b : ℝ} (S : NormalizedKappaSolutionSequence kappa)

noncomputable def windowSequence (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) :
    PointedFlowSequence 3 a b where
  carrier := fun k ↦ (S.term k).carrier
  flow := fun k ↦ (S.term k).basedWindow ha hb hb1

theorem window_noncollapsing
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ r κ : ℝ, 0 < r ∧ 0 < κ ∧ ∀ k,
      ENNReal.ofReal (κ * r ^ 3) ≤ ((S.term k).basedWindow ha hb hb1).zeroBallVolume r := by
  obtain ⟨C, hC, hbound⟩ := hcontrol 1 (by norm_num)
  let r : ℝ := (C + 1)⁻¹
  have hCp : 0 < C + 1 := by linarith
  have hr : 0 < r := inv_pos.mpr hCp
  have hr1 : r ≤ 1 := (inv_le_one₀ hCp).2 (by linarith)
  have hrC : C ≤ r⁻¹ ^ 2 := by dsimp [r]; rw [inv_inv]; nlinarith
  have hcal := ENNReal.toReal_pos (euclideanVolumeCalibration_pos 3).ne'
    (euclideanVolumeCalibration_ne_top 3)
  refine ⟨r, kappa / (euclideanVolumeCalibration 3).toReal, hr,
    div_pos S.kappa_pos hcal, ?_⟩
  intro k
  let B := S.term k
  let Crr := B.carrier
  letI : TopologicalSpace Crr.carrier := Crr.topologicalSpace
  letI : MeasurableSpace Crr.carrier := Crr.measurableSpace
  letI : BorelSpace Crr.carrier := Crr.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Crr.carrier := Crr.chartedSpace
  letI : IsManifold (𝓡 3) ∞ Crr.carrier := Crr.isManifold
  letI : T2Space Crr.carrier := Crr.t2Space
  letI : T3Space Crr.carrier := Crr.t3Space
  letI : SecondCountableTopology Crr.carrier := Crr.secondCountable
  letI : ConnectedSpace Crr.carrier := B.connectedSpace
  have hnc := B.flow.noncollapsed r hr (-1) (by norm_num) B.base r hr le_rfl (by
    intro t ht x hx
    have hx0 := P.ball_monotone Crr.carrier B.flow (-1) 0 (by norm_num) le_rfl B.base r hx
    have hx1 : x ∈ (B.flow.flow.metric 0).ball B.base 1 :=
      lt_of_lt_of_le hx0 (ENNReal.ofReal_le_ofReal hr1)
    exact (hbound k t (ht.2.trans (by norm_num)) x hx1).trans hrC)
  rw [B.kappa_eq] at hnc
  have hvol := calibrated_noncollapse_to_hausdorff Crr (B.flow.flow.metric (-1))
    ((B.flow.flow.metric (-1)).ball B.base r) S.kappa_pos hr hnc
  simpa only [BasedFlow.zeroBallVolume, BasedFlow.zeroBall, FlowCarrier.metricBall,
    BasedKappaSolution.basedWindow, BasedKappaSolution.shiftedWindowFlow,
    RicciFlow.translate, zero_add] using hvol

noncomputable def compactnessHypotheses
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) :
    PointedRicciFlowCompactnessHypotheses 3 a b where
  time_bounds := ⟨ha, hb⟩
  sequence := S.windowSequence ha hb hb1
  volume_compatibility := fun _ ↦ rfl
  zero_time_ball_compact := fun A _ ↦ Eventually.of_forall fun k ↦
    (S.term k).basedWindow_zeroBall_compact ha hb hb1 A
  spacetime_control := by
    intro A hA I _ _ _ hI
    obtain ⟨C, hC, hbound⟩ := hcontrol A hA
    refine ⟨C, hC, Eventually.of_forall ?_⟩
    intro k
    let B := S.term k
    let Crr := B.carrier
    letI : TopologicalSpace Crr.carrier := Crr.topologicalSpace
    letI : MeasurableSpace Crr.carrier := Crr.measurableSpace
    letI : BorelSpace Crr.carrier := Crr.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Crr.carrier := Crr.chartedSpace
    letI : IsManifold (𝓡 3) ∞ Crr.carrier := Crr.isManifold
    letI : T2Space Crr.carrier := Crr.t2Space
    letI : T3Space Crr.carrier := Crr.t3Space
    letI : SecondCountableTopology Crr.carrier := Crr.secondCountable
    letI : ConnectedSpace Crr.carrier := B.connectedSpace
    refine ⟨SmoothSpacetimeEmbedding.refl (B.basedWindow ha hb hb1)
      (I ×ˢ (B.basedWindow ha hb hb1).zeroBall A), fun _ _ ↦ rfl, hC, ?_⟩
    intro t ht x hx
    change x ∈ (B.basedWindow ha hb hb1).zeroBall A at hx
    rw [B.basedWindow_zeroBall ha hb hb1] at hx
    have hx0 := P.ball_monotone Crr.carrier B.flow (-1) 0 (by norm_num) le_rfl B.base A hx
    exact (le_abs_self _).trans (hbound k (t - 1) (by linarith [(hI ht).2]) x hx0)
  all_time_curvature_control := by
    intro A hA
    obtain ⟨C, hC, hbound⟩ := hcontrol A hA
    refine ⟨C, hC, Eventually.of_forall ?_⟩
    intro k
    let B := S.term k
    let Crr := B.carrier
    letI : TopologicalSpace Crr.carrier := Crr.topologicalSpace
    letI : MeasurableSpace Crr.carrier := Crr.measurableSpace
    letI : BorelSpace Crr.carrier := Crr.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Crr.carrier := Crr.chartedSpace
    letI : IsManifold (𝓡 3) ∞ Crr.carrier := Crr.isManifold
    letI : T2Space Crr.carrier := Crr.t2Space
    letI : T3Space Crr.carrier := Crr.t3Space
    letI : SecondCountableTopology Crr.carrier := Crr.secondCountable
    letI : ConnectedSpace Crr.carrier := B.connectedSpace
    dsimp only
    intro t₀ ht₀ t ht x hx
    have hx0 := P.ball_monotone Crr.carrier B.flow (t₀ - 1) 0
      (by linarith [ht₀.2]) le_rfl B.base A hx
    exact (le_abs_self _).trans (hbound k (t - 1) (by linarith [ht.2]) x hx0)
  noncollapsing := by
    obtain ⟨r, κ, hr, hκ, hvol⟩ := S.window_noncollapsing P hcontrol ha hb hb1
    exact ⟨r, κ, hr, hκ, Eventually.of_forall hvol⟩

theorem compactnessConclusion
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hlocal : M23LocalCurvatureEstimate S)
    (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) :
    Nonempty (PointedRicciFlowCompactnessConclusion
      (S.compactnessHypotheses P (m23AllTimeCurvatureControl_of_local S P hlocal) ha hb hb1)) :=
  P.pointed_compactness ha hb _

end NormalizedKappaSolutionSequence

end PoincareConjecture
