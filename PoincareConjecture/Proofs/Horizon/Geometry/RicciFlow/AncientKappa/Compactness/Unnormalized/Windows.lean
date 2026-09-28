import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.LocalControl
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.AncientKappaSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance windowCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

variable (C : ℕ → FlowCarrier.{0} 3)
  (K : ∀ k, AncientKappaSolution 3 (C k).carrier) (p : ∀ k, (C k).carrier)
  {a b : ℝ}

def shiftedWindowFlow (k : ℕ) (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) :
    RicciFlow 3 (C k).carrier (Ioo a b) :=
  (K k).flow.translate (-1)
    (by rintro _ ⟨t, ht, rfl⟩; change t + -1 ≤ 0; linarith [ht.2])
    ordConnected_Ioo
    (by refine ⟨a / 2, ⟨?_, ?_⟩, b / 2, ⟨?_, ?_⟩, ?_⟩ <;> linarith)

noncomputable def basedWindow (k : ℕ) (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) :
    BasedFlow 3 a b (C k) where
  base := p k
  flow := shiftedWindowFlow C K k ha hb hb1
  volumeMeasure := (C k).metricHausdorffVolume
    ((shiftedWindowFlow C K k ha hb hb1).metric 0)
  spacetimeVectorField := fun _ _ => (1, 0)
  spacetimeVectorField_time := fun _ _ => rfl
  spacetimeVectorField_spatial_zero := fun _ _ => rfl

theorem basedWindow_zeroBall (k : ℕ) (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) (r : ℝ) :
    (basedWindow C K p k ha hb hb1).zeroBall r = ((K k).flow.metric (-1)).ball (p k) r := by
  simp only [BasedFlow.zeroBall, basedWindow, shiftedWindowFlow,
    RicciFlow.translate, FlowCarrier.metricBall, zero_add]

theorem basedWindow_zeroBall_compact
    (k : ℕ) (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) (r : ℝ) :
    IsCompact (closure ((basedWindow C K p k ha hb hb1).zeroBall r)) := by
  rw [basedWindow_zeroBall C K p k ha hb hb1]
  exact ((K k).flow.metric (-1)).isCompact_closure_ball_of_metricComplete
    ((K k).complete (-1) (by norm_num)) (p k) r

noncomputable def windowSequence (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) :
    PointedFlowSequence 3 a b where
  carrier := C
  flow := fun k => basedWindow C K p k ha hb hb1

variable (P : M23NormalizedKappaCompactnessPredecessors)
  {κ : ℝ} (hκ : 0 < κ) (hkappa : ∀ k, (K k).kappa = κ)
  (hcontrol : ∀ r : ℝ, 0 < r → ∃ B : ℝ, 0 ≤ B ∧
    ∀ k t, t ≤ 0 → ∀ x ∈ ((K k).flow.metric 0).ball (p k) r,
      |((K k).flow.connection t).curvatureTensorNorm x| ≤ B)

include P hκ hkappa hcontrol in
theorem window_noncollapsing (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ r κ' : ℝ, 0 < r ∧ 0 < κ' ∧ ∀ k,
      ENNReal.ofReal (κ' * r ^ 3) ≤ (basedWindow C K p k ha hb hb1).zeroBallVolume r := by
  obtain ⟨B, hB, hbound⟩ := hcontrol 1 (by norm_num)
  let r : ℝ := (B + 1)⁻¹
  have hBp : 0 < B + 1 := by linarith
  have hr : 0 < r := inv_pos.mpr hBp
  have hr1 : r ≤ 1 := (inv_le_one₀ hBp).2 (by linarith)
  have hrB : B ≤ r⁻¹ ^ 2 := by dsimp [r]; rw [inv_inv]; nlinarith
  have hcal := ENNReal.toReal_pos (euclideanVolumeCalibration_pos 3).ne'
    (euclideanVolumeCalibration_ne_top 3)
  refine ⟨r, κ / (euclideanVolumeCalibration 3).toReal, hr, div_pos hκ hcal, ?_⟩
  intro k
  have hnc := (K k).noncollapsed r hr (-1) (by norm_num) (p k) r hr le_rfl (by
    intro t ht x hx
    have hx0 := P.ball_monotone (C k).carrier (K k) (-1) 0
      (by norm_num) le_rfl (p k) r hx
    have hx1 : x ∈ ((K k).flow.metric 0).ball (p k) 1 :=
      lt_of_lt_of_le hx0 (ENNReal.ofReal_le_ofReal hr1)
    exact (hbound k t (ht.2.trans (by norm_num)) x hx1).trans hrB)
  rw [hkappa k] at hnc
  have hvol := calibrated_noncollapse_to_hausdorff (C k) ((K k).flow.metric (-1))
    (((K k).flow.metric (-1)).ball (p k) r) hκ hr hnc
  simpa only [BasedFlow.zeroBallVolume, BasedFlow.zeroBall, FlowCarrier.metricBall,
    basedWindow, shiftedWindowFlow, RicciFlow.translate, zero_add] using hvol

noncomputable def compactnessHypotheses (ha : a < 0) (hb : 0 < b) (hb1 : b ≤ 1) :
    PointedRicciFlowCompactnessHypotheses 3 a b where
  time_bounds := ⟨ha, hb⟩
  sequence := windowSequence C K p ha hb hb1
  volume_compatibility := fun _ => rfl
  zero_time_ball_compact := fun A _ => Eventually.of_forall fun k =>
    basedWindow_zeroBall_compact C K p k ha hb hb1 A
  spacetime_control := by
    intro A hA I _ _ _ hI
    obtain ⟨B, hB, hbound⟩ := hcontrol A hA
    refine ⟨B, hB, Eventually.of_forall ?_⟩
    intro k
    refine ⟨SmoothSpacetimeEmbedding.refl (basedWindow C K p k ha hb hb1)
      (I ×ˢ (basedWindow C K p k ha hb hb1).zeroBall A), fun _ _ => rfl, hB, ?_⟩
    intro t ht x hx
    change x ∈ (basedWindow C K p k ha hb hb1).zeroBall A at hx
    rw [basedWindow_zeroBall C K p k ha hb hb1] at hx
    have hx0 := P.ball_monotone (C k).carrier (K k) (-1) 0
      (by norm_num) le_rfl (p k) A hx
    exact (le_abs_self _).trans (hbound k (t - 1) (by linarith [(hI ht).2]) x hx0)
  all_time_curvature_control := by
    intro A hA
    obtain ⟨B, hB, hbound⟩ := hcontrol A hA
    refine ⟨B, hB, Eventually.of_forall ?_⟩
    intro k
    dsimp only
    intro t₀ ht₀ t ht x hx
    have hx0 := P.ball_monotone (C k).carrier (K k) (t₀ - 1) 0
      (by linarith [ht₀.2]) le_rfl (p k) A hx
    exact (le_abs_self _).trans (hbound k (t - 1) (by linarith [ht.2]) x hx0)
  noncollapsing := by
    obtain ⟨r, κ', hr, hκ', hvol⟩ := window_noncollapsing C K p P hκ hkappa hcontrol ha hb hb1
    exact ⟨r, κ', hr, hκ', Eventually.of_forall hvol⟩

end PoincareConjecture.AncientKappaSequence
