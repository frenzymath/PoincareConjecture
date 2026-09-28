import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeData
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceInitialBall
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenNeckRestriction
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}


def tubeMetric (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) :
    RiemannianMetric 3 (T k).carrierOpen :=
  intrinsicOpenMetric (H.normalizedSliceMetric k) (T k).carrierOpen


def tubeConnection (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) :
    LeviCivitaData (H.tubeMetric T k) :=
  Classical.choice (exists_leviCivitaData (H.tubeMetric T k))


def tubeBase (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) : (T k).carrierOpen :=
  ⟨(H.segment k).path (H.segment k).lower,
    (T k).path_mem (left_mem_Icc.mpr (H.segment k).lower_lt_upper.le)⟩


def tubeHigh (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) : (T k).carrierOpen :=
  ⟨(H.segment k).path (H.segment k).upper,
    (T k).path_mem (right_mem_Icc.mpr (H.segment k).lower_lt_upper.le)⟩


theorem tube_scalar_eq (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) (x : (T k).carrierOpen) :
    (H.tubeConnection T k).scalarCurvature x =
      (H.normalizedSliceConnection k).scalarCurvature (x : _) :=
  intrinsicOpenMetric_scalarCurvature (H.normalizedSliceMetric k)
    (T k).carrierOpen (H.tubeConnection T k) (H.normalizedSliceConnection k) x



theorem tube_edist_ne_top (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) (x y : (T k).carrierOpen) :
    (H.tubeMetric T k).edist x y ≠ ⊤ := by
  let : PreconnectedSpace (T k).carrierOpen := (T k).preconnected
  exact (H.tubeMetric T k).edist_ne_top x y



theorem tube_base_regular (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) :
    H.tubeBase T k ∈ regularPoints (H.tubeMetric T k)
      ((4 * max C 2)⁻¹ * epsilon⁻¹ / 8) := by
  obtain ⟨N, _, hepsilon, hcenter, hNV⟩ := (T k).exists_initial_neck
  have h := H.normalizedSlice_low_neck_regular k N hepsilon hcenter
    (T k).carrierOpen hNV
  have hp : (⟨N.center,
      hNV (N.central_sphere_subset N.center_on_central_sphere)⟩ : (T k).carrierOpen) =
      H.tubeBase T k := Subtype.ext hcenter
  simpa only [hp, tubeMetric] using h



theorem tube_high_distance_lt (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) :
    (H.tubeMetric T k).edist (H.tubeBase T k) (H.tubeHigh T k) <
      ENNReal.ofReal (A + 2 * endpointConnectorBudget epsilon C) := by
  rw [tubeMetric, intrinsicOpenMetric_edist]
  have hpath := (H.segment k).path_smooth.mono
    (Icc_subset_Icc (H.segment k).lower_pos.le (H.segment k).upper_lt_one.le)
  exact (intrinsicEDist_le_pathELength (H.normalizedSliceMetric k)
    (H.segment k).lower_lt_upper.le hpath (T k).path_mem).trans_lt
      (H.normalizedSlice_path_length_lt k)


theorem tube_high_scalar_tendsto (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) :
    Tendsto (fun k => (H.tubeConnection T k).scalarCurvature (H.tubeHigh T k))
      atTop atTop := by
  simpa only [tube_scalar_eq, tubeHigh] using H.normalizedSlice_upper_scalar_tendsto

end CounterexampleNeckFamily



theorem exists_source_tube_initial_bound_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)} (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)), epsilon ≤ epsilon₀ →
        let r₀ := (4 * max C 2)⁻¹ * epsilon⁻¹ / 8
        0 < r₀ ∧ ∀ k (x : (T k).carrierOpen),
          x ∈ (H.tubeMetric T k).ball (H.tubeBase T k) r₀ →
            (H.tubeConnection T k).scalarCurvature x ≤ 32 * (max C 2) ^ 2 := by
  obtain ⟨epsilon₀, hpos, hsmall, h⟩ := exists_source_initial_ball_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hbound
  obtain ⟨hr, hinitial⟩ := h H hbound
  refine ⟨hr, ?_⟩
  intro k x hx
  obtain ⟨N, _, hcenter, _, _, hscalar⟩ := hinitial k
  rw [H.tube_scalar_eq]
  apply hscalar x
  apply subset_closure
  change (H.normalizedSliceMetric k).edist N.center (x : _) < _
  rw [hcenter]
  have hle := RiemannianMetric.edist_le_intrinsicEDist (H.normalizedSliceMetric k)
    ((T k).carrierOpen : Set _) ((H.tubeBase T k : (T k).carrierOpen) : _) (x : _)
  rw [← intrinsicOpenMetric_edist] at hle
  exact hle.trans_lt hx

end PoincareConjecture.M28
