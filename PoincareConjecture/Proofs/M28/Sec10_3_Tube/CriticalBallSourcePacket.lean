import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallModerateProducer
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallLocalShiProducer
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallWitnessCofinality
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallFrontierReachability
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCriticalRadius
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFiniteWalk











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





structure CriticalBallSourcePacket
    (H : CounterexampleNeckFamily E) where
  tube : ∀ k, SourceTubeData (H.segment k)
  radius : ℝ
  radius_pos : 0 < radius
  radius_lower : (4 * max C 2)⁻¹ * epsilon⁻¹ / 8 ≤ radius
  radius_upper : radius ≤ A + 2 * endpointConnectorBudget epsilon C
  radius_bound : ∀ r < radius, PoincareConjecture.M28.tube.eventuallyRadiusBound
    (fun k x => ((H.tubeMetric tube k).edist (H.tubeBase tube k) x).toReal)
    (fun k x => (H.tubeConnection tube k).scalarCurvature x) r
  high_index : ℕ → ℕ
  high_index_strictMono : StrictMono high_index
  high_point : ∀ j : ℕ, (tube (high_index j)).carrierOpen
  high_radius_upper : ∀ j : ℕ,
    ((H.tubeMetric tube (high_index j)).edist
      (H.tubeBase tube (high_index j)) (high_point j)).toReal <
        radius + 1 / ((j : ℝ) + 1)
  high_scalar_lower : ∀ j : ℕ, (j : ℝ) <
    (H.tubeConnection tube (high_index j)).scalarCurvature (high_point j)
  high_cofinal : ∀ n : ℕ, ∃ j : ℕ,
    radius - 1 / ((n : ℝ) + 1) <
      ((H.tubeMetric tube (high_index j)).edist
        (H.tubeBase tube (high_index j)) (high_point j)).toReal
  high_endpoint_eventually_near : ∀ n : ℕ, ∀ᶠ k in atTop,
    radius - 1 / ((n : ℝ) + 1) <
      ((H.tubeMetric tube k).edist (H.tubeBase tube k)
        (H.tubeHigh tube k)).toReal
  local_shi : CriticalBallLocalShi H tube
  finite_walk : ∀ k, Nonempty (SourceFiniteWalk H tube k)
  moderate_witness : ∀ {A1 delta : ℝ} {k : ℕ}
    (x : H.tubeCriticalRegion tube A1 k) {i : ℤ},
    i ∈ (tube k).chain.shape.active →
    (x : (tube k).carrierOpen).val ∈ ((tube k).chain.neck i).carrier →
    |(((tube k).chain.neck i).coordinate_inverse
        (x : (tube k).carrierOpen).val).2| ≤
      3 * ((tube k).chain.neck i).epsilon⁻¹ / 4 →
    0 < delta → delta / 48 ≤ H.tubeNodeScale tube k i →
    CriticalBallModerateWitness H tube (A1 := A1) (delta := delta) k x





theorem exists_criticalBall_source_packet_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E),
        epsilon ≤ epsilon₀ → Nonempty (CriticalBallSourcePacket H) := by
  obtain ⟨epsilonR, hRpos, hRsmall, hR⟩ :=
    exists_actual_source_tube_critical_radius_accuracy.{u}
  obtain ⟨epsilonS, hSpos, hSsmall, hS⟩ :=
    exists_criticalBallLocalShi_uniform_accuracy.{u} P
  obtain ⟨epsilonM, hMpos, hMsmall, hM⟩ :=
    exists_criticalBall_moderate_witness_accuracy.{u}
  obtain ⟨epsilonW, hWpos, hWsmall, hW⟩ :=
    exists_source_finite_walk_accuracy.{u}
  let epsilon₀ := min epsilonR (min epsilonS (min epsilonM epsilonW))
  have hpos : 0 < epsilon₀ := lt_min hRpos (lt_min hSpos (lt_min hMpos hWpos))
  have hsmall : epsilon₀ ≤ (1 / 200 : ℝ) :=
    (min_le_left _ _).trans (hRsmall.trans (by norm_num))
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H hE
  have hER : epsilon ≤ epsilonR := hE.trans (min_le_left _ _)
  have hES : epsilon ≤ epsilonS :=
    hE.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hEM : epsilon ≤ epsilonM :=
    hE.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hEW : epsilon ≤ epsilonW :=
    hE.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨T, A1, hA1, hA1lower, hA1upper, hbound,
      phi, hphi, x, hx⟩ := hR H hER
  have hshi := hS H T hES
  refine ⟨{
    tube := T
    radius := A1
    radius_pos := hA1
    radius_lower := hA1lower
    radius_upper := hA1upper
    radius_bound := hbound
    high_index := phi
    high_index_strictMono := hphi
    high_point := x
    high_radius_upper := fun j => (hx j).1
    high_scalar_lower := fun j => (hx j).2
    high_cofinal :=
      PoincareConjecture.M28.tube.critical_witnesses_cofinal_below
        hbound hphi x hx
    high_endpoint_eventually_near :=
      H.tube_high_eventually_near T hbound
    local_shi := hshi
    finite_walk := hW H T hEW
    moderate_witness := ?_ }⟩
  intro A1' delta k x' i hi hx' hquarter hdelta hscale
  exact hM H T hEM (A1 := A1') (delta := delta) (k := k) x' hi hx'
    hquarter hdelta hscale

end PoincareConjecture.M28.CounterexampleNeckFamily
