import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallCurvature
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCenteredNecks
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckDerivativeTransfer
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSourceBounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

theorem exists_criticalBallLocalShi_accuracy
    (P : RicciFlowCurvatureTheory.{u})
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      (epsilon ≤ epsilon₀ → CriticalBallLocalShi H T) := by
  obtain ⟨epsilonC, hepsilonC, hCsmall, hcentered⟩ :=
    exists_source_tube_centered_strong_necks_accuracy P
  obtain ⟨epsilonS, hepsilonS, hSsmall, K₀, hK₀, hsource⟩ :=
    exists_strongNeck_source_bounds_accuracy P.local_derivative_estimates
  let epsilon₀ := min epsilonC epsilonS
  have hepsilon₀ : 0 < epsilon₀ := lt_min hepsilonC hepsilonS
  have hsmall₀ : epsilon₀ ≤ (1 / 200 : ℝ) :=
    (min_le_right _ _).trans hSsmall
  refine ⟨epsilon₀, hepsilon₀, hsmall₀, ?_⟩
  intro hepsilon
  have hepsilonC' : epsilon ≤ epsilonC :=
    hepsilon.trans (min_le_left _ _)
  have hepsilonS' : epsilon ≤ epsilonS :=
    hepsilon.trans (min_le_right _ _)
  have hepsilon_pos : 0 < epsilon := by
    rw [← (T 0).epsilon_eq]
    exact (T 0).tube.epsilon_pos
  obtain ⟨B, hB, hsourceB⟩ := hsource epsilon hepsilon_pos hepsilonS'
  intro K tau htau l
  have hmax : 0 ≤ max K 1 :=
    le_trans (by norm_num) (le_max_right K 1)
  refine ⟨(max K 1) ^ (l + 2) * B l,
    mul_nonneg (pow_nonneg hmax _) (hB l).le, ?_⟩
  intro k x hscalar
  obtain ⟨J, hJcenter⟩ := hcentered (E (k + H.shift)) (H.segment k)
    (H.base_scalar_pos k) hepsilonC' (T k) x x.property
  obtain ⟨HJ⟩ := GeneralizedStrongNeck.exists_rescaled_raw_cylinder_flow J
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (strongNeckOpen J).carrier :=
    TopologicalSpace.Opens.instChartedSpace (strongNeckOpen J)
  have hsourceJ := hsourceB (E (k + H.shift)).flow
    (E (k + H.shift)).time J HJ
  have hcenterball :
      strongNeckSourceCenter J ∈
        ((GeneralizedStrongNeck.rescaled_half_flow J HJ).metric 0).ball
          (strongNeckSourceCenter J) (epsilon⁻¹ / 16) := by
    change ((GeneralizedStrongNeck.rescaled_half_flow J HJ).metric 0).edist
      (strongNeckSourceCenter J) (strongNeckSourceCenter J) <
      ENNReal.ofReal (epsilon⁻¹ / 16)
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr
        (div_pos (inv_pos.mpr hepsilon_pos) (by norm_num))
  have hderiv :
      (HJ.rescaling.flow.connection 0).curvatureDerivativeNorm l
        (strongNeckSourceCenter J) ≤ B l := by
    simpa only [GeneralizedStrongNeck.rescaled_half_flow_connection] using
      hsourceJ.2 l (strongNeckSourceCenter J) hcenterball
  let Q : ℝ :=
    ((E (k + H.shift)).flow.connection (E (k + H.shift)).time).scalarCurvature
      (E (k + H.shift)).basepoint
  have hQ : 0 < Q := by
    simpa only [GeneralizedRicciFlowData.scalar] using H.base_scalar_pos k
  let D := H.normalizedSliceConnection k
  let a : ℝ := Q * J.scale ^ 2
  have ha : 0 < a := by
    dsimp [a]
    exact mul_pos hQ (sq_pos_of_pos J.scale_pos)
  have hnormalized : a * D.scalarCurvature J.center = 1 := by
    have hscale : J.scale ^ 2 *
        ((E (k + H.shift)).flow.connection (E (k + H.shift)).time).scalarCurvature
          J.center = 1 := by
      rw [J.scale_scalar, ← Real.rpow_mul_natCast
        J.scalar_center_pos.le (-1 / 2 : ℝ) 2]
      simpa [Real.rpow_neg_one] using
        (inv_mul_cancel₀ J.scalar_center_pos.ne')
    have hscalarJ : D.scalarCurvature J.center =
        ((E (k + H.shift)).flow.connection (E (k + H.shift)).time).scalarCurvature
          J.center / Q := by
      simpa only [D, Q, GeneralizedRicciFlowData.scalar] using
        H.normalizedSlice_scalar_eq k J.center
    calc
      a * D.scalarCurvature J.center =
          (Q * J.scale ^ 2) *
            (((E (k + H.shift)).flow.connection
              (E (k + H.shift)).time).scalarCurvature J.center / Q) := by
        dsimp only [a]
        rw [hscalarJ]
      _ = J.scale ^ 2 *
          ((E (k + H.shift)).flow.connection
            (E (k + H.shift)).time).scalarCurvature J.center := by
        field_simp [hQ.ne']
      _ = 1 := hscale
  have hxscalar : D.scalarCurvature x.val ≤ K := by
    rw [← H.tube_scalar_eq T k x]
    apply hscalar x
    change (H.tubeMetric T k).edist x x < ENNReal.ofReal tau
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr htau
  have hJscalar : D.scalarCurvature J.center ≤ K := by
    simpa only [hJcenter] using hxscalar
  have hinv := inverse_sqrt_le_of_normalized_scalar ha hnormalized hJscalar
  have hinvpow :
      (Real.sqrt a)⁻¹ ^ (l + 2) ≤ (max K 1) ^ (l + 2) := by
    exact pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg a)) hinv _
  have hscaled := GeneralizedStrongNeck.scaled_curvatureDerivativeNorm
    J HJ Q hQ D l (strongNeckSourceCenter J)
  change D.curvatureDerivativeNorm l J.center =
      (Real.sqrt (Q * J.scale ^ 2))⁻¹ ^ (l + 2) *
        (HJ.rescaling.flow.connection 0).curvatureDerivativeNorm l
          (strongNeckSourceCenter J) at hscaled
  have hglobal : D.curvatureDerivativeNorm l x.val ≤
      (max K 1) ^ (l + 2) * B l := by
    have hglobal_center : D.curvatureDerivativeNorm l J.center ≤
        (max K 1) ^ (l + 2) * B l := by
      rw [hscaled]
      calc
        (Real.sqrt a)⁻¹ ^ (l + 2) *
            (HJ.rescaling.flow.connection 0).curvatureDerivativeNorm l
              (strongNeckSourceCenter J) ≤
            (max K 1) ^ (l + 2) *
              (HJ.rescaling.flow.connection 0).curvatureDerivativeNorm l
                (strongNeckSourceCenter J) :=
          mul_le_mul_of_nonneg_right hinvpow
            (by
              unfold LeviCivitaData.curvatureDerivativeNorm RiemannianMetric.tensorNorm
              exact Real.sqrt_nonneg _)
        _ ≤ (max K 1) ^ (l + 2) * B l :=
          mul_le_mul_of_nonneg_left hderiv (pow_nonneg hmax _)
    simpa only [hJcenter] using hglobal_center
  simpa only [intrinsicOpenMetric_curvatureDerivativeNorm
    (g := H.normalizedSliceMetric k) (V := (T k).carrierOpen)
    (DU := H.tubeConnection T k) (D := D) l x] using hglobal

theorem exists_criticalBallPointwiseShi_uniform_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ →
        ∀ (K : ℝ) (l : ℕ), ∃ B : ℝ, 0 ≤ B ∧
          ∀ (k : ℕ) (x : (T k).carrierOpen),
            (H.tubeConnection T k).scalarCurvature x ≤ K →
            (H.tubeConnection T k).curvatureDerivativeNorm l x ≤ B := by
  obtain ⟨epsilonC, hepsilonC, hCsmall, hcentered⟩ :=
    exists_source_tube_centered_strong_necks_accuracy P
  obtain ⟨epsilonS, hepsilonS, hSsmall, K₀, hK₀, hsource⟩ :=
    exists_strongNeck_source_bounds_accuracy P.local_derivative_estimates
  let epsilon₀ := min epsilonC epsilonS
  have hepsilon₀ : 0 < epsilon₀ := lt_min hepsilonC hepsilonS
  have hsmall₀ : epsilon₀ ≤ (1 / 200 : ℝ) :=
    (min_le_right _ _).trans hSsmall
  refine ⟨epsilon₀, hepsilon₀, hsmall₀, ?_⟩
  intro epsilon C A E H T hepsilon
  have hepsilonC' : epsilon ≤ epsilonC :=
    hepsilon.trans (min_le_left _ _)
  have hepsilonS' : epsilon ≤ epsilonS :=
    hepsilon.trans (min_le_right _ _)
  have hepsilon_pos : 0 < epsilon := by
    rw [← (T 0).epsilon_eq]
    exact (T 0).tube.epsilon_pos
  obtain ⟨B, hB, hsourceB⟩ := hsource epsilon hepsilon_pos hepsilonS'
  intro K l
  have hmax : 0 ≤ max K 1 := le_trans (by norm_num) (le_max_right K 1)
  refine ⟨(max K 1) ^ (l + 2) * B l,
    mul_nonneg (pow_nonneg hmax _) (hB l).le, ?_⟩
  intro k x hscalar
  obtain ⟨J, hJcenter⟩ :=
    (hcentered (E (k + H.shift)) (H.segment k)
      (H.base_scalar_pos k) hepsilonC' (T k) x x.property)
  obtain ⟨HJ⟩ := GeneralizedStrongNeck.exists_rescaled_raw_cylinder_flow J
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (strongNeckOpen J).carrier :=
    TopologicalSpace.Opens.instChartedSpace (strongNeckOpen J)
  have hsourceJ := hsourceB (E (k + H.shift)).flow
    (E (k + H.shift)).time J HJ
  have hcenterball :
      strongNeckSourceCenter J ∈
        ((GeneralizedStrongNeck.rescaled_half_flow J HJ).metric 0).ball
          (strongNeckSourceCenter J) (epsilon⁻¹ / 16) := by
    change ((GeneralizedStrongNeck.rescaled_half_flow J HJ).metric 0).edist
      (strongNeckSourceCenter J) (strongNeckSourceCenter J) <
      ENNReal.ofReal (epsilon⁻¹ / 16)
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr
        (div_pos (inv_pos.mpr hepsilon_pos) (by norm_num))
  have hderiv :
      (HJ.rescaling.flow.connection 0).curvatureDerivativeNorm l
        (strongNeckSourceCenter J) ≤ B l := by
    simpa only [GeneralizedStrongNeck.rescaled_half_flow_connection] using
      hsourceJ.2 l (strongNeckSourceCenter J) hcenterball
  let Q : ℝ :=
    ((E (k + H.shift)).flow.connection (E (k + H.shift)).time).scalarCurvature
      (E (k + H.shift)).basepoint
  have hQ : 0 < Q := by
    simpa only [GeneralizedRicciFlowData.scalar] using H.base_scalar_pos k
  let D := H.normalizedSliceConnection k
  let a : ℝ := Q * J.scale ^ 2
  have ha : 0 < a := by
    dsimp [a]
    exact mul_pos hQ (sq_pos_of_pos J.scale_pos)
  have hnormalized : a * D.scalarCurvature J.center = 1 := by
    have hscale : J.scale ^ 2 *
        ((E (k + H.shift)).flow.connection (E (k + H.shift)).time).scalarCurvature
          J.center = 1 := by
      rw [J.scale_scalar, ← Real.rpow_mul_natCast
        J.scalar_center_pos.le (-1 / 2 : ℝ) 2]
      simpa [Real.rpow_neg_one] using
        (inv_mul_cancel₀ J.scalar_center_pos.ne')
    have hscalarJ : D.scalarCurvature J.center =
        ((E (k + H.shift)).flow.connection (E (k + H.shift)).time).scalarCurvature
          J.center / Q := by
      simpa only [D, Q, GeneralizedRicciFlowData.scalar] using
        H.normalizedSlice_scalar_eq k J.center
    calc
      a * D.scalarCurvature J.center =
          (Q * J.scale ^ 2) *
            (((E (k + H.shift)).flow.connection
              (E (k + H.shift)).time).scalarCurvature J.center / Q) := by
        dsimp only [a]
        rw [hscalarJ]
      _ = J.scale ^ 2 *
          ((E (k + H.shift)).flow.connection
            (E (k + H.shift)).time).scalarCurvature J.center := by
        field_simp [hQ.ne']
      _ = 1 := hscale
  have hxscalar : D.scalarCurvature x.val ≤ K := by
    rw [← H.tube_scalar_eq T k x]
    exact hscalar
  have hJscalar : D.scalarCurvature J.center ≤ K := by
    simpa only [hJcenter] using hxscalar
  have hinv := inverse_sqrt_le_of_normalized_scalar ha hnormalized hJscalar
  have hinvpow :
      (Real.sqrt a)⁻¹ ^ (l + 2) ≤ (max K 1) ^ (l + 2) := by
    exact pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg a)) hinv _
  have hscaled := GeneralizedStrongNeck.scaled_curvatureDerivativeNorm
    J HJ Q hQ D l (strongNeckSourceCenter J)
  change D.curvatureDerivativeNorm l J.center =
      (Real.sqrt (Q * J.scale ^ 2))⁻¹ ^ (l + 2) *
        (HJ.rescaling.flow.connection 0).curvatureDerivativeNorm l
          (strongNeckSourceCenter J) at hscaled
  have hglobal : D.curvatureDerivativeNorm l x.val ≤
      (max K 1) ^ (l + 2) * B l := by
    have hglobal_center : D.curvatureDerivativeNorm l J.center ≤
        (max K 1) ^ (l + 2) * B l := by
      rw [hscaled]
      calc
        (Real.sqrt a)⁻¹ ^ (l + 2) *
            (HJ.rescaling.flow.connection 0).curvatureDerivativeNorm l
              (strongNeckSourceCenter J) ≤
            (max K 1) ^ (l + 2) *
              (HJ.rescaling.flow.connection 0).curvatureDerivativeNorm l
                (strongNeckSourceCenter J) :=
          mul_le_mul_of_nonneg_right hinvpow
            (by
              unfold LeviCivitaData.curvatureDerivativeNorm RiemannianMetric.tensorNorm
              exact Real.sqrt_nonneg _)
        _ ≤ (max K 1) ^ (l + 2) * B l :=
          mul_le_mul_of_nonneg_left hderiv (pow_nonneg hmax _)
    simpa only [hJcenter] using hglobal_center
  simpa only [intrinsicOpenMetric_curvatureDerivativeNorm
    (g := H.normalizedSliceMetric k) (V := (T k).carrierOpen)
    (DU := H.tubeConnection T k) (D := D) l x] using hglobal

theorem exists_criticalBallLocalShi_uniform_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → CriticalBallLocalShi H T := by
  obtain ⟨epsilon₀, hpos, hsmall, hpointwise⟩ :=
    exists_criticalBallPointwiseShi_uniform_accuracy P
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon K tau htau l
  obtain ⟨B, hB, hbound⟩ := hpointwise H T hepsilon K l
  refine ⟨B, hB, ?_⟩
  intro k x hscalar
  apply hbound k x
  apply hscalar x
  change (H.tubeMetric T k).edist x x < ENNReal.ofReal tau
  simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
    ENNReal.ofReal_pos.mpr htau

end PoincareConjecture.M28.CounterexampleNeckFamily
