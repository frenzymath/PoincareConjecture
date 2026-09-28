import PoincareConjecture.Proofs.M47.CanonicalStandardCapCarrier
import PoincareConjecture.Proofs.M35.Uniqueness.RawDistanceContinuity
import PoincareConjecture.Proofs.M04.ScalarEvolution










set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem continuousOn_standard_normalized_tip_distance {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta : theta < 1) :
    ContinuousOn (fun p : ℝ × StandardCapSpace =>
      ((standard.flow.metric p.1).edist 0 p.2).toReal *
        Real.sqrt ((standard.flow.connection p.1).scalarCurvature p.2))
      (Icc 0 theta ×ˢ univ) := by
  have htime : theta < standard.flow.base.lifetime := by
    rwa [standard.lifetime_one]
  have hdist := M35.Uniqueness.continuousOn_raw_distance
    standard.flow.base htheta0 htime (0 : StandardCapSpace)
  have hscalar : ContinuousOn (fun p : ℝ × StandardCapSpace =>
      (standard.flow.connection p.1).scalarCurvature p.2) (Icc 0 theta ×ˢ univ) :=
    standard.flow.base.flow.contMDiffOn_scalarCurvature.continuousOn.mono
      (fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt htime⟩, mem_univ _⟩)
  exact hdist.mul (Real.continuous_sqrt.comp_continuousOn hscalar)



theorem exists_compact_standard_tip_locus {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {theta L : ℝ}
    (htheta0 : 0 < theta) (htheta : theta < 1) (hL : 0 ≤ L) :
    ∃ R : ℝ, 0 ≤ R ∧
      IsCompact {p : ℝ × StandardCapSpace | p.1 ∈ Icc 0 theta ∧
        ((P.standard_cap.flow.metric p.1).edist 0 p.2).toReal *
          Real.sqrt ((P.standard_cap.flow.connection p.1).scalarCurvature p.2) ≤ L} ∧
      {p : ℝ × StandardCapSpace | p.1 ∈ Icc 0 theta ∧
        ((P.standard_cap.flow.metric p.1).edist 0 p.2).toReal *
          Real.sqrt ((P.standard_cap.flow.connection p.1).scalarCurvature p.2) ≤ L} ⊆
        Icc 0 theta ×ˢ {x | g0.metric.edist 0 x ≤ ENNReal.ofReal R} := by
  obtain ⟨c, hc, hrate⟩ := (Classical.choice P.standard_cap_uniqueness).scalar_lower_bound
  obtain ⟨Lambda, hLambda, hmetric⟩ :=
    exists_standard_initial_distance_factor P.standard_cap htheta0.le htheta
  let R := Lambda * (L / Real.sqrt c)
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hR : 0 ≤ R := mul_nonneg hLambda.le (div_nonneg hL hsqrt.le)
  let K : Set (ℝ × StandardCapSpace) := {p | p.1 ∈ Icc 0 theta ∧
    ((P.standard_cap.flow.metric p.1).edist 0 p.2).toReal *
      Real.sqrt ((P.standard_cap.flow.connection p.1).scalarCurvature p.2) ≤ L}
  have hclosed : IsClosed K := by
    have h := (isClosed_Icc.prod isClosed_univ).isClosed_le
      (continuousOn_standard_normalized_tip_distance P.standard_cap htheta0 htheta)
      (continuousOn_const (c := L))
    simpa only [K, mem_prod, mem_univ, and_true] using h
  have hsub : K ⊆ Icc 0 theta ×ˢ {x | g0.metric.edist 0 x ≤ ENNReal.ofReal R} := by
    intro p hp
    have htime : p.1 ∈ Ico 0 P.standard_cap.flow.base.lifetime := by
      rw [P.standard_cap.lifetime_one]
      exact ⟨hp.1.1, hp.1.2.trans_lt htheta⟩
    have hden : 0 < 1 - p.1 := by linarith [hp.1.2]
    have hfloor : c ≤ (P.standard_cap.flow.connection p.1).scalarCurvature p.2 := by
      apply le_trans _ (hrate p.1 htime p.2)
      apply (le_div_iff₀ hden).mpr
      nlinarith [hc, hp.1.1]
    have hroot := Real.sqrt_le_sqrt hfloor
    have hdist : ((P.standard_cap.flow.metric p.1).edist 0 p.2).toReal ≤
        L / Real.sqrt c := by
      apply (le_div_iff₀ hsqrt).mpr
      exact (mul_le_mul_of_nonneg_left hroot ENNReal.toReal_nonneg).trans hp.2
    have hdist' : (P.standard_cap.flow.metric p.1).edist 0 p.2 ≤
        ENNReal.ofReal (L / Real.sqrt c) := by
      rw [← ENNReal.ofReal_toReal ((P.standard_cap.flow.metric p.1).edist_ne_top 0 p.2)]
      exact ENNReal.ofReal_le_ofReal hdist
    refine ⟨hp.1, ?_⟩
    calc
      g0.metric.edist 0 p.2 ≤ ENNReal.ofReal Lambda *
          (P.standard_cap.flow.metric p.1).edist 0 p.2 := hmetric p.1 hp.1 0 p.2
      _ ≤ ENNReal.ofReal Lambda * ENNReal.ofReal (L / Real.sqrt c) :=
        mul_le_mul' le_rfl hdist'
      _ = ENNReal.ofReal R := (ENNReal.ofReal_mul hLambda.le).symm
  exact ⟨R, hR, (isCompact_Icc.prod (M36.standard_closed_ball_compact g0 hR)).of_isClosed_subset
    hclosed hsub, hsub⟩

end PoincareConjecture.Proofs.M47
