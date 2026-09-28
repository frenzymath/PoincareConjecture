import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceNormalizedConnector
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RegularMinimizerExtension
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCriticalRegion













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily





theorem exists_source_criticalBall_small_scale_margin_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ →
        ∀ {A1 delta : ℝ} (k : ℕ) (x : H.tubeCriticalRegion T A1 k),
          0 < delta → x ∈ regularPoints (H.tubeCriticalMetric T A1 k) delta →
          ∀ {i : ℤ}, i ∈ (T k).chain.shape.active →
            (x : (T k).carrierOpen).val ∈ ((T k).chain.neck i).carrier →
            H.tubeNodeScale T k i < delta / 48 →
            ((H.tubeMetric T k).edist (H.tubeBase T k)
              (x : (T k).carrierOpen)).toReal < A1 - delta / 2 := by
  obtain ⟨epsilonW, hWpos, hWsmall, hW⟩ := exists_source_finite_walk_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _hRsmall, hR⟩ := exists_source_neck_region_accuracy.{u}
  obtain ⟨epsilonE, hEpos, _hEsmall, hE⟩ :=
    exists_source_neck_endpoint_exclusion_accuracy.{u}
  let epsilon₀ := min epsilonW (min epsilonR epsilonE)
  refine ⟨epsilon₀, lt_min hWpos (lt_min hRpos hEpos),
    (min_le_left _ _).trans hWsmall, ?_⟩
  intro epsilon C A E H T hsmall A1 delta k x hdelta hxreg i hi hx hscale
  have hsmallW : epsilon ≤ epsilonW := hsmall.trans (min_le_left _ _)
  have hsmallR : epsilon ≤ epsilonR :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallE : epsilon ≤ epsilonE :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  let S := H.segment k
  have hTR : (T k).carrierOpen.1 ⊆ S.source_region.carrier :=
    (T k).carrier_subset_neckCarrierUnion.trans
      (hR (E (k + H.shift)) S (H.base_scalar_pos k) hsmallR).2.1
  have hend := hE (E (k + H.shift)) S (H.base_scalar_pos k) hsmallE
  have hzero : S.path 0 ∉ (T k).carrierOpen :=
    fun h => hend.1 ((T k).carrier_subset_neckCarrierUnion h)
  have hone : S.path 1 ∉ (T k).carrierOpen :=
    fun h => hend.2 ((T k).carrier_subset_neckCarrierUnion h)
  obtain ⟨W⟩ := hW H T hsmallW k
  obtain ⟨v, hv, hvT, hbasepath, hconnector⟩ :=
    normalized_source_connector_of_finite_walk H T k W
      (hsmallW.trans hWsmall) hi (x : (T k).carrierOpen) hx
  have hnorm := H.normalizedSlice_source_path_minimizing k
  have he : 0 ≤ 8 * H.tubeNodeScale T k i :=
    mul_nonneg (by norm_num) (H.tubeNodeScale_pos T k i).le
  have hL : 0 < 3 * delta / 4 := by positivity
  have hbudget : 8 * H.tubeNodeScale T k i + 3 * delta / 4 < delta := by
    linarith
  obtain ⟨y, hgain⟩ := exists_radial_gain_of_regular_regional_minimizer
    (H.normalizedSliceMetric k) (T k).carrierOpen (H.tubeCriticalRegion T A1 k)
    (H.tubeBase T k) x hTR S.path_smooth S.source_region.path_mem
    hnorm.1 hnorm.2 hzero hone
    ⟨S.lower_pos.le, S.lower_lt_upper.le.trans S.upper_lt_one.le⟩ hv
    rfl hvT hbasepath hxreg he hL hbudget hconnector
  change (H.tubeMetric T k).edist (H.tubeBase T k) (x : (T k).carrierOpen) +
      ENNReal.ofReal (3 * delta / 4) ≤
    (H.tubeMetric T k).edist (H.tubeBase T k) (y : (T k).carrierOpen) +
      ENNReal.ofReal (8 * H.tubeNodeScale T k i) at hgain
  have hxfinite := H.tube_edist_ne_top T k (H.tubeBase T k)
    (x : (T k).carrierOpen)
  have hyfinite := H.tube_edist_ne_top T k (H.tubeBase T k)
    (y : (T k).carrierOpen)
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hyfinite, ENNReal.ofReal_ne_top⟩) hgain
  rw [ENNReal.toReal_add hxfinite ENNReal.ofReal_ne_top,
    ENNReal.toReal_add hyfinite ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hL.le, ENNReal.toReal_ofReal he] at hreal
  have hycrit : ((H.tubeMetric T k).edist (H.tubeBase T k)
      (y : (T k).carrierOpen)).toReal < A1 :=
    ENNReal.toReal_lt_of_lt_ofReal y.property
  linarith

end PoincareConjecture.M28.CounterexampleNeckFamily
