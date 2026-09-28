import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCenteredNecks
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCriticalRegion
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckScaledVolume
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.OpenRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem exists_source_tubeCritical_noncollapse_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ κ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧ 0 < κ ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)} (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)) (Acrit : ℝ) (hAcrit : 0 < Acrit),
        epsilon ≤ epsilon₀ → ∀ k (D : LeviCivitaData (H.tubeCriticalMetric T Acrit k)),
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            ∀ q ∈ regularComponent (H.tubeCriticalMetric T Acrit k)
              (H.tubeCriticalBase T Acrit hAcrit k) r,
              (∀ x ∈ (H.tubeCriticalMetric T Acrit k).ball q r,
                |D.curvatureTensorNorm x| ≤ r⁻¹ ^ 2) →
              ENNReal.ofReal (κ * r ^ 3) ≤ (H.tubeCriticalMetric T Acrit k).volumeMeasure
                ((H.tubeCriticalMetric T Acrit k).ball q r) := by
  obtain ⟨epsilon₀, hpos, hsmall, hcentered⟩ :=
    exists_source_tube_centered_strong_necks_accuracy P
  refine ⟨epsilon₀, strongNeckNoncollapseConstant, hpos, hsmall,
    strongNeckNoncollapseConstant_pos, ?_⟩
  intro epsilon C A E H T Acrit hAcrit hepsilon k D r hr _hrone q hq hcurv
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos k
  have hsmall200 : epsilon ≤ (1 / 200 : ℝ) :=
    (hepsilon.trans hsmall).trans (by norm_num)
  have hhalf : epsilon < 1 / 2 := hsmall200.trans_lt (by norm_num)
  obtain ⟨J, hJcenter⟩ := hcentered (E (k + H.shift)) (H.segment k)
    (H.base_scalar_pos k) hepsilon (T k) q.val.val q.val.property
  let s := Real.sqrt Q * J.scale
  have hs : 0 < s := mul_pos (Real.sqrt_pos.mpr hQ) J.scale_pos
  have hscalar : D.scalarCurvature q =
      (H.normalizedSliceConnection k).scalarCurvature q.val.val := by
    calc
      _ = (H.tubeConnection T k).scalarCurvature q.val :=
        intrinsicOpenMetric_scalarCurvature (H.tubeMetric T k)
          (H.tubeCriticalRegion T Acrit k) D (H.tubeConnection T k) q
      _ = _ := H.tube_scalar_eq T k q.val
  have hcenterNorm := tube.neck_normalized_scalar_center
    (strongNeck_top J hhalf) ((E (k + H.shift)).flow.connection (E (k + H.shift)).time)
  change J.scale ^ 2 * (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, J.center⟩ = 1 at hcenterNorm
  have hnormalized : s ^ 2 * D.scalarCurvature q = 1 := by
    rw [hscalar, H.normalizedSlice_scalar_eq]
    change (Real.sqrt Q * J.scale) ^ 2 *
      ((E (k + H.shift)).flow.scalar ⟨(E (k + H.shift)).time, q.val.val⟩ / Q) = 1
    rw [← hJcenter, mul_pow, Real.sq_sqrt hQ.le, div_eq_mul_inv]
    calc
      _ = (Q * Q⁻¹) * (J.scale ^ 2 * (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, J.center⟩) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hQ.ne', one_mul]; exact hcenterNorm
  have hqball : q ∈ (H.tubeCriticalMetric T Acrit k).ball q r := by
    change (H.tubeCriticalMetric T Acrit k).edist q q < ENNReal.ofReal r
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr hr
  have hcurvcenter : D.curvatureTensorNorm q ≤ r⁻¹ ^ 2 :=
    (le_abs_self _).trans (hcurv q hqball)
  have hscalarBound : D.scalarCurvature q ≤ 3 * r⁻¹ ^ 2 := by
    have h := D.scalarCurvature_le_curvatureTensorNorm_sharp q
    norm_num only [Nat.cast_ofNat] at h
    exact h.trans (mul_le_mul_of_nonneg_left hcurvcenter (by norm_num))
  have hbound : (1 : ℝ) ≤ s ^ 2 * (3 * r⁻¹ ^ 2) := by
    calc
      1 = s ^ 2 * D.scalarCurvature q := hnormalized.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hscalarBound (sq_nonneg s)
  have hradiusSq : r ^ 2 ≤ 3 * s ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hbound (sq_nonneg r)
    calc
      r ^ 2 ≤ (s ^ 2 * (3 * r⁻¹ ^ 2)) * r ^ 2 := by simpa only [one_mul] using h
      _ = (3 * s ^ 2) * (r⁻¹ ^ 2 * r ^ 2) := by ring
      _ = 3 * s ^ 2 := by
        rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, mul_one]
  have hrscale : r ≤ 2 * s :=
    (sq_le_sq₀ hr.le (mul_nonneg (by norm_num) hs.le)).mp
      (by nlinarith only [hradiusSq, sq_nonneg s])
  have hvolume := GeneralizedStrongNeck.scaled_ambient_ball_volume_lower J Q hQ
    hsmall200 hr hrscale
  change ENNReal.ofReal (strongNeckNoncollapseConstant * r ^ 3) ≤
    (H.normalizedSliceMetric k).volumeMeasure
      ((H.normalizedSliceMetric k).ball J.center r) at hvolume
  rw [hJcenter] at hvolume
  have hregular : q ∈ regularPoints (H.tubeCriticalMetric T Acrit k) r :=
    regularComponent_subset _ _ _ hq
  have hmeasure : (H.tubeCriticalMetric T Acrit k).volumeMeasure
      ((H.tubeCriticalMetric T Acrit k).ball q r) =
      (H.normalizedSliceMetric k).volumeMeasure
        ((H.normalizedSliceMetric k).ball q.val.val r) :=
    nested_intrinsicOpenMetric_ball_volume_of_regular (H.normalizedSliceMetric k)
      (T k).carrierOpen (H.tubeCriticalRegion T Acrit k) q hregular
  rw [hmeasure]
  exact hvolume

end PoincareConjecture.M28
