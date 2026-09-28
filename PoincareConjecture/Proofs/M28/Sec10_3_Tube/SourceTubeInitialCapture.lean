import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeLargeInitialBall
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCriticalRegion










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}



theorem tube_initial_neck_distance_lt (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ)
    (hsmall : epsilon ≤ (1 / 1000 : ℝ))
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (hepsilon : N.epsilon = epsilon)
    (hcenter : N.center = (H.segment k).path (H.segment k).lower)
    (hNT : N.carrier ⊆ (T k).carrierOpen)
    {x : ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier}
    (hx : x ∈ N.carrier) :
    (H.tubeMetric T k).edist (H.tubeBase T k) ⟨x, hNT hx⟩ <
      ENNReal.ofReal ((3 / 2 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹) := by
  let g := (E (k + H.shift)).flow.metric (E (k + H.shift)).time
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos k
  have hNscale : 0 < N.scale := N.scale_pos
  have hε : 0 < epsilon := hepsilon ▸ N.epsilon_pos
  have hApos : 0 < epsilon⁻¹ := inv_pos.mpr hε
  have hA : (1000 : ℝ) ≤ epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hsmall hApos.le
    rw [mul_inv_cancel₀ hε.ne'] at h
    linarith only [h]
  have hroot : Real.sqrt (1 + epsilon) ≤ (1.1 : ℝ) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 + epsilon by linarith only [hε])
    nlinarith only [hsq, hsmall, Real.sqrt_nonneg (1 + epsilon)]
  have hconstant : Real.sqrt 2 * (Real.pi + 1) ≤ (10 : ℝ) := by
    have hsqrt : Real.sqrt 2 ≤ (2 : ℝ) :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have h := mul_le_mul_of_nonneg_right hsqrt
      (show 0 ≤ Real.pi + 1 by linarith [Real.pi_pos])
    nlinarith only [h, Real.pi_lt_four]
  have hheight : |(N.coordinate_inverse x).2| < epsilon⁻¹ := by
    simpa only [hepsilon] using abs_lt.mpr (N.coordinate_inverse_mem x hx).2
  have hcN : N.center ∈ N.carrier :=
    N.central_sphere_subset N.center_on_central_sphere
  have hc0 : (N.coordinate_inverse N.center).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem_carrier hcN).mp N.center_on_central_sphere
  have hfactor : Real.sqrt (1 + epsilon) *
      (|(N.coordinate_inverse x).2| + Real.sqrt 2 * (Real.pi + 1)) <
        (3 / 2 : ℝ) * epsilon⁻¹ := by
    apply (mul_le_mul_of_nonneg_right hroot (by positivity)).trans_lt
    nlinarith only [hheight, hconstant, hA]
  have hraw : intrinsicEDist g N.carrier N.center x <
      ENNReal.ofReal ((3 / 2 : ℝ) * N.scale * epsilon⁻¹) := by
    have h := N.intrinsicEDist_le_axial_add hcN hx
    rw [hc0, sub_zero, hepsilon] at h
    apply h.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    have hm := mul_lt_mul_of_pos_left hfactor N.scale_pos
    nlinarith only [hm]
  obtain ⟨L, ⟨γ, hγ, h0, h1, hγN, rfl⟩, hshort⟩ := sInf_lt_iff.mp hraw
  have hγT : γ '' Icc (0 : ℝ) 1 ⊆ (T k).tube.carrier :=
    hγN.trans hNT
  have hhom := M13.homothety_pathELength g (H.normalizedSliceMetric k)
    (Diffeomorph.refl (𝓡 3) _ ∞) Q hQ
    (M13.identity_metricHomothety g Q hQ) γ 0 1 hγ
  change (H.normalizedSliceMetric k).pathELength γ 0 1 =
    ENNReal.ofReal (Real.sqrt Q) * g.pathELength γ 0 1 at hhom
  have hradius : Real.sqrt Q * ((3 / 2 : ℝ) * N.scale * epsilon⁻¹) =
      (3 / 2 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ := by
    calc
      _ = (3 / 2 : ℝ) * (Real.sqrt Q * N.scale) * epsilon⁻¹ := by ring
      _ = _ := by rw [H.normalizedSlice_low_neck_scale k N hcenter]
  have hnormalized : (H.normalizedSliceMetric k).pathELength γ 0 1 <
      ENNReal.ofReal ((3 / 2 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹) := by
    rw [hhom, ← hradius, ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
    exact ENNReal.mul_right_strictMono
      (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne'
      ENNReal.ofReal_ne_top hshort
  rw [tubeMetric, intrinsicOpenMetric_edist]
  change intrinsicEDist (H.normalizedSliceMetric k) (T k).tube.carrier
    ((H.segment k).path (H.segment k).lower) x < _
  rw [← hcenter]
  have hle : intrinsicEDist (H.normalizedSliceMetric k) (T k).tube.carrier N.center x ≤
      (H.normalizedSliceMetric k).pathELength γ 0 1 :=
    sInf_le ⟨γ, hγ, h0, h1, hγT, rfl⟩
  exact hle.trans_lt hnormalized



theorem tubeCritical_contains_initial_neck (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k))
    (hsmall : epsilon ≤ (1 / 1000 : ℝ)) {Acrit : ℝ}
    (hAcrit : (7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ ≤ Acrit) (k : ℕ) :
    ∃ N ∈ (H.segment k).cover.necks, N.epsilon = epsilon ∧
      N.center = (H.segment k).path (H.segment k).lower ∧
      N.carrier ⊆ (Subtype.val : (T k).carrierOpen →
        ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier) ''
          (H.tubeCriticalRegion T Acrit k : Set (T k).carrierOpen) := by
  obtain ⟨N, hN, hepsilon, hcenter, hNT⟩ := (T k).exists_initial_neck
  refine ⟨N, hN, hepsilon, hcenter, ?_⟩
  intro x hx
  refine ⟨⟨x, hNT hx⟩, ?_, rfl⟩
  have hsmallball := H.tube_initial_neck_distance_lt T k hsmall N hepsilon hcenter hNT hx
  change (H.tubeMetric T k).edist (H.tubeBase T k) ⟨x, hNT hx⟩ < ENNReal.ofReal Acrit
  apply hsmallball.trans_le
  apply ENNReal.ofReal_le_ofReal
  apply le_trans ?_ hAcrit
  have hε : 0 < epsilon := hepsilon ▸ N.epsilon_pos
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  nlinarith only [mul_pos (inv_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 4) hB))
    (inv_pos.mpr hε)]

end PoincareConjecture.M28.CounterexampleNeckFamily
