import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeInitialCapture
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSlabRegularity
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.NestedBallClosure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  (H : CounterexampleNeckFamily E)

theorem normalizedSlice_low_neck_ball_at (k : ℕ)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (hcenter : N.center = (H.segment k).path (H.segment k).lower)
    (p : ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier) (r : ℝ) :
    (H.normalizedSliceMetric k).ball p ((4 * max C 2)⁻¹ * r) =
      ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).ball p (N.scale * r) := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos k
  have hradius : Real.sqrt Q * (N.scale * r) = (4 * max C 2)⁻¹ * r := by
    rw [← mul_assoc, H.normalizedSlice_low_neck_scale k N hcenter]
  have hball := M13.homothety_ball_image
    ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
    (H.normalizedSliceMetric k) (Diffeomorph.refl (𝓡 3) _ ∞) Q hQ
    (M13.identity_metricHomothety _ Q hQ) p (N.scale * r)
  rw [hradius] at hball
  simpa using hball.symm

theorem normalizedSlice_low_neck_core_compact (k : ℕ)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (hepsilon : N.epsilon = epsilon)
    (hcenter : N.center = (H.segment k).path (H.segment k).lower)
    {p : ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier}
    (hp : p ∈ N.carrier)
    (hheight : |(N.coordinate_inverse p).2| ≤ 7 * N.epsilon⁻¹ / 8) :
    IsCompact (closure ((H.normalizedSliceMetric k).ball p
      ((4 * max C 2)⁻¹ * epsilon⁻¹ / 32))) ∧
      closure ((H.normalizedSliceMetric k).ball p
        ((4 * max C 2)⁻¹ * epsilon⁻¹ / 32)) ⊆ N.carrier := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half])
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon), N.epsilon_lt_half]
  have hfactor : N.scale / 2 ≤ N.scale * Real.sqrt (1 - N.epsilon) := by
    nlinarith only [mul_le_mul_of_nonneg_left hroot N.scale_pos.le]
  have hmargin : N.epsilon⁻¹ / 8 ≤ N.epsilon⁻¹ - |(N.coordinate_inverse p).2| := by
    linarith only [hheight]
  have hbound := mul_le_mul hfactor hmargin
    (by positivity : 0 ≤ N.epsilon⁻¹ / 8)
    (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
  have hraw : N.scale * N.epsilon⁻¹ / 32 <
      (N.scale * Real.sqrt (1 - N.epsilon)) *
        (N.epsilon⁻¹ - |(N.coordinate_inverse p).2|) := by
    apply lt_of_lt_of_le _ hbound
    nlinarith only [mul_pos N.scale_pos hA]
  have hball : (H.normalizedSliceMetric k).ball p
      ((4 * max C 2)⁻¹ * epsilon⁻¹ / 32) =
      ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).ball p
        (N.scale * N.epsilon⁻¹ / 32) := by
    simpa only [hepsilon, mul_div_assoc] using
      H.normalizedSlice_low_neck_ball_at k N hcenter p (N.epsilon⁻¹ / 32)
  rw [hball]
  exact N.precompact_ball_of_axial_margin hp hraw

variable (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ)

theorem tubeCritical_initial_neck_core_regular (k : ℕ)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (hepsilon : N.epsilon = epsilon)
    (hcenter : N.center = (H.segment k).path (H.segment k).lower)
    (hNcritical : N.carrier ⊆ (Subtype.val : (T k).carrierOpen →
      ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier) ''
        (H.tubeCriticalRegion T A1 k : Set (T k).carrierOpen))
    (x : H.tubeCriticalRegion T A1 k)
    (hx : (x : (T k).carrierOpen).val ∈ N.carrier)
    (hheight : |(N.coordinate_inverse (x : (T k).carrierOpen).val).2| ≤
      7 * N.epsilon⁻¹ / 8) :
    x ∈ regularPoints (H.tubeCriticalMetric T A1 k)
      ((4 * max C 2)⁻¹ * epsilon⁻¹ / 32) := by
  obtain ⟨hcompact, hclosure⟩ := H.normalizedSlice_low_neck_core_compact
    k N hepsilon hcenter hx hheight
  have hcompactV := nested_intrinsicOpenMetric_isCompact_closure_ball
    (H.normalizedSliceMetric k) (T k).carrierOpen (H.tubeCriticalRegion T A1 k) x
    hcompact (hclosure.trans hNcritical)
  change IsCompact (closure ((H.tubeCriticalMetric T A1 k).ball x
    ((4 * max C 2)⁻¹ * epsilon⁻¹ / 32))) at hcompactV
  intro r hr
  apply hcompactV.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro y hy
  exact hy.trans_le (ENNReal.ofReal_le_ofReal hr.le)

theorem tubeCritical_initial_neck_core_component (hA1 : 0 < A1) (k : ℕ)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (hepsilon : N.epsilon = epsilon)
    (hcenter : N.center = (H.segment k).path (H.segment k).lower)
    (hNcritical : N.carrier ⊆ (Subtype.val : (T k).carrierOpen →
      ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier) ''
        (H.tubeCriticalRegion T A1 k : Set (T k).carrierOpen))
    (x : H.tubeCriticalRegion T A1 k)
    (hx : (x : (T k).carrierOpen).val ∈ N.carrier)
    (hheight : |(N.coordinate_inverse (x : (T k).carrierOpen).val).2| ≤
      3 * N.epsilon⁻¹ / 4) :
    x ∈ regularComponent (H.tubeCriticalMetric T A1 k)
      (H.tubeCriticalBase T A1 hA1 k) ((4 * max C 2)⁻¹ * epsilon⁻¹ / 32) := by
  let f : H.tubeCriticalRegion T A1 k →
      ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier :=
    fun y => (y : (T k).carrierOpen).val
  let O := N.region (-(7 * N.epsilon⁻¹ / 8)) (7 * N.epsilon⁻¹ / 8)
  let K := f ⁻¹' O
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hO : IsPreconnected O := N.isPreconnected_region (by linarith) (by linarith)
  have hrange : O ⊆ range f := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hNcritical hy.1
    exact ⟨⟨z, hz⟩, hzy⟩
  have hf : Topology.IsInducing f :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hK : IsPreconnected K := by
    apply hf.isPreconnected_image.mp
    change IsPreconnected (f '' (f ⁻¹' O))
    rw [image_preimage_eq_of_subset hrange]
    exact hO
  have hbase : H.tubeCriticalBase T A1 hA1 k ∈ K := by
    change f (H.tubeCriticalBase T A1 hA1 k) ∈ O
    have hb : f (H.tubeCriticalBase T A1 hA1 k) = N.center := hcenter.symm
    rw [hb]
    exact N.central_sphere_subset_region (by linarith only [hA]) (by positivity)
      N.center_on_central_sphere
  have hregular : K ⊆ regularPoints (H.tubeCriticalMetric T A1 k)
      ((4 * max C 2)⁻¹ * epsilon⁻¹ / 32) := by
    intro y hy
    exact H.tubeCritical_initial_neck_core_regular T A1 k N hepsilon hcenter hNcritical
      y hy.1 (abs_lt.mpr hy.2).le
  have hxK : x ∈ K := by
    change (x : (T k).carrierOpen).val ∈ O
    refine ⟨hx, ?_, ?_⟩
    · linarith [(abs_le.mp hheight).1]
    · linarith [(abs_le.mp hheight).2]
  exact (hK.subset_connectedComponentIn hbase hregular) hxK

end PoincareConjecture.M28.CounterexampleNeckFamily
