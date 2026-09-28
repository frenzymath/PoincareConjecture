import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCriticalRegion
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





theorem normalizedSlice_fresh_core_compact (k : ℕ)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (rmin : ℝ) (hrmin : 0 < rmin)
    (hfloor : rmin ≤ Real.sqrt ((E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩) * N.scale)
    {p : ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier}
    (hp : p ∈ N.carrier)
    (hheight : |(N.coordinate_inverse p).2| ≤ 17 * N.epsilon⁻¹ / 24) :
    IsCompact (closure ((H.normalizedSliceMetric k).ball p
      (rmin * N.epsilon⁻¹ / 200))) ∧
      closure ((H.normalizedSliceMetric k).ball p (rmin * N.epsilon⁻¹ / 200)) ⊆
        {x | x ∈ N.carrier ∧ |(N.coordinate_inverse x).2| ≤ 3 * N.epsilon⁻¹ / 4} := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  let h := (N.coordinate_inverse p).2
  let w := N.epsilon⁻¹ / 48
  let R := (N.scale * Real.sqrt (1 - N.epsilon)) * w
  let K := N.coordinate_map '' (univ ×ˢ Icc (h - w) (h + w))
  have hQ : 0 < Q := H.base_scalar_pos k
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hw : 0 < w := div_pos hA (by norm_num)
  have hwA : w < N.epsilon⁻¹ - |(N.coordinate_inverse p).2| := by
    dsimp only [w]
    linarith only [hheight, hA]
  have hlo : -N.epsilon⁻¹ < h - w := by
    dsimp only [h, w]
    linarith [(abs_le.mp hheight).1]
  have hhi : h + w < N.epsilon⁻¹ := by
    dsimp only [h, w]
    linarith [(abs_le.mp hheight).2]
  have hK : IsCompact K := N.isCompact_coordinate_slab_intrinsic hlo hhi
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half])
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon), N.epsilon_lt_half]
  have hfactor : rmin / 2 ≤
      (Real.sqrt Q * N.scale) * Real.sqrt (1 - N.epsilon) := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul hfloor hroot (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (mul_nonneg (Real.sqrt_nonneg Q) N.scale_pos.le)
  have hradius : rmin * N.epsilon⁻¹ / 200 ≤ Real.sqrt Q * R := by
    have hm := mul_le_mul_of_nonneg_right hfactor hw.le
    dsimp only [R, w] at hm ⊢
    nlinarith only [hm, mul_pos hrmin hA]
  have hball : (H.normalizedSliceMetric k).ball p (Real.sqrt Q * R) =
      ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).ball p R := by
    have hh := M13.homothety_ball_image
      ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
      (H.normalizedSliceMetric k) (Diffeomorph.refl (𝓡 3) _ ∞) Q hQ
      (M13.identity_metricHomothety _ Q hQ) p R
    simpa using hh.symm
  have hballK : (H.normalizedSliceMetric k).ball p
      (rmin * N.epsilon⁻¹ / 200) ⊆ K := by
    intro x hx
    have hxR : x ∈ (H.normalizedSliceMetric k).ball p (Real.sqrt Q * R) :=
      hx.trans_le (ENNReal.ofReal_le_ofReal hradius)
    rw [hball] at hxR
    have hi := N.ball_subset_centered_region hp hw hwA hxR
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hi.2.1.le, hi.2.2.le⟩,
      N.coordinate_map_coordinate_inverse hi.1⟩
  have hclosure := closure_minimal hballK hK.isClosed
  refine ⟨hK.of_isClosed_subset isClosed_closure hclosure, hclosure.trans ?_⟩
  rintro x ⟨z, hz, rfl⟩
  have hzdom : z ∈ N.cylinderDomain :=
    ⟨mem_univ _, hlo.trans_le hz.2.1, hz.2.2.trans_lt hhi⟩
  refine ⟨N.coordinate_map_mem hzdom, ?_⟩
  rw [N.coordinate_inverse_coordinate_map hzdom]
  apply abs_le.mpr
  have hzl : h - w ≤ z.2 := hz.2.1
  have hzu : z.2 ≤ h + w := hz.2.2
  dsimp only [h, w] at hzl hzu
  constructor
  · linarith [(abs_le.mp hheight).1]
  · linarith [(abs_le.mp hheight).2]

variable (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ)





theorem tubeCritical_fresh_core_regular (k : ℕ)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (rmin : ℝ) (hrmin : 0 < rmin)
    (hfloor : rmin ≤ Real.sqrt ((E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩) * N.scale)
    (hslab : {x | x ∈ N.carrier ∧
        |(N.coordinate_inverse x).2| ≤ 3 * N.epsilon⁻¹ / 4} ⊆
      (Subtype.val : (T k).carrierOpen →
        ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier) ''
          (H.tubeCriticalRegion T A1 k : Set (T k).carrierOpen))
    (x : H.tubeCriticalRegion T A1 k)
    (hx : x.val.val ∈ N.carrier)
    (hheight : |(N.coordinate_inverse x.val.val).2| ≤ 17 * N.epsilon⁻¹ / 24) :
    x ∈ regularPoints (H.tubeCriticalMetric T A1 k) (rmin * N.epsilon⁻¹ / 200) := by
  obtain ⟨hcompact, hclosure⟩ :=
    H.normalizedSlice_fresh_core_compact k N rmin hrmin hfloor hx hheight
  have hcompactV := nested_intrinsicOpenMetric_isCompact_closure_ball
    (H.normalizedSliceMetric k) (T k).carrierOpen (H.tubeCriticalRegion T A1 k) x
    hcompact (hclosure.trans hslab)
  change IsCompact (closure ((H.tubeCriticalMetric T A1 k).ball x
    (rmin * N.epsilon⁻¹ / 200))) at hcompactV
  intro r hr
  apply hcompactV.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro y hy
  exact hy.trans_le (ENNReal.ofReal_le_ofReal hr.le)





theorem tubeCritical_fresh_core_component (hA1 : 0 < A1) (k : ℕ)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (rmin : ℝ) (hrmin : 0 < rmin)
    (hfloor : rmin ≤ Real.sqrt ((E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩) * N.scale)
    (hslab : {x | x ∈ N.carrier ∧
        |(N.coordinate_inverse x).2| ≤ 3 * N.epsilon⁻¹ / 4} ⊆
      (Subtype.val : (T k).carrierOpen →
        ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier) ''
          (H.tubeCriticalRegion T A1 k : Set (T k).carrierOpen))
    (q : H.tubeCriticalRegion T A1 k) (hcenter : N.center = q.val.val)
    {delta : ℝ} (hdelta : delta ≤ rmin * N.epsilon⁻¹ / 200)
    (hq : q ∈ regularComponent (H.tubeCriticalMetric T A1 k)
      (H.tubeCriticalBase T A1 hA1 k) delta)
    (x : H.tubeCriticalRegion T A1 k) (hx : x.val.val ∈ N.carrier)
    (hheight : |(N.coordinate_inverse x.val.val).2| ≤ 2 * N.epsilon⁻¹ / 3) :
    x ∈ regularComponent (H.tubeCriticalMetric T A1 k)
      (H.tubeCriticalBase T A1 hA1 k) delta := by
  let f : H.tubeCriticalRegion T A1 k →
      ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier :=
    fun y => y.val.val
  let O := N.region (-(17 * N.epsilon⁻¹ / 24)) (17 * N.epsilon⁻¹ / 24)
  let K := f ⁻¹' O
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hO : IsPreconnected O := N.isPreconnected_region (by linarith) (by linarith)
  have hrange : O ⊆ range f := by
    intro y hy
    have hh : |(N.coordinate_inverse y).2| ≤ 3 * N.epsilon⁻¹ / 4 := by
      have hh' := (abs_lt.mpr hy.2).le
      change |(N.coordinate_inverse y).2| ≤ 17 * N.epsilon⁻¹ / 24 at hh'
      linarith
    obtain ⟨z, hz, hzy⟩ := hslab ⟨hy.1, hh⟩
    exact ⟨⟨z, hz⟩, hzy⟩
  have hf : Topology.IsInducing f :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hK : IsPreconnected K := by
    apply hf.isPreconnected_image.mp
    change IsPreconnected (f '' (f ⁻¹' O))
    rw [image_preimage_eq_of_subset hrange]
    exact hO
  have hqK : q ∈ K := by
    change q.val.val ∈ O
    rw [← hcenter]
    exact N.central_sphere_subset_region (by linarith only [hA]) (by positivity)
      N.center_on_central_sphere
  have hregular : K ⊆ regularPoints (H.tubeCriticalMetric T A1 k) delta := by
    intro y hy
    apply regularPoints_antitone (H.tubeCriticalMetric T A1 k) hdelta
    exact H.tubeCritical_fresh_core_regular T A1 k N rmin hrmin hfloor hslab
      y hy.1 (abs_lt.mpr hy.2).le
  have hxK : x ∈ K := by
    change x.val.val ∈ O
    refine ⟨hx, ?_, ?_⟩
    · linarith [(abs_le.mp hheight).1]
    · linarith [(abs_le.mp hheight).2]
  change x ∈ connectedComponentIn (regularPoints (H.tubeCriticalMetric T A1 k) delta)
    (H.tubeCriticalBase T A1 hA1 k)
  rw [connectedComponentIn_eq hq]
  exact hK.subset_connectedComponentIn hqK hregular hxK

end PoincareConjecture.M28.CounterexampleNeckFamily
