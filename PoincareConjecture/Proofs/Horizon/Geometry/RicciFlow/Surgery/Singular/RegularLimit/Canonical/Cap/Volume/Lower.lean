import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Volume.ScaleRange
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Volume.SmallerBall
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.EnlargedOldBalls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.RadiusBound
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.VolumeComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.ModelVolumeComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem exists_eventually_captured_cap_terminal_core_volume_lower
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀) :
    ∃ cmax : ℝ, 1 < cmax ∧ ∀ c : ℝ, 1 < c → c < cmax →
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t),
          N.epsilon ≤ CapCertificate.coreBallClearanceThreshold.{u} →
          N.cap_constant ≤ H.constant → N.connection = F.connection t →
          H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
          H.reference.forward t ht x₀ ∈ N.core →
          ∀ x : H.regularRegion P04, H.reference.forward t ht x ∈ N.core →
          ∀ r' : ℝ, N.core_radius (H.reference.forward t ht x) / c ≤ r' →
            r' ≤ c * N.core_radius (H.reference.forward t ht x) →
            ENNReal.ofReal ((3 / (4 * H.constant)) * r' ^ 3) ≤
              calibratedMetricVolume (H.terminalMetric P04) ((H.terminalMetric P04).ball x r') := by
  obtain ⟨B, hB, hbounds⟩ := H.exists_eventually_captured_cap_scalar_upper P04 hA
  let K := 13 * max B (Real.exp 4)
  have hK : 0 < K := by dsimp [K]; positivity
  let m := (H.terminalConnection P04).scalarCurvature x₀ / 2
  have hm : 0 < m := half_pos hx₀
  let L := H.constant / m + 1
  have hL : 0 < L := by dsimp [L]; positivity [H.constant_pos]
  have hscale : H.constant ≤ m * L ^ 2 := by
    have hcancel : m * (H.constant / m) = H.constant := mul_div_cancel₀ _ (ne_of_gt hm)
    have hnonneg := mul_nonneg hm.le (sq_nonneg (H.constant / m))
    dsimp only [L]
    nlinarith [H.constant_pos]
  obtain ⟨cmax, hcmax, hratio⟩ := SingularRegularLimit.exists_modelVolume_ratio_margin
    (L := L) hK.le (inv_pos.mpr (by positivity : 0 < B + 1))
  obtain ⟨δ, hδ, henlarge⟩ := H.exists_eventually_cap_core_enlarged_old_balls P04 hA x₀ hx₀
  refine ⟨cmax, hcmax, ?_⟩
  intro c hc hccmax
  have hcpos := zero_lt_one.trans hc
  have hbase : ∀ᶠ t in 𝓝[<] T, m < H.reference.scalar t x₀ :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually_const_lt (half_lt_self hx₀)
  filter_upwards [hbounds, henlarge, hbase,
    H.eventually_terminal_calibratedVolume_comparison P04 hA hc,
    H.eventually_terminal_tangentNorm_comparison P04 hA hc]
    with t hbounds henlarge hbase hvolume hnorm
  intro ht N hε hconstant hconnection hcapture hx₀core x hxcore r' hr'low hr'high
  let y := H.reference.forward t ht x
  let r := N.core_radius y
  have hr : 0 < r := N.core_radius_pos y hxcore
  have hr' : 0 < r' := (div_pos hr hcpos).trans_le hr'low
  obtain ⟨hscalar, hcurv, hlower⟩ := hbounds ht N hconnection hcapture
  have hbase' : m ≤ N.connection.scalarCurvature (H.reference.forward t ht x₀) := by
    rw [hconnection]
    exact (H.reference.scalar_pullback t ht x₀).symm ▸ hbase.le
  have hrL : r ≤ L := (N.core_radius_lt_of_scalar_lower hconstant hm hL hscale
    (N.core_subset_carrier hx₀core) hbase' hxcore).le
  have hmodel := hratio c hc hccmax r ⟨hlower y hxcore, hrL⟩
  let q := r / c ^ 2
  have hq : 0 < q := div_pos hr (pow_pos hcpos 2)
  have hqr : q ≤ r := by
    apply (div_le_iff₀ (pow_pos hcpos 2)).mpr
    nlinarith [mul_pos hr (show 0 < c ^ 2 - 1 by nlinarith)]
  obtain ⟨hclosed, hcompact⟩ := henlarge ht N hε hconstant hconnection hcapture hx₀core y hxcore
  have hsmallvol := N.core_ball_smaller_volume_lower hconstant hK.le
    (by intro z hz; simpa only [hconnection] using hcurv z hz) hxcore
    (by change r < r + δ; linarith) hcompact (fun z hz => hclosed (subset_closure hz)) hq hqr
  let S := H.regularReferencePreimage P04 t ht ((F.metric t).ball y q)
  have hballN : (F.metric t).ball y q ⊆ N.carrier := by
    intro z hz
    apply N.core_ball_subset y hxcore
    exact subset_closure (hz.trans_le (ENNReal.ofReal_le_ofReal hqr))
  have hcaptureS := (image_mono hballN).trans hcapture
  have hSA : S ⊆ A := H.regularReferencePreimage_subset P04 t ht _ hcaptureS
  have hregular : H.reference.inverse t ht '' (F.metric t).ball y q ⊆
      H.reference.regularLimitSet := by
    rintro z hz
    obtain ⟨a, _, rfl⟩ := hcaptureS hz
    exact a.property
  have hballEq : S = ((H.terminalFlow P04).metric t).ball x q :=
    H.regularReferencePreimage_ball_eq P04 t ht x q hregular
  have hSopen : IsOpen S := by
    rw [hballEq]
    let g := (H.terminalFlow P04).metric t
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : H.regularRegion P04 → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : H.regularRegion P04 → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace (H.regularRegion P04) := EMetricSpace.ofRiemannianMetric (𝓡 3) _
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hSball : S ⊆ (H.terminalMetric P04).ball x r' := by
    have hsub := RiemannianMetric.ball_subset_ball_of_tangentNorm_le
      ((H.terminalFlow P04).metric t) (H.terminalMetric P04) x q c hcpos
      (fun z hz v => (hnorm z (hSA (hballEq.symm ▸ hz)) v).1)
    rw [← hballEq] at hsub
    have hcr : c * q = r / c := by dsimp [q]; field_simp
    rw [hcr] at hsub
    exact fun z hz => (hsub hz).trans_le (ENNReal.ofReal_le_ofReal hr'low)
  have himage : (fun z : H.regularRegion P04 => H.reference.forward t ht z) '' S =
      (F.metric t).ball y q := by
    apply subset_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz
    · intro z hz
      let a : H.regularRegion P04 := ⟨H.reference.inverse t ht z, hregular ⟨z, hz, rfl⟩⟩
      have haz : H.reference.forward t ht a = z := H.reference.right_inverse t ht z
      refine ⟨a, ?_, haz⟩
      change H.reference.forward t ht a ∈ (F.metric t).ball y q
      rwa [haz]
  have hmeasure := H.terminalFlow_reference_calibratedVolume P04 ht hSopen.measurableSet
  rw [himage] at hmeasure
  have hcompare := (hvolume S hSopen.measurableSet hSA).2
  rw [← hmeasure] at hcompare
  have hreal : c ^ 3 * (3 / (4 * H.constant) * r' ^ 3) ≤
      (RiemannianMetric.modelVolume 3 K q / RiemannianMetric.modelVolume 3 K r) *
        (H.constant⁻¹ * r ^ 3) := by
    have hpower : r' ^ 3 ≤ c ^ 3 * r ^ 3 := by
      simpa only [mul_pow] using pow_le_pow_left₀ hr'.le hr'high 3
    have hcoef : 0 < c ^ 3 * (3 / (4 * H.constant)) := by positivity [H.constant_pos]
    have hbound := mul_le_mul_of_nonneg_left hpower hcoef.le
    have hstrict := mul_le_mul_of_nonneg_right hmodel.le
      (mul_pos (inv_pos.mpr H.constant_pos) (pow_pos hr 3)).le
    calc
      _ ≤ c ^ 3 * (3 / (4 * H.constant)) * (c ^ 3 * r ^ 3) := by
        simpa only [mul_assoc] using hbound
      _ = ((3 / 4 : ℝ) * c ^ 6) * (H.constant⁻¹ * r ^ 3) := by ring
      _ ≤ _ := hstrict
  have hfirst : ENNReal.ofReal c ^ 3 * ENNReal.ofReal (3 / (4 * H.constant) * r' ^ 3) ≤
      ENNReal.ofReal (RiemannianMetric.modelVolume 3 K q /
        RiemannianMetric.modelVolume 3 K r) * ENNReal.ofReal (H.constant⁻¹ * r ^ 3) := by
    rw [← ENNReal.ofReal_pow hcpos.le, ← ENNReal.ofReal_mul (pow_pos hcpos 3).le,
      ← ENNReal.ofReal_mul (div_nonneg
        (RiemannianMetric.modelVolume_pos (by norm_num) hK.le hq).le
        (RiemannianMetric.modelVolume_pos (by norm_num) hK.le hr).le)]
    exact ENNReal.ofReal_le_ofReal hreal
  apply (ENNReal.mul_le_mul_iff_right
    (pow_ne_zero 3 (ENNReal.ofReal_pos.mpr hcpos).ne')
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mp
  exact hfirst.trans (hsmallvol.trans (hcompare.trans
    (mul_le_mul_right (by
      simpa only [Generalized.Noncollapse.calibratedMetricVolume_eq_volumeMeasure]
        using measure_mono hSball) _)))

end PoincareConjecture.SingularTimeAssumptions
