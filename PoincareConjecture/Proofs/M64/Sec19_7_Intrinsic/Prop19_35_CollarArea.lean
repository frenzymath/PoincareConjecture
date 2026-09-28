import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_GlobalOpenStrip
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalLocalChart
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InjectiveStripArea
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AreaLoss
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem normal_coordinate_differential_injective
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u)
    {z : AnnulusCoordinates} (hi : Function.Injective (fderiv ℝ u (z 0, z 1))) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 2)
      (fun x : AnnulusCoordinates => u (x 0, x 1)) z) := by
  have hfd : Function.Injective (fderiv ℝ
      (fun x : AnnulusCoordinates => u (x 0, x 1)) z) := by
    intro v w hvw
    have hz : !₂[z 0, z 1] = z := by
      ext i
      fin_cases i <;> rfl
    have hv := m64Intrinsic_normal_coordinate_differential
      (hu.differentiable (by simp) (z 0, z 1)) v
    have hw := m64Intrinsic_normal_coordinate_differential
      (hu.differentiable (by simp) (z 0, z 1)) w
    rw [hz] at hv hw
    rw [hv, hw] at hvw
    have hcoords := hi hvw
    ext i
    fin_cases i
    · exact congrArg Prod.fst hcoords
    · exact congrArg Prod.snd hcoords
  rw [mfderiv_eq_fderiv]
  apply LinearMap.ker_eq_bot.mp
  exact LinearMap.ker_eq_bot.mpr hfd





theorem m64Intrinsic_exists_embedded_collar_area_bound (N : IntrinsicAnnulus) :
    ∃ (u : ℝ × ℝ → AnnulusCoordinates) (r c : ℝ),
      0 < r ∧ r ≤ 1 ∧ 0 < c ∧ ContDiff ℝ ∞ u ∧
      (∀ a, u (a, 0) = intrinsicAnnulusBoundary 1 a) ∧
      InjOn u (Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) r) ∧
      ∀ (S : Set ℝ) (height : ℝ → ℝ), MeasurableSet S → Measurable height →
        S ⊆ Ico (0 : ℝ) rampPeriod →
        (∀ s ∈ S, 0 ≤ height s ∧ height s ≤ r) →
        ENNReal.ofReal (c ^ 2) *
          (∫⁻ s in S, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 s) *
            ENNReal.ofReal (height s)) ≤
          ENNReal.ofReal (intrinsicAnnulusArea N.metric) := by
  obtain ⟨normal, u, r, hr, hrone, _, hu, _, hboundary, _, hinj, hregular, _⟩ :=
    m64Intrinsic_exists_embedded_normal_collar N
  let e : AnnulusCoordinates → AnnulusCoordinates := fun z => u (z 0, z 1)
  have he : ContDiff ℝ ∞ e := hu.comp (by fun_prop)
  let K : Set AnnulusCoordinates :=
    {z | z 0 ∈ Icc (0 : ℝ) rampPeriod ∧ z 1 ∈ Icc (0 : ℝ) r}
  have hKclosed : IsClosed K := by
    have h0 : Continuous (fun z : AnnulusCoordinates => z 0) := by fun_prop
    have h1 : Continuous (fun z : AnnulusCoordinates => z 1) := by fun_prop
    exact (isClosed_Icc.preimage h0).inter (isClosed_Icc.preimage h1)
  have hKsub : K ⊆ m64AnnulusDomain := by
    intro z hz
    exact ⟨hz.1.1, hz.1.2, hz.2.1, hz.2.2.trans hrone⟩
  have hK : IsCompact K :=
    IsCompact.of_isClosed_subset m64AnnulusDomain_isCompact hKclosed hKsub
  have hKne : K.Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨⟨le_rfl, Real.two_pi_pos.le⟩, ⟨le_rfl, hr.le⟩⟩
  have hdensity (z : AnnulusCoordinates) (hz : z ∈ K) :
      ContDiffAt ℝ ∞ (N.metric.pullbackVolumeDensity e) z ∧
        0 < N.metric.pullbackVolumeDensity e z := by
    apply N.metric.contDiffAt_pullbackVolumeDensity
    · exact contMDiffAt_iff_contDiffAt.mpr he.contDiffAt
    · exact normal_coordinate_differential_injective hu (hregular _ hz.1 _ hz.2).1
  let ratio : AnnulusCoordinates → ℝ := fun z =>
    N.metric.pullbackVolumeDensity e z / intrinsicBoundarySpeed N.metric 1 (z 0)
  have hspeed : Continuous (intrinsicBoundarySpeed N.metric 1) :=
    (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
  have hc0 : Continuous (fun z : AnnulusCoordinates => z 0) := by fun_prop
  have hratio : ContinuousOn ratio K := by
    intro z hz
    exact ((hdensity z hz).1.continuousAt.div
      (hspeed.comp hc0).continuousAt
      (m64Intrinsic_boundarySpeed_pos N (by norm_num : (1 : ℝ) ≠ 0) (z 0)).ne').continuousWithinAt
  have hratio_pos (z : AnnulusCoordinates) (hz : z ∈ K) : 0 < ratio z :=
    div_pos (hdensity z hz).2
      (m64Intrinsic_boundarySpeed_pos N (by norm_num : (1 : ℝ) ≠ 0) (z 0))
  obtain ⟨zmin, hzmin, hmin⟩ := hK.exists_isMinOn hKne hratio
  let c := Real.sqrt (ratio zmin)
  have hc : 0 < c := Real.sqrt_pos.mpr (hratio_pos zmin hzmin)
  have hc2 : c ^ 2 = ratio zmin := Real.sq_sqrt (hratio_pos zmin hzmin).le
  have hlower (z : AnnulusCoordinates) (hz : z ∈ K) :
      c ^ 2 * intrinsicBoundarySpeed N.metric 1 (z 0) ≤
        N.metric.pullbackVolumeDensity e z := by
    rw [hc2]
    exact (le_div_iff₀
      (m64Intrinsic_boundarySpeed_pos N (by norm_num : (1 : ℝ) ≠ 0) (z 0))).mp (hmin hz)
  refine ⟨u, r, c, hr, hrone, hc, hu, hboundary, hinj, ?_⟩
  intro S height hS hheight hSsub hheight_bound
  let D : Set AnnulusCoordinates :=
    {z | z 0 ∈ S ∧ z 1 ∈ Icc (0 : ℝ) (height (z 0))}
  have hD : MeasurableSet D := by
    have hp0 : Measurable (fun z : AnnulusCoordinates => z 0) := by fun_prop
    have hp1 : Measurable (fun z : AnnulusCoordinates => z 1) := by fun_prop
    exact (hS.preimage hp0).inter ((measurableSet_le measurable_const hp1).inter
      (measurableSet_le hp1 (hheight.comp hp0)))
  have hDK : D ⊆ K := by
    intro z hz
    exact ⟨Ico_subset_Icc_self (hSsub hz.1),
      ⟨hz.2.1, hz.2.2.trans (hheight_bound _ hz.1).2⟩⟩
  have hDinj : InjOn e D := by
    intro z hz w hw heq
    have hp := hinj ⟨hSsub hz.1, (hDK hz).2⟩
      ⟨hSsub hw.1, (hDK hw).2⟩ heq
    ext i
    fin_cases i
    · exact congrArg Prod.fst hp
    · exact congrArg Prod.snd hp
  have himage : e '' D ⊆ standardAnnulusDomain := by
    rintro z ⟨x, hx, rfl⟩
    exact (hregular _ (hDK hx).1 _ (hDK hx).2).2.1
  have hvolume := m64Intrinsic_volume_image_of_injective N.metric hD
    (fun x _ => he.differentiable (by simp) x) hDinj
  have harea := m64Intrinsic_region_volume_le_area N.metric himage
  have hintegral : (∫⁻ z in D,
      ENNReal.ofReal (c ^ 2 * intrinsicBoundarySpeed N.metric 1 (z 0))) ≤
        ENNReal.ofReal (intrinsicAnnulusArea N.metric) := by
    calc
      _ ≤ ∫⁻ z in D, ENNReal.ofReal (N.metric.pullbackVolumeDensity e z) := by
        apply setLIntegral_mono' hD
        intro z hz
        exact ENNReal.ofReal_le_ofReal (hlower z (hDK hz))
      _ = N.metric.volumeMeasure (e '' D) := hvolume.symm
      _ ≤ ENNReal.ofReal (intrinsicAnnulusArea N.metric) := by
        rw [← ENNReal.ofReal_toReal harea.1.ne]
        exact ENNReal.ofReal_le_ofReal harea.2
  simp_rw [ENNReal.ofReal_mul (sq_nonneg c)] at hintegral
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    m64Intrinsic_parameter_strip_integral hS hheight hspeed.measurable] at hintegral
  exact hintegral




theorem m64Intrinsic_exists_embedded_collar_area_cutoff (N : IntrinsicAnnulus) :
    ∃ (u : ℝ × ℝ → AnnulusCoordinates) (rho c : ℝ),
      0 < rho ∧ rho ≤ 1 ∧ 0 < c ∧ ContDiff ℝ ∞ u ∧
      (∀ a, u (a, 0) = intrinsicAnnulusBoundary 1 a) ∧
      InjOn u (Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) rho) ∧
      ∀ (S : Set ℝ) (height : ℝ → ℝ), MeasurableSet S → Measurable height →
        S ⊆ Ico (0 : ℝ) rampPeriod →
        (∀ s ∈ S, 0 ≤ height s ∧ height s ≤ rho) →
        ∀ R : ℝ, 0 < R →
          m64IntrinsicLongFiberLength N S height R ≤
            intrinsicAnnulusArea N.metric / (c ^ 2 * R) ∧
          ∀ r : ℝ, r < intrinsicBoundaryLength N.metric 1 0 rampPeriod →
            intrinsicAnnulusArea N.metric < c ^ 2 * R * (r / 10) →
            m64IntrinsicLongFiberLength N S height R <
              intrinsicBoundaryLength N.metric 1 0 rampPeriod / 10 := by
  obtain ⟨u, rho, c, hrho, hrhoone, hc, hu, hboundary, hinj, harea⟩ :=
    m64Intrinsic_exists_embedded_collar_area_bound N
  refine ⟨u, rho, c, hrho, hrhoone, hc, hu, hboundary, hinj, ?_⟩
  intro S height hS hheight hSsub hheight_bound R hR
  have hsub : S ⊆ Icc (0 : ℝ) rampPeriod := hSsub.trans Ico_subset_Icc_self
  have hbound := harea S height hS hheight hSsub hheight_bound
  refine ⟨m64Intrinsic_long_fiber_length_le N hS hsub hheight hc hR hbound, ?_⟩
  intro r hfirst hsmall
  exact m64Intrinsic_long_fiber_length_lt_tenth N hS hsub hheight hc hR
    hfirst hbound hsmall

end PoincareConjecture
