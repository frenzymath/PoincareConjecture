import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RadialScalar
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

theorem m64Intrinsic_scalar_jacobi_pos_before_pi
    {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ) (hRpi : κ * R < Real.pi)
    {J J' J'' k : ℝ → ℝ}
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hzero : J 0 = 0) (hinitial : 0 < J' 0)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) R, J'' t + k t * J t = 0)
    (hk : ∀ t ∈ Ioo (0 : ℝ) R, k t ≤ κ ^ 2) :
    ∀ t ∈ Ioc (0 : ℝ) R, 0 < J t := by
  have hJc : ContinuousOn J (Icc (0 : ℝ) R) :=
    fun t ht => (hJ t ht).continuousAt.continuousWithinAt
  have hslope : Tendsto (fun t => J t / t) (𝓝[>] 0) (𝓝 (J' 0)) := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
      using (hJ 0 ⟨le_rfl, hR.le⟩).tendsto_slope_zero_right
  have hlocal : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < J t := by
    filter_upwards [hslope.eventually (Ioi_mem_nhds hinitial),
      self_mem_nhdsWithin] with t ht hpos
    exact (div_pos_iff_of_pos_right (show 0 < t from hpos)).mp ht
  obtain ⟨a, ha, hapos⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hlocal
  change 0 < a at ha
  intro t ht
  by_contra hnot
  have htbad : J t ≤ 0 := le_of_not_gt hnot
  let d : ℝ := min a t / 2
  have hd : 0 < d := half_pos (lt_min ha ht.1)
  have hda : d ≤ a := (half_le_self (lt_min ha ht.1).le).trans (min_le_left a t)
  have hdt : d < t := (half_lt_self (lt_min ha ht.1)).trans_le (min_le_right a t)
  have hdJ : 0 < J d := hapos ⟨hd, hda⟩
  let S : Set ℝ := Icc d t ∩ J ⁻¹' Iic 0
  have hSc : IsCompact S := by
    apply (isCompact_Icc : IsCompact (Icc d t)).of_isClosed_subset
    · exact (hJc.mono (Icc_subset_Icc hd.le ht.2)).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_Iic
    · exact inter_subset_left
  have hSne : S.Nonempty := ⟨t, ⟨⟨hdt.le, le_rfl⟩, htbad⟩⟩
  obtain ⟨c, hc, hmin⟩ := hSc.exists_isLeast hSne
  have hdc : d < c := by
    refine lt_of_le_of_ne hc.1.1 ?_
    intro heq
    exact (not_le_of_gt hdJ) (heq ▸ hc.2)
  have hcpos : 0 < c := hd.trans hdc
  have hcR : c ≤ R := hc.1.2.trans ht.2
  have hbefore (s : ℝ) (hs : s ∈ Ioo 0 c) : 0 < J s := by
    by_cases hsd : s ≤ d
    · exact hapos ⟨hs.1, hsd.trans hda⟩
    · by_contra hsJ
      have hsS : s ∈ S := ⟨⟨(lt_of_not_ge hsd).le,
        hs.2.le.trans hc.1.2⟩, le_of_not_gt hsJ⟩
      exact (not_le_of_gt hs.2) (hmin hsS)
  have hW := m64Intrinsic_scaled_spherical_wronskian_nonneg_of_jacobi
    hcpos hκ.le ((mul_le_mul_of_nonneg_left hcR hκ.le).trans hRpi.le)
    (fun s hs => hJ s ⟨hs.1, hs.2.trans hcR⟩)
    (hJ'.mono (Icc_subset_Icc le_rfl hcR))
    (fun s hs => hJ'' s ⟨hs.1, hs.2.trans_le hcR⟩) hzero
    (fun s hs => (hbefore s hs).le)
    (fun s hs => hjac s ⟨hs.1, hs.2.trans_le hcR⟩)
    (fun s hs => hk s ⟨hs.1, hs.2.trans_le hcR⟩)
  have hsin (s : ℝ) (hs : s ∈ Icc d c) : 0 < Real.sin (κ * s) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos hκ (hd.trans_le hs.1)
    · exact (mul_le_mul_of_nonneg_left (hs.2.trans hcR) hκ.le).trans_lt hRpi
  have hsinD (s : ℝ) : HasDerivAt (fun u => Real.sin (κ * u))
      (κ * Real.cos (κ * s)) s := by
    simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using
      (Real.hasDerivAt_sin (κ * s)).comp s ((hasDerivAt_id s).const_mul κ)
  have hmono : MonotoneOn (fun s => J s / Real.sin (κ * s)) (Icc d c) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      ((hJc.mono (Icc_subset_Icc hd.le hcR)).div
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
        (fun s hs => (hsin s hs).ne'))
      (fun s hs => ((hJ s (by
        have hs' : s ∈ Ioo d c := by simpa only [interior_Icc] using hs
        exact ⟨hd.le.trans hs'.1.le, hs'.2.le.trans hcR⟩)).div (hsinD s)
        ((hsin s (by simpa only [interior_Icc] using interior_subset hs)).ne')).hasDerivWithinAt)
    intro s hs
    have hs' : s ∈ Ioo d c := by simpa only [interior_Icc] using hs
    apply div_nonneg _ (sq_nonneg _)
    have hws := hW s ⟨hd.le.trans hs'.1.le, hs'.2.le⟩
    nlinarith
  have hquot : J d / Real.sin (κ * d) ≤ J c / Real.sin (κ * c) :=
    hmono ⟨le_rfl, hdc.le⟩ ⟨hdc.le, le_rfl⟩ hdc.le
  have hleft : 0 < J d / Real.sin (κ * d) := div_pos hdJ (hsin d ⟨le_rfl, hdc.le⟩)
  have hright : J c / Real.sin (κ * c) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hc.2 (hsin c ⟨hdc.le, le_rfl⟩).le
  linarith

theorem m64Intrinsic_scalar_jacobi_ne_zero_before_pi
    {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ) (hRpi : κ * R < Real.pi)
    {J J' J'' k : ℝ → ℝ}
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hzero : J 0 = 0) (hinitial : J' 0 ≠ 0)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) R, J'' t + k t * J t = 0)
    (hk : ∀ t ∈ Ioo (0 : ℝ) R, k t ≤ κ ^ 2) :
    ∀ t ∈ Ioc (0 : ℝ) R, J t ≠ 0 := by
  rcases lt_or_gt_of_ne hinitial with hneg | hpos
  · have hp := m64Intrinsic_scalar_jacobi_pos_before_pi hR hκ hRpi
      (J := -J) (J' := -J') (J'' := -J'') (k := k)
      (fun t ht => (hJ t ht).neg) hJ'.neg (fun t ht => (hJ'' t ht).neg)
      (by simp only [Pi.neg_apply, hzero, neg_zero]) (neg_pos.mpr hneg)
      (fun t ht => by
        simp only [Pi.neg_apply]
        nlinarith [hjac t ht]) hk
    intro t ht
    exact (neg_pos.mp (hp t ht)).ne
  · exact fun t ht => (m64Intrinsic_scalar_jacobi_pos_before_pi hR hκ hRpi
      hJ hJ' hJ'' hzero hpos hjac hk t ht).ne'

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_mfderiv_injective_of_pullbackDensity_pos
    (N : IntrinsicAnnulus) {e : AnnulusCoordinates → AnnulusCoordinates}
    {x : AnnulusCoordinates} (he : ContMDiffAt (𝓡 2) (𝓡 2) ∞ e x)
    (hp : 0 < N.metric.pullbackVolumeDensity e x) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 2) e x) := by
  have hdensity := N.metric.pullbackVolumeDensity_comp (f := id)
    mdifferentiableAt_id ((contMDiffAt_iff_contDiffAt.mp he).differentiableAt (by simp))
  have hdet : (fderiv ℝ e x).det ≠ 0 := by
    intro hzero
    simp only [Function.id_comp, hzero, abs_zero, zero_mul] at hdensity
    exact hp.ne' hdensity
  rw [mfderiv_eq_fderiv]
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)

theorem m64Intrinsic_radial_mfderiv_injective_of_gaussian_upper
    (N : IntrinsicAnnulus) (K κ : ℝ) (hK : N.GaussianCurvatureBound K)
    (hκ : 0 < κ) (hKκ : K ≤ κ ^ 2)
    {e : AnnulusCoordinates → AnnulusCoordinates} {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (h0 : (0 : AnnulusCoordinates) ∈ U)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    (hgeo : ∀ v ∈ U,
      N.metric.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 v) = inner ℝ u v)
    (theta : AnnulusCoordinates) (htheta : ‖theta‖ = 1)
    {b : ℝ} (hb : 0 < b) (hbpi : κ * b < Real.pi)
    (hsub : ∀ s ∈ Icc 0 b, s • theta ∈ U)
    (hmap : ∀ s ∈ Ioo 0 b, e (s • theta) ∈ standardAnnulusDomain) :
    ∀ s ∈ Icc 0 b,
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (s • theta)) := by
  obtain ⟨j, v, hjzero, hj, hv, _hjc, hdensity⟩ :=
    m64Intrinsic_exists_radial_scalar_jacobi N hU h0 he hgeo hmetric theta htheta hb hsub
  let y : ℝ → ℝ := fun s => s * N.metric.pullbackVolumeDensity e (s • theta)
  have hyd : HasDerivAt y 1 0 := by
    simpa only [Nat.cast_one, div_one, Real.rpow_one] using
      N.metric.hasDerivAt_signed_polarDensityRoot_zero
        (he.contMDiffAt (hU.mem_nhds h0)) hmetric theta 1
  have hjlim : Tendsto (fun s => j s / s) (𝓝[>] 0) (𝓝 (v 0)) := by
    simpa only [zero_add, hjzero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
      using (hj 0 ⟨le_rfl, hb.le⟩).tendsto_slope_zero_right
  have hylim : Tendsto (fun s => y s / s) (𝓝[>] 0) (𝓝 1) := by
    simpa only [zero_add, y, zero_mul, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
      using hyd.tendsto_slope_zero_right
  have habslim : Tendsto (fun s => |j s / s|) (𝓝[>] 0) (𝓝 1) := by
    apply hylim.congr'
    filter_upwards [Ioo_mem_nhdsGT hb] with s hs
    rw [abs_div, abs_of_pos hs.1, hdensity s ⟨hs.1, hs.2.le⟩]
  have hvabs : |v 0| = 1 := tendsto_nhds_unique hjlim.abs habslim
  have hvne : v 0 ≠ 0 := by
    intro hzero
    simp only [hzero, abs_zero] at hvabs
    norm_num at hvabs
  have hjne := m64Intrinsic_scalar_jacobi_ne_zero_before_pi hb hκ hbpi hj
    (fun s hs => (hv s hs).continuousAt.continuousWithinAt)
    (fun s hs => hv s ⟨hs.1.le, hs.2.le⟩) hjzero hvne
    (k := fun s => N.connection.scalarCurvature (e (s • theta)) / 2)
    (fun s _hs => by ring)
    (fun s hs => (hK (e (s • theta)) (hmap s hs)).trans hKκ)
  intro s hs
  apply m64Intrinsic_mfderiv_injective_of_pullbackDensity_pos N
    (he.contMDiffAt (hU.mem_nhds (hsub s hs)))
  rcases hs.1.eq_or_lt with rfl | hpos
  · simpa only [zero_smul, N.metric.pullbackVolumeDensity_zero_eq_one e hmetric]
      using zero_lt_one
  · have hp : 0 < s * N.metric.pullbackVolumeDensity e (s • theta) := by
      rw [← hdensity s ⟨hpos, hs.2⟩]
      exact abs_pos.mpr (hjne s ⟨hpos, hs.2⟩)
    exact (mul_pos_iff_of_pos_left hpos).mp hp

end PoincareConjecture
