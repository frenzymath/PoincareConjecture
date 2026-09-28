import PoincareConjecture.Proofs.M47.CanonicalNormalizedRadii
import PoincareConjecture.Proofs.M47.CanonicalModelVolumeMargin
import PoincareConjecture.Proofs.M34.Standard.CapBallVolumeRadius
import PoincareConjecture.Proofs.M15.Thm1_34_LocalVolume

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem cap_core_radii_bounded {g : RiemannianMetric 3 M} (N : CapCertificate g) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ y ∈ N.core, B⁻¹ ≤ N.core_radius y ∧ N.core_radius y ≤ B := by
  obtain ⟨m, hm, b, _, _, hlower, hratio⟩ := cap_uniform_scalar_lower N
  obtain ⟨o, ho⟩ := N.core_nonempty
  have hoc : o ∈ N.carrier := N.core_subset_carrier' ho
  let B := max 1 (max (b * N.connection.scalarCurvature o) m⁻¹)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  have hupperB : b * N.connection.scalarCurvature o ≤ B :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hinvB : m⁻¹ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hBm : B⁻¹ ≤ m := by
    have h := (inv_le_inv₀ hBpos (inv_pos.mpr hm)).mpr hinvB
    simpa only [inv_inv] using h
  refine ⟨B, hB1, ?_⟩
  intro y hy
  apply g.scalar_normalized_radius_bounds N.connection y (N.core_radius_pos y hy) hB1
    (N.core_radius_eq y hy)
  intro z hz
  have hzcarrier := N.core_ball_subset y hy (subset_closure hz)
  exact ⟨hBm.trans (hlower z hzcarrier), (hratio o hoc z hzcarrier).trans hupperB⟩

theorem cap_core_ball_volume_bound_persists [CompactSpace M] [SecondCountableTopology M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (t : Icc a b) (N : CapCertificate (F.metric t.val))
    (hconnection : N.connection = F.connection t.val) :
    ∃ b' : ℝ, N.cap_constant⁻¹ < b' ∧
      ∀ᶠ s : Icc a b in 𝓝 t, ∀ y ∈ N.core, ∀ r : ℝ, 0 < r →
        scalarCurvatureSupOn (F.metric s.val) (F.connection s.val)
          ((F.metric s.val).ball y r) = r⁻¹ ^ 2 →
        ENNReal.ofReal (b' * r ^ 3) ≤
          calibratedMetricVolume (F.metric s.val) ((F.metric s.val).ball y r) := by
  obtain ⟨B, hB1, hrange⟩ := cap_core_radii_bounded N
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  obtain ⟨b0, hb0, hvolume⟩ := N.core_ball_volume_lower
  have hCinv : 0 < N.cap_constant⁻¹ := inv_pos.mpr N.cap_constant_pos
  have hb0pos : 0 < b0 := hCinv.trans hb0
  let b' := (N.cap_constant⁻¹ + b0) / 2
  have hb' : N.cap_constant⁻¹ < b' := by dsimp [b']; linarith
  have hb'pos : 0 < b' := hCinv.trans hb'
  have hb'b0 : b' < b0 := by dsimp [b']; linarith
  let q := b' / b0
  have hq : 0 < q := div_pos hb'pos hb0pos
  have hq1 : q < 1 := (div_lt_one hb0pos).mpr hb'b0
  have hqb : q * b0 = b' := div_mul_cancel₀ b' hb0pos.ne'
  obtain ⟨K, hK, hRic⟩ := exists_compact_slab_ricci_bound F
  obtain ⟨Lambda, hLambda, hmodel⟩ := exists_model_volume_ratio_margin
    (b := B) hK.le (inv_pos.mpr hBpos) hq hq1
  have hLpos : 0 < Lambda := zero_lt_one.trans hLambda
  have hradii := cap_normalized_radii_close hC F t N hconnection hLambda
  obtain ⟨L, _, hcompare⟩ := exists_compact_slab_metric_volume_comparison F
  have hE : Continuous (fun s : Icc a b => Real.exp (L * |s.val - t.val|)) :=
    Real.continuous_exp.comp
      (continuous_const.mul ((continuous_subtype_val.sub continuous_const).abs))
  have hmetric : ∀ᶠ s : Icc a b in 𝓝 t, Real.exp (L * |s.val - t.val|) < Lambda :=
    hE.continuousAt.eventually (Iio_mem_nhds (by
      simpa only [sub_self, abs_zero, mul_zero, Real.exp_zero] using hLambda))
  refine ⟨b', hb', ?_⟩
  filter_upwards [hradii, hmetric] with s hs hEsmall
  intro y hy r hr hnorm
  obtain ⟨hrUpper, hrLower⟩ := hs y hy r hr hnorm
  let R := N.core_radius y
  have hR : 0 < R := N.core_radius_pos y hy
  let u := R / Lambda ^ 2
  have hu : 0 < u := div_pos hR (sq_pos_of_pos hLpos)
  have huR : u ≤ R := by
    apply (div_le_iff₀ (sq_pos_of_pos hLpos)).mpr
    have hLsq : 1 ≤ Lambda ^ 2 := one_le_pow₀ hLambda.le
    nlinarith
  have hballs : (F.metric t.val).ball y u ⊆ (F.metric s.val).ball y r := by
    intro z hz
    have hdist := ((hcompare t.val t.property s.val s.property).2.1 y z).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hEsmall.le) le_rfl)
    have hstrict := ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hLpos).ne'
      ENNReal.ofReal_ne_top (show (F.metric t.val).edist y z < ENNReal.ofReal u from hz)
    have hproduct : ENNReal.ofReal Lambda * ENNReal.ofReal u = ENNReal.ofReal (R / Lambda) := by
      rw [← ENNReal.ofReal_mul hLpos.le]
      congr 1
      dsimp [u]
      field_simp [hLpos.ne']
    rw [hproduct] at hstrict
    have hsmall : R / Lambda ≤ r := (div_le_iff₀ hLpos).mpr (by
      simpa only [R, mul_comm] using hrLower)
    exact hdist.trans_lt (hstrict.trans_le (ENNReal.ofReal_le_ofReal hsmall))
  have hlocalRic : ∀ z ∈ (F.metric t.val).ball y R, ∀ v : TangentSpace (𝓡 3) z,
      -(((3 : ℝ) - 1) * K) * (F.metric t.val).inner z v v ≤ (F.connection t.val).ricci z v v := by
    intro z _ v
    have hinner : 0 ≤ (F.metric t.val).inner z v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact ((F.metric t.val).pos z v hv).le
    have hlower := (abs_le.mp (hRic t.val t.property z v)).1
    nlinarith [mul_nonneg hK.le hinner]
  have hBG := M46.canonical_smallBall_volume_at_boundary (F.metric t.val) y
    (by norm_num : 1 ≤ 3) hK.le hu huR (N.core_ball_compact y hy)
    (F.connection t.val) hlocalRic
  rw [← M15.calibratedMetricVolume_eq_volumeMeasure (F.metric t.val)] at hBG
  have hden : 0 < RiemannianMetric.modelVolume 3 K R :=
    RiemannianMetric.modelVolume_pos (by norm_num : 1 ≤ 3) hK.le hR
  have hnum : 0 < RiemannianMetric.modelVolume 3 K u :=
    RiemannianMetric.modelVolume_pos (by norm_num : 1 ≤ 3) hK.le hu
  have hratio := hmodel R (hrange y hy)
  have hsmallVolume : ENNReal.ofReal (q * Lambda ^ 6 * b0 * R ^ 3) ≤
      calibratedMetricVolume (F.metric t.val) ((F.metric t.val).ball y u) := by
    apply (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio.le hb0pos.le)
        (pow_nonneg hR.le 3))).trans
    rw [mul_assoc _ b0 (R ^ 3),
      ENNReal.ofReal_mul (div_pos hnum hden).le, ENNReal.ofReal_div_of_pos hden]
    exact (mul_le_mul' le_rfl (hvolume y hy)).trans hBG
  have hvolumeBack : calibratedMetricVolume (F.metric t.val) ((F.metric t.val).ball y u) ≤
      ENNReal.ofReal Lambda ^ 3 * calibratedMetricVolume (F.metric s.val)
        ((F.metric s.val).ball y r) := by
    have h := (hcompare s.val s.property t.val t.property).2.2 ((F.metric t.val).ball y u)
    rw [abs_sub_comm t.val s.val] at h
    apply h.trans
    exact mul_le_mul' (ENNReal.pow_le_pow_left (ENNReal.ofReal_le_ofReal hEsmall.le))
      (measure_mono hballs)
  have hweighted := hsmallVolume.trans hvolumeBack
  rw [← ENNReal.ofReal_pow hLpos.le] at hweighted
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (pow_pos hLpos 3)).ne'
    ENNReal.ofReal_ne_top).mp
  have hcube : r ^ 3 ≤ Lambda ^ 3 * R ^ 3 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hr.le hrUpper 3
  have hreal : Lambda ^ 3 * (b' * r ^ 3) ≤ q * Lambda ^ 6 * b0 * R ^ 3 := by
    calc
      _ ≤ Lambda ^ 3 * (b' * (Lambda ^ 3 * R ^ 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcube hb'pos.le)
          (pow_nonneg hLpos.le 3)
      _ = _ := by rw [← hqb]; ring
  calc
    ENNReal.ofReal (Lambda ^ 3) * ENNReal.ofReal (b' * r ^ 3) =
        ENNReal.ofReal (Lambda ^ 3 * (b' * r ^ 3)) :=
      (ENNReal.ofReal_mul (pow_nonneg hLpos.le 3)).symm
    _ ≤ ENNReal.ofReal (q * Lambda ^ 6 * b0 * R ^ 3) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ _ := hweighted

end PoincareConjecture.Proofs.M47
