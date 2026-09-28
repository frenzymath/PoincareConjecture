import PoincareConjecture.Proofs.M01.NormalizationChartDistance
import PoincareConjecture.Proofs.M01.NormalizationSmallBallMeasure
import PoincareConjecture.Proofs.M01.NormalizationPinching

set_option autoImplicit false

open Bundle Manifold MeasureTheory Metric Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace PoincareConjecture

section

variable {M F : Type*} [EMetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem m01_hausdorff_metricBall_le (e : OpenPartialHomeomorph M F)
    (C : ℝ≥0) (hC : 1 < C) (a₀ : F) {R : ℝ}
    (htarget : Metric.ball a₀ R ⊆ e.target)
    (hinv : LipschitzOnWith C e.symm (Metric.ball a₀ R))
    (hfwd : LipschitzOnWith C e (e.symm '' Metric.ball a₀ R))
    (y : M) (hy : y ∈ e.source) (hycoord : e y ∈ Metric.ball a₀ (R / 2))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R / 2) :
    Measure.hausdorffMeasure (3 : ℝ) (Metric.ball (e y) (r / (C : ℝ))) ≤
      (C : ℝ≥0∞) ^ 3 * Measure.hausdorffMeasure (3 : ℝ)
        (Metric.eball y (ENNReal.ofReal r)) := by
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (zero_lt_one.trans hC)
  have hCne : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hC).ne'
  have hfrac : r / (C : ℝ) ≤ R / 2 :=
    (div_le_self hr.le (by exact_mod_cast hC.le)).trans hrR
  have hR : 0 < R := by linarith
  have hyouter : e y ∈ Metric.ball a₀ R :=
    (Metric.ball_subset_ball (by linarith : R / 2 ≤ R)) hycoord
  have hsub : Metric.ball (e y) (r / (C : ℝ)) ⊆ Metric.ball a₀ R := by
    intro a ha
    change dist a a₀ < R
    have hdist := dist_triangle a (e y) a₀
    have ha' : dist a (e y) < r / (C : ℝ) := ha
    have hy' : dist (e y) a₀ < R / 2 := hycoord
    linarith
  let s := e.symm '' Metric.ball (e y) (r / (C : ℝ))
  have hs : s ⊆ e.symm '' Metric.ball a₀ R := image_mono hsub
  have hmetric : s ⊆ Metric.eball y (ENNReal.ofReal r) := by
    rintro _ ⟨a, ha, rfl⟩
    have hd := hinv (hsub ha) hyouter
    rw [e.left_inv hy] at hd
    have hcoord : edist a (e y) < ENNReal.ofReal (r / (C : ℝ)) := edist_lt_ofReal.mpr ha
    apply hd.trans_lt
    have hmul := ENNReal.mul_lt_mul_right hCne ENNReal.coe_ne_top hcoord
    have hcancel : (C : ℝ≥0∞) * (ENNReal.ofReal r / (C : ℝ≥0∞)) =
        ENNReal.ofReal r := ENNReal.mul_div_cancel hCne ENNReal.coe_ne_top
    rw [ENNReal.ofReal_div_of_pos hC0, ENNReal.ofReal_coe_nnreal] at hmul
    rw [hcancel] at hmul
    exact hmul
  have himage : Metric.ball (e y) (r / (C : ℝ)) ⊆ e '' s := by
    intro a ha
    exact ⟨e.symm a, ⟨a, ha, rfl⟩, e.right_inv (htarget (hsub ha))⟩
  have hmeasure := m01_hausdorff_coordinateBall_le e C s (e y) (r / (C : ℝ))
    (hfwd.mono hs) himage
  exact hmeasure.trans (mul_le_mul_right (measure_mono hmetric) _)

theorem m01_calibrated_ball_lower_bound_of_chart (e : OpenPartialHomeomorph M F)
    (iso : F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (C : ℝ≥0) (hC : 1 < C) (hC6 : (C : ℝ≥0∞) ^ 6 ≤ 2) (a₀ : F) {R : ℝ}
    (htarget : Metric.ball a₀ R ⊆ e.target)
    (hinv : LipschitzOnWith C e.symm (Metric.ball a₀ R))
    (hfwd : LipschitzOnWith C e (e.symm '' Metric.ball a₀ R))
    (y : M) (hy : y ∈ e.source) (hycoord : e y ∈ Metric.ball a₀ (R / 2))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R / 2) :
    (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 ≤
      euclideanHausdorffCalibration * Measure.hausdorffMeasure (3 : ℝ)
        (Metric.eball y (ENNReal.ofReal r)) := by
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (zero_lt_one.trans hC)
  have hCne : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hC).ne'
  have hmeasure := m01_hausdorff_metricBall_le e C hC a₀ htarget hinv hfwd
    y hy hycoord hr hrR
  let μ := euclideanHausdorffCalibration * Measure.hausdorffMeasure (3 : ℝ)
    (Metric.eball y (ENNReal.ofReal r))
  have hcal : euclideanUnitBallLebesgueVolume * ENNReal.ofReal (r / (C : ℝ)) ^ 3 ≤
      (C : ℝ≥0∞) ^ 3 * μ := by
    rw [← m01_calibrated_hausdorff_ball iso (e y) (div_pos hr hC0)]
    calc
      _ ≤ euclideanHausdorffCalibration * ((C : ℝ≥0∞) ^ 3 *
          Measure.hausdorffMeasure (3 : ℝ) (Metric.eball y (ENNReal.ofReal r))) :=
        mul_le_mul_right hmeasure _
      _ = _ := by dsimp [μ]; ac_rfl
  rw [ENNReal.ofReal_div_of_pos hC0, ENNReal.ofReal_coe_nnreal,
    div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv, ← mul_div_assoc] at hcal
  have htwo : euclideanUnitBallLebesgueVolume * ENNReal.ofReal r ^ 3 ≤ 2 * μ := by
    calc
      _ ≤ ((C : ℝ≥0∞) ^ 3 * μ) * (C : ℝ≥0∞) ^ 3 :=
        (ENNReal.div_le_iff_le_mul (Or.inl (pow_ne_zero _ hCne))
          (Or.inl (ENNReal.pow_ne_top ENNReal.coe_ne_top))).mp hcal
      _ = (C : ℝ≥0∞) ^ 6 * μ := by
        rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add]
        ac_rfl
      _ ≤ 2 * μ := mul_le_mul_left hC6 μ
  have hquot : (euclideanUnitBallLebesgueVolume * ENNReal.ofReal r ^ 3) / 2 ≤ μ := by
    apply (ENNReal.div_le_iff_le_mul (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))).mpr
    simpa only [mul_comm] using htwo
  calc
    _ = (euclideanUnitBallLebesgueVolume * ENNReal.ofReal r ^ 3) / 2 := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ μ := hquot

end

universe u

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M]

theorem m01_normalizedMetricVolume_locally_lower_bound (g : RiemannianMetric 3 M) (x : M) :
    ∃ r₀ > 0, ∀ᶠ y in 𝓝 x, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 ≤
        normalizedMetricVolume g (g.ball y r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let F := TangentSpace (𝓡 3) x
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let C : ℝ≥0 := 11 / 10
  have hC : 1 < C := by norm_num [C]
  have hC6 : (C : ℝ≥0∞) ^ 6 ≤ 2 := by
    have h : C ^ 6 ≤ (2 : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]
      norm_num [C]
    exact_mod_cast h
  let b := (g.orthonormalBasis x).reindex (finCongr (m01_tangentSpace_finrank x))
  obtain ⟨e, R, hR, hxe, htarget, hinv, hfwd⟩ :=
    m01_exists_bilipschitz_chart (E := EuclideanSpace ℝ (Fin 3)) x C hC
  refine ⟨R / 2, half_pos hR, ?_⟩
  have hnear := (e.continuousAt hxe).preimage_mem_nhds (Metric.ball_mem_nhds (e x) (half_pos hR))
  filter_upwards [e.open_source.mem_nhds hxe, hnear] with y hy hycoord
  intro r hr hrR
  have h := m01_calibrated_ball_lower_bound_of_chart e b.repr C hC hC6 (e x)
    htarget hinv hfwd y hy hycoord hr hrR
  have hball_eq : g.ball y r = Metric.eball y (ENNReal.ofReal r) := by
    ext z
    change riemannianEDist (𝓡 3) y z < ENNReal.ofReal r ↔
      edist z y < ENNReal.ofReal r
    rw [← IsRiemannianManifold.out (I := 𝓡 3), edist_comm]
  change _ ≤ (euclideanHausdorffCalibration • g.hausdorffVolume) (g.ball y r)
  rw [Measure.smul_apply, smul_eq_mul, hball_eq]
  simpa only [RiemannianMetric.hausdorffVolume] using h

theorem m01_normalizedMetricVolume_uniform_lower_bound [CompactSpace M]
    (g : RiemannianMetric 3 M) :
    ∃ r₀ > 0, ∀ x : M, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 ≤
        normalizedMetricVolume g (g.ball x r) := by
  classical
  choose R hR hbound using m01_normalizedMetricVolume_locally_lower_bound g
  choose U hUsub hUopen hUmem using fun x => mem_nhds_iff.mp (hbound x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hUmem x⟩)
  refine ⟨s.fold min 1 R, (Finset.lt_fold_min (0 : ℝ)).mpr
    ⟨zero_lt_one, fun x _ => hR x⟩, ?_⟩
  intro x r hr hrR
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact hUsub y hxy r hr (hrR.trans
    ((Finset.fold_min_le (R y)).mpr (Or.inr ⟨y, hy, le_rfl⟩)))

end PoincareConjecture
