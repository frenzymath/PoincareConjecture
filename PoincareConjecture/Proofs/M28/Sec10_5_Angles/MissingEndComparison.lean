import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedSegmentRayLimits
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedSphereRadiusBarrier
import PoincareConjecture.Proofs.M28.Sec10_5_Angles.CrossSegmentComparison
import Mathlib.Analysis.SpecificLimits.Basic











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

private theorem continuousOn_Icc_of_unit_metric
    {Y : Type*} [MetricSpace Y] {eta : ℝ → Y} {L : ℝ}
    (hmetric : ∀ s ∈ Icc (0 : ℝ) L, ∀ t ∈ Icc (0 : ℝ) L,
      dist (eta s) (eta t) = |s - t|) :
    ContinuousOn eta (Icc (0 : ℝ) L) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h : Isometry (fun t : Icc (0 : ℝ) L => eta t.1) := by
    apply Isometry.of_dist_eq
    intro s t
    change dist (eta s.1) (eta t.1) = dist s.1 t.1
    simpa only [Real.dist_eq] using hmetric s.1 s.2 t.1 t.2
  exact h.continuous

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {X : Set M}





theorem corresponding_side_lower_at_selected_end
    (T : EpsilonTubeCertificate g X) (C : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) [PreconnectedSpace U]
    (hU : (U : Set M) = C.tail true (1 / 2)) (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
    (D : LeviCivitaData (intrinsicOpenMetric g U))
    (hsec : D.NonnegativeSectionalCurvature) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) (alpha : ℝ), 0 < alpha →
      (∀ eta : ℝ, 0 < eta → ∃ c : ℝ, 1 / 2 < c ∧ c < 1 ∧
        ∀ x : U, c < (C.inverse x).2 →
          dist (x : UniformSpace.Completion U) E < eta) →
      (∀ x : U, dist (x : UniformSpace.Completion U) E < alpha → 0 < f x) →
      (∀ p q : U, 0 < f p → 0 < f q →
        ∃ mu : ℝ → U, mu 0 = p ∧ mu 1 = q ∧ Continuous mu ∧
          (∀ t : ℝ, (3 / 4 : ℝ) ≤ (C.inverse (mu t)).2) ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            (intrinsicOpenMetric g U).edist (mu s) (mu t) =
              ENNReal.ofReal |s - t| * (intrinsicOpenMetric g U).edist p q) →
      ∀ {a b : ℝ} {gamma mu : ℝ → U},
        (∀ s ∈ Ico (0 : ℝ) a, ∀ t ∈ Ico (0 : ℝ) a,
          dist (gamma s) (gamma t) = |s - t|) →
        (∀ s ∈ Ico (0 : ℝ) b, ∀ t ∈ Ico (0 : ℝ) b,
          dist (mu s) (mu t) = |s - t|) →
        (∀ s ∈ Ico (0 : ℝ) a,
          dist (gamma s : UniformSpace.Completion U) E = a - s) →
        (∀ s ∈ Ico (0 : ℝ) b,
          dist (mu s : UniformSpace.Completion U) E = b - s) →
      ∀ {A B : ℝ}, 0 < A → A < a → A < alpha / 4 →
        0 < B → B < b → B < alpha / 4 →
      ∀ s ∈ Ioc (0 : ℝ) A, ∀ t ∈ Ioc (0 : ℝ) B,
        dist (gamma (a - s)) (mu (b - t)) ^ 2 ≥ s ^ 2 + t ^ 2 -
          2 * s * t * ((A ^ 2 + B ^ 2 -
            dist (gamma (a - A)) (mu (b - B)) ^ 2) / (2 * A * B)) := by
  classical
  let := intrinsicOpenMetricSpace g U hfinite
  let : RegularSpace U := @UniformSpace.to_regularSpace U
    (intrinsicOpenMetricSpace g U hfinite).toUniformSpace
  let : T0Space U := @MetricSpace.instT0Space U (intrinsicOpenMetricSpace g U hfinite)
  let : T3Space U := ⟨⟩
  intro E alpha halpha htail hbarrier hsegments
    a b gamma mu hgamma hmu hgammaRadius hmuRadius A B hA hAa hAalpha hB hBb hBalpha
  let gU := intrinsicOpenMetric g U
  let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
  have hedist (x y : U) : gU.edist x y = ENNReal.ofReal (dist x y) := by
    rw [intrinsicOpenMetric_edist, ← intrinsicOpenMetricSpace_edist g U hfinite,
      edist_dist]
  have hedistReal (x y : U) : (gU.edist x y).toReal = dist x y := by
    rw [hedist, ENNReal.toReal_ofReal dist_nonneg]
  have htriangle (x y : U) :
      |r x - r y| ≤ dist x y ∧ dist x y ≤ r x + r y := by
    constructor
    · simpa only [UniformSpace.Completion.dist_eq] using
        abs_dist_sub_le (x : UniformSpace.Completion U) (y : UniformSpace.Completion U) E
    · simpa only [UniformSpace.Completion.dist_eq] using
        dist_triangle_right (x : UniformSpace.Completion U) (y : UniformSpace.Completion U) E
  let h : ℕ → ℝ := fun n => min A B / ((n : ℝ) + 2)
  have hmin : 0 < min A B := lt_min hA hB
  have hhpos (n : ℕ) : 0 < h n := by
    dsimp [h]
    exact div_pos hmin (by positivity)
  have hhmin (n : ℕ) : h n < min A B := by
    dsimp [h]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
    have hden : (1 : ℝ) < (n : ℝ) + 2 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    simpa only [mul_one] using mul_lt_mul_of_pos_left hden hmin
  have hhA (n : ℕ) : h n < A := (hhmin n).trans_le (min_le_left _ _)
  have hhB (n : ℕ) : h n < B := (hhmin n).trans_le (min_le_right _ _)
  have hhzero : Tendsto h atTop (𝓝 (0 : ℝ)) := by
    simpa only [h, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_const_div_atTop_nhds_zero_nat (min A B)).comp (tendsto_add_atTop_nat 2)
  let q : ℕ → U := fun n => gamma (a - h n)
  let p : U := mu (b - B)
  have hqtime (n : ℕ) : a - h n ∈ Ico (0 : ℝ) a := by
    constructor <;> linarith [hhA n, hhpos n]
  have hqRadius (n : ℕ) : r (q n) = h n := by
    dsimp [q, r]
    rw [hgammaRadius _ (hqtime n)]
    ring
  have hpRadius : r p = B := by
    dsimp [p, r]
    rw [hmuRadius _ ⟨by linarith, by linarith⟩]
    ring
  have hpalpha : r p < alpha := by rw [hpRadius]; linarith
  have hqalpha (n : ℕ) : r (q n) < alpha := by
    rw [hqRadius]
    linarith [hhA n]
  let length : ℕ → ℝ := fun n => dist p (q n)
  have hlengthBounds (n : ℕ) : B - h n ≤ length n ∧ length n ≤ B + h n := by
    have hlo := (le_abs_self (r p - r (q n))).trans (htriangle p (q n)).1
    have hup := (htriangle p (q n)).2
    rw [hpRadius, hqRadius] at hlo hup
    exact ⟨hlo, hup⟩
  have hlengthPos (n : ℕ) : 0 < length n :=
    (sub_pos.mpr (hhB n)).trans_le (hlengthBounds n).1
  have hlength : Tendsto length atTop (𝓝 B) := by
    have hlo : Tendsto (fun n => B - h n) atTop (𝓝 B) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := B)).sub hhzero
    have hup : Tendsto (fun n => B + h n) atTop (𝓝 B) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := B)).add hhzero
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup
      (fun n => (hlengthBounds n).1) (fun n => (hlengthBounds n).2)
  choose segment hsegment0 hsegment1 _hsegmentContinuous hsegmentLower
    hsegmentMetric hsegmentRadius using fun n =>
      exists_intrinsic_segment_below_completion_radius_barrier T C U f hfinite
        E alpha hbarrier hsegments p (q n) hpalpha (hqalpha n)
  let arc : ℕ → ℝ → U := fun n t => segment n (t / length n)
  have harc0 (n : ℕ) : arc n 0 = p := by
    simpa only [arc, zero_div] using hsegment0 n
  have harc1 (n : ℕ) : arc n (length n) = q n := by
    simpa only [arc, div_self (hlengthPos n).ne'] using hsegment1 n
  have hparameter (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (length n)) :
      t / length n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 (hlengthPos n).le, (div_le_one (hlengthPos n)).mpr ht.2⟩
  have harcMetric (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (length n))
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (length n)) :
      dist (arc n s) (arc n t) = |s - t| := by
    change dist (segment n (s / length n)) (segment n (t / length n)) = _
    rw [hsegmentMetric n _ (hparameter n s hs) _ (hparameter n t ht)]
    change |s / length n - t / length n| * length n = |s - t|
    rw [← sub_div, abs_div, abs_of_pos (hlengthPos n),
      div_mul_cancel₀ _ (hlengthPos n).ne']
  have harcLower (n : ℕ) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) (length n)) :
      (3 / 4 : ℝ) ≤ (C.inverse (arc n t)).2 :=
    hsegmentLower n (t / length n)
  have harcRadius (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (length n)) :
      r (arc n t) ≤ B + h n := by
    have hh := hsegmentRadius n (t / length n) (hparameter n t ht)
    change r (arc n t) ≤ r p + r (q n) at hh
    simpa only [hpRadius, hqRadius] using hh
  have hdefect : Tendsto (fun n => dist (q n : UniformSpace.Completion U) E)
      atTop (𝓝 0) := by
    change Tendsto (fun n => r (q n)) atTop (𝓝 0)
    simpa only [hqRadius] using hhzero
  have harcLimit := selected_segment_tendsto_shortened_ray T C U hU hfinite
    E htail hB hBb hmu hmuRadius hlengthPos hlength hdefect harc0 harc1
    harcMetric harcLower
  have hfiniteComparison (n : ℕ) :
      ∀ u ∈ Icc (0 : ℝ) (A - h n), ∀ v ∈ Icc (0 : ℝ) (length n),
        dist (gamma (a - (h n + u))) (arc n (length n - v)) ^ 2 ≥
          u ^ 2 + v ^ 2 - 2 * u * v *
            (((A - h n) ^ 2 + length n ^ 2 - dist (gamma (a - A)) p ^ 2) /
              (2 * (A - h n) * length n)) := by
    let left : ℝ → U := fun u => gamma (a - (h n + u))
    let right : ℝ → U := fun v => arc n (length n - v)
    have hfirstPos : 0 < A - h n := sub_pos.mpr (hhA n)
    have hleftTime (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (A - h n)) :
        a - (h n + u) ∈ Ico (0 : ℝ) a := by
      constructor <;> linarith [hu.1, hu.2, hhpos n]
    have hrightTime (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (length n)) :
        length n - v ∈ Icc (0 : ℝ) (length n) := by
      constructor <;> linarith [hv.1, hv.2]
    have hleftMetric : ∀ u ∈ Icc (0 : ℝ) (A - h n),
        ∀ v ∈ Icc (0 : ℝ) (A - h n), dist (left u) (left v) = |u - v| := by
      intro u hu v hv
      change dist (gamma (a - (h n + u))) (gamma (a - (h n + v))) = _
      rw [hgamma _ (hleftTime u hu) _ (hleftTime v hv),
        show a - (h n + u) - (a - (h n + v)) = -(u - v) by ring, abs_neg]
    have hrightMetric : ∀ u ∈ Icc (0 : ℝ) (length n),
        ∀ v ∈ Icc (0 : ℝ) (length n), dist (right u) (right v) = |u - v| := by
      intro u hu v hv
      change dist (arc n (length n - u)) (arc n (length n - v)) = _
      rw [harcMetric n _ (hrightTime u hu) _ (hrightTime v hv),
        show length n - u - (length n - v) = -(u - v) by ring, abs_neg]
    have hleftRadius (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (A - h n)) :
        r (left u) < alpha := by
      dsimp [left, r]
      rw [hgammaRadius _ (hleftTime u hu)]
      linarith [hu.2]
    have hrightRadius (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (length n)) :
        r (right v) < alpha := by
      have hbnd := harcRadius n _ (hrightTime v hv)
      change r (right v) ≤ B + h n at hbnd
      linarith [hhB n]
    obtain ⟨zeta, hzeta, hzetaEq, _hzetaSmooth, hzetaSpeed⟩ :=
      exists_geodesic_eq_intrinsic_metric_segment_real g U hfinite hfirstPos
        (continuousOn_Icc_of_unit_metric hleftMetric) hleftMetric
    obtain ⟨eta, heta, hetaEq, _hetaSmooth, hetaSpeed⟩ :=
      exists_geodesic_eq_intrinsic_metric_segment_real g U hfinite (hlengthPos n)
        (continuousOn_Icc_of_unit_metric hrightMetric) hrightMetric
    have hzeroLeft : (0 : ℝ) ∈ Icc (0 : ℝ) (A - h n) := ⟨le_rfl, hfirstPos.le⟩
    have hzeroRight : (0 : ℝ) ∈ Icc (0 : ℝ) (length n) :=
      ⟨le_rfl, (hlengthPos n).le⟩
    have hendLeft : A - h n ∈ Icc (0 : ℝ) (A - h n) := ⟨hfirstPos.le, le_rfl⟩
    have hendRight : length n ∈ Icc (0 : ℝ) (length n) :=
      ⟨(hlengthPos n).le, le_rfl⟩
    have hleft0 : left 0 = q n := by simp only [left, q, add_zero]
    have hright0 : right 0 = q n := by
      simpa only [right, sub_zero] using harc1 n
    have hbase : zeta 0 = eta 0 :=
      (hzetaEq hzeroLeft).trans (hleft0.trans (hright0.symm.trans (hetaEq hzeroRight).symm))
    have hzetaDist : ∀ u ∈ Icc (0 : ℝ) (A - h n),
        gU.edist (zeta 0) (zeta u) = ENNReal.ofReal u := by
      intro u hu
      rw [hedist, hzetaEq hzeroLeft, hzetaEq hu, hleftMetric 0 hzeroLeft u hu,
        zero_sub, abs_neg, abs_of_nonneg hu.1]
    have hetaDist : ∀ v ∈ Icc (0 : ℝ) (length n),
        gU.edist (eta 0) (eta v) = ENNReal.ofReal v := by
      intro v hv
      rw [hedist, hetaEq hzeroRight, hetaEq hv, hrightMetric 0 hzeroRight v hv,
        zero_sub, abs_neg, abs_of_nonneg hv.1]
    have hjoin : ∀ u ∈ Icc (0 : ℝ) (A - h n),
        ∀ v ∈ Icc (0 : ℝ) (length n), ∃ nu : ℝ → U,
          gU.IsGeodesicOn nu (Icc 0 1) ∧ nu 0 = zeta u ∧ nu 1 = eta v ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            gU.edist (nu s) (nu t) =
              ENNReal.ofReal (|s - t| * (gU.edist (zeta u) (eta v)).toReal) := by
      intro u hu v hv
      have hzu : r (zeta u) < alpha := by rw [hzetaEq hu]; exact hleftRadius u hu
      have hev : r (eta v) < alpha := by rw [hetaEq hv]; exact hrightRadius v hv
      obtain ⟨nu, hnu0, hnu1, hnu, _hsmooth, _hlower, hmetric, _hradius⟩ :=
        exists_smooth_intrinsic_segment_below_completion_radius_barrier
          T C U f hfinite E alpha hbarrier hsegments (zeta u) (eta v) hzu hev
      exact ⟨nu, hnu, hnu0, hnu1, hmetric⟩
    intro u hu v hv
    have hc := Comparison.corresponding_side_lower_of_cross_segments gU D hsec
      hfirstPos (hlengthPos n) hzeta heta hzetaSpeed hetaSpeed hbase
      hzetaDist hetaDist hjoin u hu v hv
    rw [hedistReal, hedistReal, hzetaEq hu, hetaEq hv,
      hzetaEq hendLeft, hetaEq hendRight] at hc
    simpa only [left, right, show h n + (A - h n) = A by ring,
      sub_self, harc0 n] using hc
  intro s hs t ht
  have hpointLimit : Tendsto (fun n => arc n (B - t))
      (hyperfilter ℕ : Filter ℕ) (𝓝 (mu (b - t))) := by
    have hh := harcLimit (B - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [show b - B + (B - t) = b - t by ring] using hh
  have hleftLimit : Tendsto (fun n => dist (gamma (a - s)) (arc n (B - t)) ^ 2)
      (hyperfilter ℕ : Filter ℕ) (𝓝 (dist (gamma (a - s)) (mu (b - t)) ^ 2)) :=
    ((tendsto_const_nhds (x := gamma (a - s))).dist hpointLimit).pow 2
  have hAlimit : Tendsto (fun n => A - h n) atTop (𝓝 A) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := A)).sub hhzero
  have hslimit : Tendsto (fun n => s - h n) atTop (𝓝 s) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := s)).sub hhzero
  have htlimit : Tendsto (fun n => length n - (B - t)) atTop (𝓝 t) := by
    have hh := hlength.sub (tendsto_const_nhds (x := B - t))
    simpa only [show B - (B - t) = t by ring] using hh
  have hcoefficient :
      Tendsto (fun n => ((A - h n) ^ 2 + length n ^ 2 -
        dist (gamma (a - A)) p ^ 2) / (2 * (A - h n) * length n))
        atTop (𝓝 ((A ^ 2 + B ^ 2 - dist (gamma (a - A)) p ^ 2) / (2 * A * B))) := by
    exact (((hAlimit.pow 2).add (hlength.pow 2)).sub tendsto_const_nhds).div
      ((tendsto_const_nhds.mul hAlimit).mul hlength) (by positivity)
  have hrightLimit :
      Tendsto (fun n => (s - h n) ^ 2 + (length n - (B - t)) ^ 2 -
        2 * (s - h n) * (length n - (B - t)) *
          (((A - h n) ^ 2 + length n ^ 2 - dist (gamma (a - A)) p ^ 2) /
            (2 * (A - h n) * length n)))
        (hyperfilter ℕ : Filter ℕ)
        (𝓝 (s ^ 2 + t ^ 2 - 2 * s * t *
          ((A ^ 2 + B ^ 2 - dist (gamma (a - A)) p ^ 2) / (2 * A * B)))) :=
    (((hslimit.pow 2).add (htlimit.pow 2)).sub
      (((tendsto_const_nhds.mul hslimit).mul htlimit).mul hcoefficient)).mono_left
        Nat.hyperfilter_le_atTop
  have htimes : ∀ᶠ n in atTop,
      s - h n ∈ Icc (0 : ℝ) (A - h n) ∧
        length n - (B - t) ∈ Icc (0 : ℝ) (length n) := by
    filter_upwards [hhzero.eventually (gt_mem_nhds hs.1),
      hlength.eventually (lt_mem_nhds (by linarith [ht.1] : B - t < B))] with n hn hnL
    constructor <;> constructor <;> linarith [hs.2, ht.2]
  have heventual : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
      (s - h n) ^ 2 + (length n - (B - t)) ^ 2 -
        2 * (s - h n) * (length n - (B - t)) *
          (((A - h n) ^ 2 + length n ^ 2 - dist (gamma (a - A)) p ^ 2) /
            (2 * (A - h n) * length n)) ≤
        dist (gamma (a - s)) (arc n (B - t)) ^ 2 := by
    apply (htimes.mono ?_).filter_mono Nat.hyperfilter_le_atTop
    intro n hn
    have hc := hfiniteComparison n (s - h n) hn.1 (length n - (B - t)) hn.2
    simpa only [show h n + (s - h n) = s by ring,
      show length n - (length n - (B - t)) = B - t by ring] using hc
  exact le_of_tendsto_of_tendsto hrightLimit hleftLimit heventual

end PoincareConjecture.M28
