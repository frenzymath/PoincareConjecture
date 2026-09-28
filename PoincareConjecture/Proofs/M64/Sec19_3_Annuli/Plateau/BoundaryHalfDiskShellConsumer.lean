import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfDiskAngularTransport
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RawAnnulusChartTraceBridge
import PoincareConjecture.Proofs.M64.Mathlib.RadialTestVanishing
import PoincareConjecture.Proofs.M58.Cor18_28_PolarIntegration














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff intervalIntegral

namespace PoincareConjecture

open Proofs.M58

local notation "S" => interior m64AnnulusDomain
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

private def halfDisk (x R : ℝ) : Set LoopPlane :=
  Metric.ball (annulusPoint x 0) R ∩ {p | 0 < p 1}

private theorem halfDisk_measurable (x R : ℝ) : MeasurableSet (halfDisk x R) := by
  exact measurableSet_ball.inter (measurableSet_lt measurable_const (by fun_prop))

private theorem halfDisk_subset {x R : ℝ}
    (hx : R < x) (hP : x + R < curvePeriod) (hR : R < 1) : halfDisk x R ⊆ S := by
  intro p hp
  have hd := Metric.mem_ball.mp hp.1
  rw [dist_eq_norm] at hd
  have h0 := (PiLp.norm_apply_le (p - annulusPoint x 0) 0).trans_lt hd
  have h1 := (PiLp.norm_apply_le (p - annulusPoint x 0) 1).trans_lt hd
  change ‖p 0 - x‖ < R at h0
  change ‖p 1 - 0‖ < R at h1
  rw [Real.norm_eq_abs] at h0 h1
  obtain ⟨h0l, h0r⟩ := abs_lt.mp h0
  obtain ⟨_, h1r⟩ := abs_lt.mp h1
  exact (m64AnnulusInterior_coordinates p).mpr
    ⟨by linarith, by linarith, hp.2, by linarith⟩

private theorem halfDisk_polar_mem (x R : ℝ) {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    annulusPoint x 0 + p.1 • angularPoint p.2 ∈ halfDisk x R ↔
      p ∈ Ioo (0 : ℝ) R ×ˢ Ioo (0 : ℝ) Real.pi := by
  have hdist : dist (annulusPoint x 0 + p.1 • angularPoint p.2)
      (annulusPoint x 0) = p.1 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hp.1.le, norm_angularPoint, mul_one]
  have hs : 0 < Real.sin p.2 ↔ 0 < p.2 := by
    constructor
    · intro hsin
      by_contra ht
      exact (not_lt_of_ge (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (le_of_not_gt ht) hp.2.1.le)) hsin
    · intro ht
      exact Real.sin_pos_of_pos_of_lt_pi ht hp.2.2
  change (dist (annulusPoint x 0 + p.1 • angularPoint p.2)
      (annulusPoint x 0) < R ∧
      0 < (annulusPoint x 0 + p.1 • angularPoint p.2) 1) ↔ _
  rw [hdist]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, annulusPoint,
    angularPoint, Matrix.cons_val_one, Matrix.cons_val_zero, zero_add,
    mem_prod, mem_Ioo]
  rw [mul_pos_iff_of_pos_left hp.1, hs]
  constructor
  · rintro ⟨hR, htheta⟩
    exact ⟨⟨hp.1, hR⟩, htheta, hp.2.2⟩
  · rintro ⟨⟨_, hR⟩, htheta, _⟩
    exact ⟨hR, htheta⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem translated_polar_integral (f : LoopPlane → E) (x : ℝ) :
    (∫ p in polarCoord.target,
      p.1 • f (annulusPoint x 0 + p.1 • angularPoint p.2)) = ∫ z, f z := by
  calc
    _ = ∫ p : ℝ × ℝ, f (annulusPoint x 0 + loopPlaneEquivProd.symm p) := by
      simpa only [loopPlaneEquivProd_symm_polar] using
        integral_comp_polarCoord_symm
          (fun p => f (annulusPoint x 0 + loopPlaneEquivProd.symm p))
    _ = ∫ p : LoopPlane, f (annulusPoint x 0 + p) :=
      measurePreserving_loopPlaneEquivProd.symm.integral_comp'
        (fun p => f (annulusPoint x 0 + p))
    _ = ∫ z, f z :=
      integral_add_left_eq_self f (annulusPoint x 0)

omit [CompleteSpace E] in
private theorem translated_polar_integrable {f : LoopPlane → E} (hf : Integrable f)
    (x : ℝ) : IntegrableOn
      (fun p : ℝ × ℝ => p.1 • f (annulusPoint x 0 + p.1 • angularPoint p.2))
      polarCoord.target := by
  have htrans : Integrable (fun p : LoopPlane =>
      f (annulusPoint x 0 + p)) :=
    (measurePreserving_add_left (volume : Measure LoopPlane)
      (annulusPoint x 0)).integrable_comp_of_integrable hf
  have hprod : Integrable (fun p : ℝ × ℝ =>
      f (annulusPoint x 0 + loopPlaneEquivProd.symm p)) :=
    measurePreserving_loopPlaneEquivProd.symm.integrable_comp_of_integrable htrans
  have hchange := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn
    (fun p : ℝ × ℝ => f (annulusPoint x 0 + loopPlaneEquivProd.symm p))).mp
      (by rw [polarCoord.symm_image_target_eq_source]; exact hprod.integrableOn)
  apply hchange.congr
  filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
  have hp0 : 0 < p.1 := hp.1
  simp only [det_fderivPolarCoordSymm, abs_of_pos hp0,
    loopPlaneEquivProd_symm_polar]

omit [CompleteSpace E] in
private theorem halfDisk_polar_integral (x R : ℝ) (f : LoopPlane → E) :
    (∫ z in halfDisk x R, f z) =
      ∫ p in Ioo (0 : ℝ) R ×ˢ Ioo (0 : ℝ) Real.pi,
        p.1 • f (annulusPoint x 0 + p.1 • angularPoint p.2) := by
  classical
  let K := Ioo (0 : ℝ) R ×ˢ Ioo (0 : ℝ) Real.pi
  have hK : MeasurableSet K := measurableSet_Ioo.prod measurableSet_Ioo
  have hKsub : K ⊆ polarCoord.target := by
    intro p hp
    exact ⟨hp.1.1, by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
  rw [← integral_indicator (halfDisk_measurable x R), ← translated_polar_integral _ x]
  calc
    _ = ∫ p in polarCoord.target,
        K.indicator (fun p : ℝ × ℝ =>
          p.1 • f (annulusPoint x 0 + p.1 • angularPoint p.2)) p := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      have hm := halfDisk_polar_mem x R hp
      by_cases h : p ∈ K
      · dsimp
        rw [indicator_of_mem (hm.mpr h), indicator_of_mem h]
      · dsimp
        rw [indicator_of_notMem (mt hm.mp h), indicator_of_notMem h, smul_zero]
    _ = _ := by rw [integral_indicator hK, Measure.restrict_restrict hK,
      inter_eq_left.mpr hKsub]

omit [CompleteSpace E] in
private theorem halfDisk_polar_integrable {x R : ℝ} {f : LoopPlane → E}
    (hf : IntegrableOn f (halfDisk x R)) :
    IntegrableOn (fun p : ℝ × ℝ =>
      p.1 • f (annulusPoint x 0 + p.1 • angularPoint p.2))
      (Ioo (0 : ℝ) R ×ˢ Ioo (0 : ℝ) Real.pi) := by
  have hi := translated_polar_integrable
    ((integrable_indicator_iff (halfDisk_measurable x R)).mpr hf) x
  have hsub : Ioo (0 : ℝ) R ×ˢ Ioo (0 : ℝ) Real.pi ⊆ polarCoord.target := by
    intro p hp
    exact ⟨hp.1.1, by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
  apply (hi.mono_set hsub).congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  rw [indicator_of_mem ((halfDisk_polar_mem x R (hsub hp)).mpr hp)]

private def m64PolynomialZeroGreenStatement
    {n m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (x : ℝ) (psi : ℝ → ℝ) : Prop :=
    (∫ p in S, m64HalfDiskPolynomialTestZeroAt x psi p 0 • A.column 0 p) +
        (∫ p in S, m64HalfDiskPolynomialTestZeroAt x psi p 1 • A.column 1 p) +
        (∫ p in S, fderiv ℝ (fun q =>
          m64HalfDiskPolynomialTestZeroAt x psi q 0) p e0 • e (A.map p)) +
        (∫ p in S, fderiv ℝ (fun q =>
          m64HalfDiskPolynomialTestZeroAt x psi q 1) p e1 • e (A.map p)) =
      -(∫ y in Icc (0 : ℝ) curvePeriod,
        (psi ((y - x) ^ 2) * (y - x)) • e (c0 y))

private def m64PolynomialOneGreenStatement
    {n m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (x : ℝ) (psi : ℝ → ℝ) : Prop :=
    (∫ p in S, m64HalfDiskPolynomialTestOneAt x psi p 0 • A.column 0 p) +
        (∫ p in S, m64HalfDiskPolynomialTestOneAt x psi p 1 • A.column 1 p) +
        (∫ p in S, fderiv ℝ (fun q =>
          m64HalfDiskPolynomialTestOneAt x psi q 0) p e0 • e (A.map p)) +
        (∫ p in S, fderiv ℝ (fun q =>
          m64HalfDiskPolynomialTestOneAt x psi q 1) p e1 • e (A.map p)) =
      -(∫ y in Icc (0 : ℝ) curvePeriod,
        (psi ((y - x) ^ 2) * (y - x) ^ 2) • e (c0 y))

private theorem m64Polynomial_support_subset
    {a b : ℝ} {psi : ℝ → ℝ}
    (hzero : ∀ t, t ∉ Ioo (a ^ 2) (b ^ 2) → psi t = 0) :
    Function.support psi ⊆ Ioo (a ^ 2) (b ^ 2) := by
  intro t ht
  by_contra hnot
  exact ht (by simpa [Function.mem_support] using hzero t hnot)

private theorem m64Polynomial_at_zero_of_not_interval
    {a b x : ℝ} {psi : ℝ → ℝ}
    (hzero : ∀ t, t ∉ Ioo (a ^ 2) (b ^ 2) → psi t = 0)
    {p : LoopPlane} (hp : m64HalfDiskQuadratic (p - !₂[x, 0]) ∉
      Ioo (a ^ 2) (b ^ 2)) :
    m64HalfDiskPolynomialTestZeroAt x psi p = 0 ∧
      m64HalfDiskPolynomialTestOneAt x psi p = 0 := by
  exact m64HalfDisk_polynomialTest_eq_zero
    (m64Polynomial_support_subset hzero) hp

private theorem m64Polynomial_period_zero
    (x a b R : ℝ) (hb : 0 ≤ b) (hbR : b < R)
    (hx : R < x) (hP : R < curvePeriod - x)
    {psi : ℝ → ℝ}
    (hzero : ∀ t, t ∉ Ioo (a ^ 2) (b ^ 2) → psi t = 0) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      m64HalfDiskPolynomialTestZeroAt x psi (annulusPoint curvePeriod s) 0 =
        m64HalfDiskPolynomialTestZeroAt x psi (annulusPoint 0 s) 0 := by
  intro s hs
  have hleft : m64HalfDiskQuadratic
      (annulusPoint 0 s - !₂[x, 0]) ∉ Ioo (a ^ 2) (b ^ 2) := by
    have hxb : b < x := lt_trans hbR hx
    have hsq : b ^ 2 < x ^ 2 := by nlinarith
    have hquad : m64HalfDiskQuadratic
        (annulusPoint 0 s - !₂[x, 0]) = x ^ 2 + s ^ 2 := by
      simp [m64HalfDiskQuadratic, annulusPoint, PiLp.sub_apply]
    intro hq
    rw [hquad] at hq
    linarith only [hsq, hq.2, sq_nonneg s]
  have hright : m64HalfDiskQuadratic
      (annulusPoint curvePeriod s - !₂[x, 0]) ∉ Ioo (a ^ 2) (b ^ 2) := by
    have hxb : b < curvePeriod - x := lt_trans hbR hP
    have hsq : b ^ 2 < (curvePeriod - x) ^ 2 := by nlinarith
    have hquad : m64HalfDiskQuadratic
        (annulusPoint curvePeriod s - !₂[x, 0]) =
          (curvePeriod - x) ^ 2 + s ^ 2 := by
      simp [m64HalfDiskQuadratic, annulusPoint, PiLp.sub_apply]
    intro hq
    rw [hquad] at hq
    linarith only [hsq, hq.2, sq_nonneg s]
  have hz0 := m64Polynomial_at_zero_of_not_interval
    (p := annulusPoint 0 s) hzero hleft
  have hz1 := m64Polynomial_at_zero_of_not_interval
    (p := annulusPoint curvePeriod s) hzero hright
  rw [hz1.1, hz0.1]

private theorem m64Polynomial_period_one
    (x a b R : ℝ) (hb : 0 ≤ b) (hbR : b < R)
    (hx : R < x) (hP : R < curvePeriod - x)
    {psi : ℝ → ℝ}
    (hzero : ∀ t, t ∉ Ioo (a ^ 2) (b ^ 2) → psi t = 0) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      m64HalfDiskPolynomialTestOneAt x psi (annulusPoint curvePeriod s) 0 =
        m64HalfDiskPolynomialTestOneAt x psi (annulusPoint 0 s) 0 := by
  intro s hs
  have hleft : m64HalfDiskQuadratic
      (annulusPoint 0 s - !₂[x, 0]) ∉ Ioo (a ^ 2) (b ^ 2) := by
    have hxb : b < x := lt_trans hbR hx
    have hsq : b ^ 2 < x ^ 2 := by nlinarith
    have hquad : m64HalfDiskQuadratic
        (annulusPoint 0 s - !₂[x, 0]) = x ^ 2 + s ^ 2 := by
      simp [m64HalfDiskQuadratic, annulusPoint, PiLp.sub_apply]
    intro hq
    rw [hquad] at hq
    linarith only [hsq, hq.2, sq_nonneg s]
  have hright : m64HalfDiskQuadratic
      (annulusPoint curvePeriod s - !₂[x, 0]) ∉ Ioo (a ^ 2) (b ^ 2) := by
    have hxb : b < curvePeriod - x := lt_trans hbR hP
    have hsq : b ^ 2 < (curvePeriod - x) ^ 2 := by nlinarith
    have hquad : m64HalfDiskQuadratic
        (annulusPoint curvePeriod s - !₂[x, 0]) =
          (curvePeriod - x) ^ 2 + s ^ 2 := by
      simp [m64HalfDiskQuadratic, annulusPoint, PiLp.sub_apply]
    intro hq
    rw [hquad] at hq
    linarith only [hsq, hq.2, sq_nonneg s]
  have hz0 := m64Polynomial_at_zero_of_not_interval
    (p := annulusPoint 0 s) hzero hleft
  have hz1 := m64Polynomial_at_zero_of_not_interval
    (p := annulusPoint curvePeriod s) hzero hright
  rw [hz1.2, hz0.2]

private theorem m64Polynomial_top_zero
    {x a b R : ℝ} (hb : 0 ≤ b) (hbR : b < R) (hR : R < 1)
    {psi : ℝ → ℝ}
    (hzero : ∀ t, t ∉ Ioo (a ^ 2) (b ^ 2) → psi t = 0) (y : ℝ) :
    m64HalfDiskPolynomialTestZeroAt x psi (annulusPoint y 1) = 0 ∧
      m64HalfDiskPolynomialTestOneAt x psi (annulusPoint y 1) = 0 := by
  apply m64Polynomial_at_zero_of_not_interval hzero
  intro hq
  have hquad : m64HalfDiskQuadratic (annulusPoint y 1 - !₂[x, 0]) =
      (y - x) ^ 2 + 1 := by
    simp [m64HalfDiskQuadratic, annulusPoint, PiLp.sub_apply]
  rw [hquad] at hq
  have hb1 : b < 1 := hbR.trans hR
  nlinarith [hq.2, sq_nonneg (y - x)]

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local instance : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr
  ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne

private theorem polynomial_supported_green
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {x a b R : ℝ} (hb : 0 ≤ b) (hbR : b < R)
    (hx : R < x) (hP : x + R < curvePeriod) (hR : R < 1)
    {psi : ℝ → ℝ} (hpsi : ContDiff ℝ 1 psi)
    (hsupport : tsupport psi ⊆ Ioo (a ^ 2) (b ^ 2)) :
    m64PolynomialZeroGreenStatement A x psi ∧
      m64PolynomialOneGreenStatement A x psi := by
  have hzero (t : ℝ) (ht : t ∉ Ioo (a ^ 2) (b ^ 2)) : psi t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => ht (hsupport h))
  have hp0 := m64Polynomial_period_zero x a b R hb hbR hx (by linarith) hzero
  have hp1 := m64Polynomial_period_one x a b R hb hbR hx (by linarith) hzero
  have ht (y : ℝ) := m64Polynomial_top_zero (x := x) hb hbR hR hzero y
  have hl (y : ℝ) := m64HalfDisk_polynomialTestAt_axis (psi := psi) x (y - x)
  simp only [add_sub_cancel] at hl
  constructor
  · unfold m64PolynomialZeroGreenStatement
    rw [A.polynomial_test_zero_green hpsi x hp0, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun y => by
      dsimp only
      rw [(ht y).1, (hl y).1]
      simp only [PiLp.zero_apply, zero_smul, zero_sub])
  · unfold m64PolynomialOneGreenStatement
    rw [A.polynomial_test_one_green hpsi x hp1, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun y => by
      dsimp only
      rw [(ht y).2, (hl y).2]
      simp only [PiLp.zero_apply, zero_smul, zero_sub])

private theorem vector_flux_integral
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {Z : LoopPlane → LoopPlane} (hZ : ContDiff ℝ 1 Z) :
    (∫ p in S, Z p 0 • A.column 0 p + Z p 1 • A.column 1 p +
      (fderiv ℝ (fun q => Z q 0) p e0 +
        fderiv ℝ (fun q => Z q 1) p e1) • e (A.map p)) =
      (∫ p in S, Z p 0 • A.column 0 p) +
      (∫ p in S, Z p 1 • A.column 1 p) +
      (∫ p in S, fderiv ℝ (fun q => Z q 0) p e0 • e (A.map p)) +
      (∫ p in S, fderiv ℝ (fun q => Z q 1) p e1 • e (A.map p)) := by
  have hz (i : Fin 2) : ContDiff ℝ 1 (fun p => Z p i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hZ
  have hu : Integrable (fun p => e (A.map p)) (volume.restrict S) :=
    A.observed_memLp.integrable (by norm_num)
  have hc (i : Fin 2) := m64Annulus_continuous_smul_integrable
    ((Lp.memLp (A.column i)).integrable (by norm_num)) (hz i).continuous
  have hd (i : Fin 2) := m64Annulus_continuous_smul_integrable hu
    (((hz i).continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i 1)))
  simp_rw [add_smul]
  have hcadd := integral_add (hc 0) (hc 1)
  have hdadd := integral_add (hd 0) (hd 1)
  have hall := integral_add ((hc 0).add (hc 1)) ((hd 0).add (hd 1))
  simp only [Pi.add_apply] at hcadd hdadd hall
  rw [hall, hcadd, hdadd]
  abel

private theorem polynomial_outside_halfDisk
    {x a b R : ℝ} (hb : 0 ≤ b) (hbR : b < R)
    {psi : ℝ → ℝ} (hsupport : tsupport psi ⊆ Ioo (a ^ 2) (b ^ 2))
    {p : LoopPlane} (hp : p ∈ S \ halfDisk x R) :
    psi (m64HalfDiskQuadratic (p - !₂[x, 0])) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  have hq := (hsupport ht).2
  have hnorm : m64HalfDiskQuadratic (p - !₂[x, 0]) = ‖p - annulusPoint x 0‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
      m64HalfDiskQuadratic, annulusPoint]
  have hR0 : 0 < R := hb.trans_lt hbR
  have hdist : R ≤ ‖p - annulusPoint x 0‖ := by
    by_contra hn
    apply hp.2
    exact ⟨by simpa only [Metric.mem_ball, dist_eq_norm, not_le] using hn,
      ((m64AnnulusInterior_coordinates p).mp hp.1).2.2.1⟩
  rw [hnorm] at hq
  nlinarith

omit [CompleteSpace E] in
private theorem halfDisk_supported_polar
    {x R : ℝ} (hx : R < x) (hP : x + R < curvePeriod) (hR : R < 1)
    {f : LoopPlane → E} (hf : IntegrableOn f S)
    (hzero : ∀ p ∈ S \ halfDisk x R, f p = 0) :
    (∫ p in S, f p) = ∫ r in Ioo (0 : ℝ) R,
      ∫ theta in Ioo (0 : ℝ) Real.pi,
        r • f (annulusPoint x 0 + r • angularPoint theta) := by
  have hsub := halfDisk_subset hx hP hR
  have hpol := halfDisk_polar_integrable (hf.mono_set hsub)
  calc
    _ = ∫ p in halfDisk x R, f p :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        isOpen_interior.measurableSet hsub hzero
    _ = _ := by
      rw [halfDisk_polar_integral]
      exact setIntegral_prod _ hpol







theorem M64ObservedWeakAnnulus.polynomial_shell_pairings
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {x a b R : ℝ} (hb : 0 ≤ b) (hbR : b < R)
    (hx : R < x) (hP : x + R < curvePeriod) (hR : R < 1) :
    let P := fun r theta => annulusPoint x 0 + r • angularPoint theta
    let U := fun r theta => e (A.map (P r theta))
    let W := fun r theta => r • ((-Real.sin theta) • A.column 0 (P r theta) +
      Real.cos theta • A.column 1 (P r theta))
    ∀ psi : ℝ → ℝ, ContDiff ℝ 1 psi → tsupport psi ⊆ Ioo (a ^ 2) (b ^ 2) →
      ((∫ r in Ioo (0 : ℝ) R, ∫ theta in Ioo (0 : ℝ) Real.pi,
        (r * psi (r ^ 2)) • W r theta) =
          -(∫ y in Icc (0 : ℝ) curvePeriod,
            (psi ((y - x) ^ 2) * (y - x)) • e (c0 y))) ∧
      ((∫ r in Ioo (0 : ℝ) R, ∫ theta in Ioo (0 : ℝ) Real.pi,
        (r ^ 2 * psi (r ^ 2)) •
          (Real.cos theta • W r theta - Real.sin theta • U r theta)) =
          -(∫ y in Icc (0 : ℝ) curvePeriod,
            (psi ((y - x) ^ 2) * (y - x) ^ 2) • e (c0 y))) := by
  dsimp only
  intro psi hpsi hsupp
  classical
  let P : ℝ → ℝ → LoopPlane := fun r theta =>
    annulusPoint x 0 + r • angularPoint theta
  let Z0 := m64HalfDiskPolynomialTestZeroAt x psi
  let Z1 := m64HalfDiskPolynomialTestOneAt x psi
  let F0 := fun p => Z0 p 0 • A.column 0 p + Z0 p 1 • A.column 1 p
  let F1 := fun p => Z1 p 0 • A.column 0 p + Z1 p 1 • A.column 1 p +
    (-(psi (m64HalfDiskQuadratic (p - !₂[x, 0])) * (p - !₂[x, 0]) 1)) • e (A.map p)
  have hZ0 : ContDiff ℝ 1 Z0 := (m64HalfDisk_polynomialTestAt_contDiff hpsi x).1
  have hZ1 : ContDiff ℝ 1 Z1 := (m64HalfDisk_polynomialTestAt_contDiff hpsi x).2
  have hcolumn (Z : LoopPlane → LoopPlane) (hZ : ContDiff ℝ 1 Z) (i : Fin 2) :=
    m64Annulus_continuous_smul_integrable
      ((Lp.memLp (A.column i)).integrable (by norm_num))
      ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hZ.continuous)
  have hF0 : IntegrableOn F0 S := (hcolumn Z0 hZ0 0).add (hcolumn Z0 hZ0 1)
  have hcoef : Continuous (fun p : LoopPlane =>
      -(psi (m64HalfDiskQuadratic (p - !₂[x, 0])) * (p - !₂[x, 0]) 1)) := by
    unfold m64HalfDiskQuadratic
    fun_prop
  have hF1 : IntegrableOn F1 S := ((hcolumn Z1 hZ1 0).add (hcolumn Z1 hZ1 1)).add
    (m64Annulus_continuous_smul_integrable
      (A.observed_memLp.integrable (by norm_num)) hcoef)
  obtain ⟨hg0, hg1⟩ := polynomial_supported_green A hb hbR hx hP hR hpsi hsupp
  have hi0 := vector_flux_integral A hZ0
  have hi1 := vector_flux_integral A hZ1
  have hi0' : (∫ p in S, F0 p) =
      (∫ p in S, Z0 p 0 • A.column 0 p) +
        (∫ p in S, Z0 p 1 • A.column 1 p) +
        (∫ p in S, fderiv ℝ (fun q => Z0 q 0) p e0 • e (A.map p)) +
        (∫ p in S, fderiv ℝ (fun q => Z0 q 1) p e1 • e (A.map p)) := by
    simpa only [F0, Z0, m64HalfDisk_polynomialTestAt_divergence_zero hpsi x,
      zero_smul, add_zero] using hi0
  have hzero0 : ∀ p ∈ S \ halfDisk x R, F0 p = 0 := by
    intro p hp
    have hpsi0 := polynomial_outside_halfDisk hb hbR hsupp hp
    simp [F0, Z0, m64HalfDiskPolynomialTestZeroAt,
      m64HalfDiskPolynomialTestZero, hpsi0]
  have hzero1 : ∀ p ∈ S \ halfDisk x R, F1 p = 0 := by
    intro p hp
    have hpsi0 := polynomial_outside_halfDisk hb hbR hsupp hp
    simp [F1, Z1, m64HalfDiskPolynomialTestOneAt,
      m64HalfDiskPolynomialTestOne, hpsi0]
  have hp0 := halfDisk_supported_polar hx hP hR hF0 hzero0
  have hp1 := halfDisk_supported_polar hx hP hR hF1 hzero1
  have hz0 (r theta : ℝ) : Z0 (P r theta) =
    (psi (r ^ 2) * r) • angularVector theta := by
    change m64HalfDiskPolynomialTestZero psi
      (annulusPoint x 0 + r • angularPoint theta - annulusPoint x 0) = _
    rw [add_sub_cancel_left]
    exact (m64HalfDisk_polynomialTest_polar r theta).1
  have hz1 (r theta : ℝ) : Z1 (P r theta) =
      (psi (r ^ 2) * r ^ 2 * Real.cos theta) • angularVector theta := by
    change m64HalfDiskPolynomialTestOne psi
      (annulusPoint x 0 + r • angularPoint theta - annulusPoint x 0) = _
    rw [add_sub_cancel_left]
    exact (m64HalfDisk_polynomialTest_polar r theta).2
  have hq (r theta : ℝ) : m64HalfDiskQuadratic (P r theta - !₂[x, 0]) = r ^ 2 := by
    change m64HalfDiskQuadratic
      (annulusPoint x 0 + r • angularPoint theta - annulusPoint x 0) = _
    rw [add_sub_cancel_left]
    change (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 = r ^ 2
    nlinarith [Real.sin_sq_add_cos_sq theta]
  constructor
  · calc
        _ = ∫ r in Ioo (0 : ℝ) R, ∫ theta in Ioo (0 : ℝ) Real.pi,
            r • F0 (P r theta) := by
          apply integral_congr_ae
          filter_upwards [] with r
          apply integral_congr_ae
          filter_upwards [] with theta
          change (r * psi (r ^ 2)) • (r • ((-Real.sin theta) •
            A.column 0 (P r theta) + Real.cos theta • A.column 1 (P r theta))) = _
          dsimp only [F0]
          rw [hz0]
          simp only [PiLp.smul_apply, smul_eq_mul, angularVector,
            Matrix.cons_val_zero, Matrix.cons_val_one]
          module
        _ = ∫ p in S, F0 p := hp0.symm
        _ = _ := hi0'.trans hg0
  · have hi1' : (∫ p in S, F1 p) =
        (∫ p in S, Z1 p 0 • A.column 0 p) +
          (∫ p in S, Z1 p 1 • A.column 1 p) +
          (∫ p in S, fderiv ℝ (fun q => Z1 q 0) p e0 • e (A.map p)) +
          (∫ p in S, fderiv ℝ (fun q => Z1 q 1) p e1 • e (A.map p)) := by
      simpa only [Z1, m64HalfDisk_polynomialTestAt_divergence_one hpsi x] using hi1
    calc
        _ = ∫ r in Ioo (0 : ℝ) R, ∫ theta in Ioo (0 : ℝ) Real.pi,
            r • F1 (P r theta) := by
          apply integral_congr_ae
          filter_upwards [] with r
          apply integral_congr_ae
          filter_upwards [] with theta
          change (r ^ 2 * psi (r ^ 2)) • (Real.cos theta • (r •
            ((-Real.sin theta) • A.column 0 (P r theta) +
              Real.cos theta • A.column 1 (P r theta))) -
            Real.sin theta • e (A.map (P r theta))) = _
          dsimp only [F1]
          rw [hz1, hq]
          have hcoord : (P r theta - !₂[x, 0]) 1 = r * Real.sin theta := by
            simp [P, annulusPoint, angularPoint]
          rw [hcoord]
          simp only [PiLp.smul_apply, smul_eq_mul, angularVector,
            Matrix.cons_val_zero, Matrix.cons_val_one]
          module
        _ = ∫ p in S, F1 p := hp1.symm
        _ = _ := hi1'.trans hg1





private theorem squared_radius_coefficient_ae_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {a b R : ℝ} {C : ℝ → F}
    (hC : IntegrableOn C (Ioo (0 : ℝ) R))
    (hpair : ∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Ioo (a ^ 2) (b ^ 2) →
      (∫ r in Ioo (0 : ℝ) R, psi (r ^ 2) • C r) = 0) :
    ∃ f : ℝ → F,
      LocallyIntegrableOn f (Ioo (a ^ 2) (b ^ 2))
          (Measure.map (fun r : ℝ => r ^ 2) (volume.restrict (Ioo 0 R))) ∧
        f ∘ (fun r : ℝ => r ^ 2) =ᵐ[volume.restrict (Ioo 0 R)] C ∧
        (∀ᵐ t ∂(Measure.map (fun r : ℝ => r ^ 2)
          (volume.restrict (Ioo 0 R))).restrict (Ioo (a ^ 2) (b ^ 2)),
          f t = 0) := by
  let μr : Measure ℝ := volume.restrict (Ioo (0 : ℝ) R)
  let sq : ℝ → ℝ := fun r => r ^ 2
  let μ : Measure ℝ := Measure.map sq μr
  let Cm : ℝ → F := hC.aestronglyMeasurable.mk C
  let f : ℝ → F := fun t => if 0 < t then Cm (Real.sqrt t) else 0
  have hCae : C =ᵐ[μr] Cm := hC.aestronglyMeasurable.ae_eq_mk
  have hCm : StronglyMeasurable Cm := hC.aestronglyMeasurable.stronglyMeasurable_mk
  have hfmeas : Measurable f := by
    dsimp only [f]
    exact Measurable.ite measurableSet_Ioi
      (hCm.measurable.comp Real.continuous_sqrt.measurable) measurable_const
  have hfsq : f ∘ sq =ᵐ[μr] C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hCae] with r hr hCr
    dsimp only [f, sq, Function.comp_apply]
    have hrsq : 0 < r ^ 2 := sq_pos_of_pos hr.1
    rw [if_pos hrsq, Real.sqrt_sq hr.1.le]
    exact hCr.symm
  have hcomp : Integrable (f ∘ sq) μr := hC.congr hfsq.symm
  have hfint : Integrable f μ := by
    dsimp only [μ]
    exact (integrable_map_measure hfmeas.aestronglyMeasurable
      (measurable_id.pow_const 2).aemeasurable).mpr hcomp
  have hloc : LocallyIntegrableOn f (Ioo (a ^ 2) (b ^ 2)) μ := by
    have hu : IntegrableOn f (Set.univ : Set ℝ) μ := by
      change Integrable f (μ.restrict Set.univ)
      simpa only [Measure.restrict_univ] using hfint
    exact hu.locallyIntegrableOn.mono_set (by intro t ht; trivial)
  refine ⟨f, ?_, hfsq, ?_⟩
  · simpa only [μ] using hloc
  have htests : ∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Ioo (a ^ 2) (b ^ 2) →
      (∫ t, psi t • f t ∂μ) = 0 := by
    intro psi hpsi hcompact hsupp
    obtain ⟨Cpsi, hbound⟩ :=
      hpsi.continuous.bounded_above_of_compact_support hcompact
    have htop : MemLp (fun r : ℝ => psi (sq r)) (⊤ : ENNReal) μr := by
      exact memLp_top_of_bound
        ((hpsi.continuous.comp (continuous_pow 2)).aestronglyMeasurable)
        Cpsi (by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          exact hbound (sq r))
    have hsmul : Integrable (fun r : ℝ => psi (sq r) • C r) μr :=
      hC.smul_of_top_right htop
    have hsmul_comp : Integrable
        (fun r : ℝ => psi (sq r) • f (sq r)) μr := by
      apply hsmul.congr
      filter_upwards [hfsq] with r hr
      simpa only [Function.comp_apply] using
        congrArg (fun z => psi (sq r) • z) hr.symm
    have hsq : AEMeasurable sq μr := (measurable_id.pow_const 2).aemeasurable
    have hmap := integral_map (μ := μr) (f := fun t => psi t • f t) hsq
      ((hpsi.continuous.measurable.smul hfmeas).aestronglyMeasurable)
    calc
      (∫ t, psi t • f t ∂μ) =
          ∫ r, psi (sq r) • f (sq r) ∂μr := hmap
      _ = ∫ r in Ioo (0 : ℝ) R, psi (r ^ 2) • C r := by
        apply integral_congr_ae
        filter_upwards [hfsq] with r hr
        change psi (sq r) • f (sq r) = psi (sq r) • C r
        simpa only [Function.comp_apply] using
          congrArg (fun z => psi (sq r) • z) hr
      _ = 0 := hpair psi (hpsi.of_le (by simp)) hcompact hsupp
  · exact radialCoefficient_ae_eq_zero_of_test_pairings hloc htests

end PoincareConjecture
