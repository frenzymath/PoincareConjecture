import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EpsilonRegularityFlux




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold
namespace PoincareConjecture.M60

section ScalarIteration
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

theorem suWeakSubsolution_cutoff_energy
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (A : V → V →L[ℝ] V →L[ℝ] ℝ) (hA : Continuous A)
    (hsym : ∀ x v w, A x v w = A x w v) {L κ p : ℝ}
    (hell : ∀ x v, g.inner x v v ≤ A x v v ∧ A x v v ≤ L * g.inner x v v)
    {O : Set V} {f η : V → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (hp : 1 ≤ p) (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hηc : HasCompactSupport η) (hηO : tsupport η ⊆ O)
    (hweak : ∀ φ : V → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ O → (∀ x, 0 ≤ φ x) →
      (∫ x, A x (D.gradient f x) (D.gradient φ x) ∂g.volumeMeasure) ≤
        κ * ∫ x, f x * φ x ∂g.volumeMeasure) :
    (∫ x, g.inner x (D.gradient (fun y => η y * f y ^ p) x)
        (D.gradient (fun y => η y * f y ^ p) x) ∂g.volumeMeasure) ≤
      p * κ * (∫ x, η x ^ 2 * (f x ^ p) ^ 2 ∂g.volumeMeasure) +
        L * (∫ x, (f x ^ p) ^ 2 *
          g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure) := by
  let W : V → ℝ := fun x => η x * f x ^ p
  let φ : V → ℝ := fun x => (η x * η x) * f x ^ (2 * p - 1)
  have hfp := LeviCivitaData.contMDiff_rpow_of_pos hf hpos p
  have hfq := LeviCivitaData.contMDiff_rpow_of_pos hf hpos (2 * p - 1)
  have hW : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ W := hη.mul hfp
  have hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ := (hη.mul hη).mul hfq
  have hWc : HasCompactSupport W := hηc.mul_right
  have hφc : HasCompactSupport φ := hηc.mul_right.mul_right
  have hcgrad {U : V → ℝ} (hU : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ U) :
      Continuous (D.gradient U) :=
    (contMDiff_vectorSpace_iff_contDiff.mp (D.contMDiff_gradient hU)).continuous
  have hpair : Integrable (fun x => A x (D.gradient f x) (D.gradient φ x))
      g.volumeMeasure := by
    apply ((hA.clm_apply (hcgrad hf)).clm_apply (hcgrad hφ)).integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact hφc
    intro x hx
    by_contra hx'
    exact hx (by
      change A x (D.gradient f x) (D.gradient φ x) = 0
      rw [D.gradient_eq_zero_of_notMem_tsupport hx', map_zero])
  have hcut : Integrable (fun x => (f x ^ p) ^ 2 *
      g.inner x (D.gradient η x) (D.gradient η x)) g.volumeMeasure :=
    ((hfp.pow 2).continuous.mul (D.continuous_inner_gradient hη hη)).integrable_of_hasCompactSupport
      (D.hasCompactSupport_inner_gradient hηc η).mul_left
  have hpoint (x : V) :
      g.inner x (D.gradient W x) (D.gradient W x) ≤
      p * A x (D.gradient f x) (D.gradient φ x) +
        L * ((f x ^ p) ^ 2 * g.inner x (D.gradient η x) (D.gradient η x)) := by
    have hηd := (hη x).mdifferentiableAt (by simp)
    have hpd := (hfp x).mdifferentiableAt (by simp)
    have hqd := (hfq x).mdifferentiableAt (by simp)
    have hWder : D.gradient W x = η x • ((p * f x ^ (p - 1)) • D.gradient f x) +
        f x ^ p • D.gradient η x := by
      rw [show W = (fun y => η y * f y ^ p) from rfl,
        D.gradient_mul hηd hpd, D.gradient_rpow_of_pos hf hpos]
    have hφder : D.gradient φ x =
        (η x * η x) • (((2 * p - 1) * f x ^ (2 * p - 1 - 1)) • D.gradient f x) +
        f x ^ (2 * p - 1) • (η x • D.gradient η x + η x • D.gradient η x) := by
      have hηηd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => η y * η y) x := hηd.mul hηd
      rw [show φ = (fun y => (η y * η y) * f y ^ (2 * p - 1)) from rfl,
        D.gradient_mul hηηd hqd, D.gradient_mul hηd hηd,
        D.gradient_rpow_of_pos hf hpos]
    have hp1 : f x ^ p = f x * f x ^ (p - 1) := by
      calc
        _ = f x ^ (1 + (p - 1)) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add (hpos x), Real.rpow_one]
    have hp2 : f x ^ (2 * p - 1 - 1) = (f x ^ (p - 1)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hpos x).le]
      congr 1
      ring
    have hp3 : f x ^ (2 * p - 1) = f x * (f x ^ (p - 1)) ^ 2 := by
      rw [← hp2]
      calc
        _ = f x ^ (1 + (2 * p - 1 - 1)) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add (hpos x), Real.rpow_one]
    have hnonneg : 0 ≤ A x (D.gradient f x) (D.gradient f x) := by
      apply le_trans _ (hell x _).1
      by_cases hz : D.gradient f x = 0
      · simp [hz]
      · exact (g.pos x _ hz).le
    have hid : A x (D.gradient W x) (D.gradient W x) =
        p * A x (D.gradient f x) (D.gradient φ x) +
        (f x ^ p) ^ 2 * A x (D.gradient η x) (D.gradient η x) -
        p * (p - 1) * (η x * f x ^ (p - 1)) ^ 2 *
          A x (D.gradient f x) (D.gradient f x) := by
      rw [hWder, hφder, hp1, hp2, hp3]
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      rw [hsym x (D.gradient η x) (D.gradient f x)]
      ring
    have hbad : 0 ≤ p * (p - 1) * (η x * f x ^ (p - 1)) ^ 2 *
        A x (D.gradient f x) (D.gradient f x) := by
      have hp0 : 0 ≤ p := le_trans (by norm_num) hp
      exact mul_nonneg (mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hp)) (sq_nonneg _)) hnonneg
    have hcutpoint := mul_le_mul_of_nonneg_left (hell x (D.gradient η x)).2 (sq_nonneg (f x ^ p))
    have hlower := (hell x (D.gradient W x)).1
    rw [hid] at hlower
    nlinarith only [hlower, hbad, hcutpoint]
  have hwi := hweak φ hφ hφc
    (by
      apply subset_trans _ hηO
      apply closure_mono
      intro x hx
      by_contra hx'
      have hηx : η x = 0 := by simpa only [Function.mem_support, not_not] using hx'
      exact hx (by simp [φ, hηx]))
    (fun x => mul_nonneg (mul_self_nonneg _) (Real.rpow_pos_of_pos (hpos x) _).le)
  have hmass : (∫ x, f x * φ x ∂g.volumeMeasure) =
      ∫ x, η x ^ 2 * (f x ^ p) ^ 2 ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards with x
    have he : f x * f x ^ (2 * p - 1) = (f x ^ p) ^ 2 := by
      calc
        _ = f x ^ (1 + (2 * p - 1)) := by rw [Real.rpow_add (hpos x), Real.rpow_one]
        _ = f x ^ (p * 2) := by congr 1; ring
        _ = _ := by rw [Real.rpow_mul (hpos x).le, Real.rpow_two]
    dsimp only [φ]
    nlinarith only [he]
  rw [hmass] at hwi
  have hi := integral_mono (D.integrable_inner_gradient hW hW hWc)
    ((hpair.const_mul p).add (hcut.const_mul L)) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (hpair.const_mul p) (hcut.const_mul L), integral_const_mul,
    integral_const_mul] at hi
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have h := mul_le_mul_of_nonneg_left hwi hp0
  change (∫ x, g.inner x (D.gradient W x) (D.gradient W x) ∂g.volumeMeasure) ≤ _
  linarith only [hi, h]
end ScalarIteration

theorem exists_uniform_divergence_mean_value :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ D : LeviCivitaData (RiemannianMetric.euclideanMetric 2),
      ∀ A : LoopPlane → LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ,
        Continuous A → (∀ x v w, A x v w = A x w v) →
        (∀ x v, ‖v‖ ^ 2 ≤ A x v v ∧ A x v v ≤ 2 * ‖v‖ ^ 2) →
        ∀ f : LoopPlane → ℝ, ContDiff ℝ ∞ f → (∀ x, 0 < f x) →
        (∀ φ : LoopPlane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ Metric.ball 0 r → (∀ x, 0 ≤ φ x) →
          (∫ x, A x (D.gradient f x) (D.gradient φ x)
            ∂(RiemannianMetric.euclideanMetric 2).volumeMeasure) ≤
          (1 / r ^ 2) * ∫ x, f x * φ x
            ∂(RiemannianMetric.euclideanMetric 2).volumeMeasure) →
        f 0 ≤ (C / r) *
          (eLpNorm f 2 (volume.restrict (Metric.closedBall 0 (r / 2)))).toReal := by
  obtain ⟨C, hC, hmean⟩ := HarmonicCoordinates.exists_uniform_energy_mean_value
    (n := 2) (by norm_num) (a := 1) (b := 1) (P := 2) (Λ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun r hr hr1 D A hA hsym hell f hf hpos hweak => ?_⟩
  let g := RiemannianMetric.euclideanMetric 2
  have hfs : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f := contMDiff_iff_contDiff.mpr hf
  have hella (x v : LoopPlane) : g.inner x v v ≤ A x v v ∧
      A x v v ≤ 2 * g.inner x v v := by
    simpa only [g, RiemannianMetric.euclideanMetric_inner, real_inner_self_eq_norm_sq]
      using hell x v
  have he (p : ℝ) (hp : 1 ≤ p) (η : LoopPlane → ℝ)
      (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
      (hηs : tsupport η ⊆ Metric.ball 0 r) :
      (∫ x, g.inner x (D.gradient (fun y => η y * f y ^ p) x)
        (D.gradient (fun y => η y * f y ^ p) x) ∂g.volumeMeasure) ≤
      2 * p ^ 2 * ((1 / r ^ 2) * (∫ x, η x ^ 2 * (f x ^ p) ^ 2 ∂g.volumeMeasure) +
        ∫ x, (f x ^ p) ^ 2 * g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure) := by
    have h := suWeakSubsolution_cutoff_energy D A hA hsym hella hfs hpos hp
      (contMDiff_iff_contDiff.mpr hη) hηc hηs
      (fun φ hφ hφc hφs hφp => hweak φ (contMDiff_iff_contDiff.mp hφ) hφc hφs hφp)
    have hm : 0 ≤ ∫ x, η x ^ 2 * (f x ^ p) ^ 2 ∂g.volumeMeasure :=
      integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hc : 0 ≤ ∫ x, (f x ^ p) ^ 2 *
        g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure :=
      integral_nonneg fun _ => by
        rw [RiemannianMetric.euclideanMetric_inner, real_inner_self_eq_norm_sq]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hκ : 0 ≤ 1 / r ^ 2 := by positivity
    have hpm := mul_le_mul_of_nonneg_right (show p ≤ 2 * p ^ 2 by nlinarith)
      (mul_nonneg hκ hm)
    have hpc := mul_le_mul_of_nonneg_right (show 1 ≤ p ^ 2 by nlinarith)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc)
    nlinarith only [h, hpm, hpc]
  have hm := hmean r hr hr1 g D (fun x _ v => by
      change 1 * ‖v‖ ^ 2 ≤ inner ℝ v v ∧ inner ℝ v v ≤ 1 * ‖v‖ ^ 2
      simp only [real_inner_self_eq_norm_sq, one_mul, le_refl, and_self])
    0 (Metric.closedBall_subset_ball (by linarith)) f hf hpos he
  norm_num only [Nat.cast_ofNat, neg_div, neg_neg, div_self (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_neg_one] at hm
  simpa only [div_eq_mul_inv] using hm
private theorem euclideanGradient_translate
    (D : LeviCivitaData (RiemannianMetric.euclideanMetric 2)) (f : LoopPlane → ℝ)
    (p x : LoopPlane) : D.gradient (fun y => f (p + y)) x = D.gradient f (p + x) := by
  unfold LeviCivitaData.gradient
  simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
  change (innerSL ℝ).inverse (fderiv ℝ (fun y => f (p + y)) x) =
    (innerSL ℝ).inverse (fderiv ℝ f (p + x))
  rw [fderiv_comp_add_left]

theorem exists_divergence_mean_value_sq :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : LoopPlane) (r : ℝ), 0 < r → r ≤ 1 →
      ∀ D : LeviCivitaData (RiemannianMetric.euclideanMetric 2),
      ∀ A : LoopPlane → LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ,
        Continuous A → (∀ x v w, A x v w = A x w v) →
        (∀ x v, ‖v‖ ^ 2 ≤ A x v v ∧ A x v v ≤ 2 * ‖v‖ ^ 2) →
        ∀ f : LoopPlane → ℝ, ContDiff ℝ ∞ f → (∀ x, 0 < f x) →
        (∀ φ : LoopPlane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ Metric.ball p r → (∀ x, 0 ≤ φ x) →
          (∫ x, A x (D.gradient f x) (D.gradient φ x)) ≤
            (1 / r ^ 2) * ∫ x, f x * φ x) →
        r ^ 2 * (f p) ^ 2 ≤ C ^ 2 * ∫ x in Metric.closedBall p (r / 2), (f x) ^ 2 := by
  obtain ⟨C, hC, hmean⟩ := exists_uniform_divergence_mean_value
  refine ⟨C, hC, fun p r hr hr1 D A hA hsym hell f hf hpos hweak => ?_⟩
  let v : LoopPlane → ℝ := fun x => f (p + x)
  have hv : ContDiff ℝ ∞ v := hf.comp (contDiff_const.add contDiff_id)
  have hm := hmean r hr hr1 D (fun x => A (p + x))
    (hA.comp (continuous_const.add continuous_id)) (fun x => hsym (p + x))
    (fun x => hell (p + x)) v hv (fun x => hpos (p + x)) (by
      intro φ hφ hφc hφs hφp
      let ψ : LoopPlane → ℝ := fun x => φ (-p + x)
      have hψc : HasCompactSupport ψ := hφc.comp_homeomorph (Homeomorph.addLeft (-p))
      have hψs : tsupport ψ ⊆ Metric.ball p r := by
        change tsupport (φ ∘ (Homeomorph.addLeft (-p))) ⊆ _
        rw [tsupport_comp_eq_preimage]
        intro x hx
        have hx' := hφs hx
        change -p + x ∈ Metric.ball 0 r at hx'
        simpa only [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, neg_zero, add_zero,
          add_comm] using hx'
      have h := hweak ψ (hφ.comp (contDiff_const.add contDiff_id)) hψc hψs
        (fun x => hφp (-p + x))
      rw [← integral_add_left_eq_self (fun x => A x (D.gradient f x) (D.gradient ψ x)) p,
        ← integral_add_left_eq_self (fun x => f x * ψ x) p] at h
      have hcancel : ∀ x : LoopPlane, -p + (p + x) = x := by intro x; abel
      have hgrad (x : LoopPlane) : D.gradient φ (-p + (p + x)) = D.gradient φ x := by
        congr 1; exact hcancel x
      simp only [ψ, euclideanGradient_translate, hcancel] at h
      simpa only [RiemannianMetric.euclideanMetric_volumeMeasure, v,
        euclideanGradient_translate, hgrad] using h)
  have hm' : f p ≤ (C / r) *
      (eLpNorm v 2 (volume.restrict (Metric.closedBall 0 (r / 2)))).toReal := by
    simpa only [v, add_zero] using hm
  have hs := mul_self_le_mul_self (hpos p).le hm'
  rw [← pow_two, ← pow_two, mul_pow, div_pow,
    Poincare.Analysis.Sobolev.eLpNorm_toReal_sq_eq_integral
      (HarmonicCoordinates.continuous_memLp_restrict_closedBall hv.continuous 0 (r / 2) 2),
    show (∫ x in Metric.closedBall 0 (r / 2), (v x) ^ 2) =
      ∫ x in Metric.closedBall p (r / 2), (f x) ^ 2 from
        suSetIntegral_closedBall_add_left (fun x => (f x) ^ 2) p (r / 2)] at hs
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg r)
  convert! hmul using 1
  field_simp

theorem exists_positive_divergence_heinz :
    ∃ B : ℝ, 0 < B ∧ ∀ (K L R : ℝ), 0 ≤ K → 0 ≤ L → 0 < R → R ≤ 1 →
      ∀ D : LeviCivitaData (RiemannianMetric.euclideanMetric 2),
      ∀ A : LoopPlane → LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ,
      Continuous A → (∀ x v w, A x v w = A x w v) →
      (∀ x v, ‖v‖ ^ 2 ≤ A x v v ∧ A x v v ≤ 2 * ‖v‖ ^ 2) →
      ∀ u : LoopPlane → ℝ, ContDiff ℝ ∞ u → (∀ x, 0 < u x) →
      (∀ φ : LoopPlane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 R → (∀ x, 0 ≤ φ x) →
        (∫ x, A x (D.gradient u x) (D.gradient φ x)) ≤
          K * (∫ x, (u x) ^ 2 * φ x) + L * (∫ x, u x * φ x)) →
      B * K * (∫ x in Metric.closedBall 0 R, u x) ≤ 1 →
      R ^ 2 * u 0 ≤ B * (1 + L) * (∫ x in Metric.closedBall 0 R, u x) := by
  obtain ⟨C, hC, hmean⟩ := exists_divergence_mean_value_sq
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨32 * C ^ 2, by positivity,
    fun K L R hK hL hR hR1 D A hA hsym hell u hu hpos hw hsmall => ?_⟩
  let E : ℝ := ∫ x in Metric.closedBall 0 R, u x
  obtain ⟨p, s, hs, hsR, hup, hsub, hcenter, hbound⟩ := exists_heinz_disk hR
    hu.continuous.continuousOn (fun x _ => (hpos x).le) (hpos 0)
  let B : ℝ := 1 + (4 * K * u p + L) * s ^ 2
  have hB : 1 ≤ B := le_add_of_nonneg_right (by positivity)
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hroot : 1 ≤ Real.sqrt B := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hB
  have hrootp : 0 < Real.sqrt B := lt_of_lt_of_le zero_lt_one hroot
  let r := s / Real.sqrt B
  have hr : 0 < r := div_pos hs hrootp
  have hrs : r ≤ s := div_le_self hs.le hroot
  have hrsq : r ^ 2 = s ^ 2 / B := by dsimp only [r]; rw [div_pow, Real.sq_sqrt hBp.le]
  have hscale : 4 * K * u p + L ≤ 1 / r ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    rw [hrsq, ← mul_div_assoc]; apply (div_le_iff₀ hBp).mpr
    dsimp only [B]; linarith
  have hball : Metric.closedBall p r ⊆ Metric.closedBall p s :=
    Metric.closedBall_subset_closedBall hrs
  have hm := hmean p r hr (by linarith) D A hA hsym hell u hu hpos (by
    intro φ hφ hφc hφs hφp
    have hsu : tsupport φ ⊆ Metric.ball 0 R :=
      hφs.trans (Metric.ball_subset_closedBall.trans (hball.trans hsub))
    have hi := hw φ hφ hφc hsu hφp
    have hi1 := ((hu.continuous.pow 2).mul hφ.continuous).integrable_of_hasCompactSupport
      (μ := volume) hφc.mul_left
    have hi2 := (hu.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      (μ := volume) hφc.mul_left
    rw [← integral_const_mul, ← integral_const_mul] at hi
    erw [← integral_add (hi1.const_mul K) (hi2.const_mul L)] at hi
    rw [← integral_const_mul]
    apply hi.trans (integral_mono ((hi1.const_mul K).add (hi2.const_mul L))
      (hi2.const_mul (1 / r ^ 2)) ?_)
    intro x
    change K * ((u x) ^ 2 * φ x) + L * (u x * φ x) ≤ (1 / r ^ 2) * (u x * φ x)
    by_cases hx : x ∈ tsupport φ
    · have hux := hbound x (hball (Metric.ball_subset_closedBall (hφs hx)))
      have hk : K * u x + L ≤ 1 / r ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_left hux hK, hscale]
      have hh := mul_le_mul_of_nonneg_right hk (mul_nonneg (hpos x).le (hφp x))
      nlinarith only [hh]
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, add_zero, le_refl])
  have hhalf : Metric.closedBall p (r/2) ⊆ Metric.closedBall p s :=
    Metric.closedBall_subset_closedBall (by linarith)
  have hiu := hu.continuous.continuousOn.integrableOn_compact
    (μ := volume) (isCompact_closedBall p (r/2))
  have hiu2 := (hu.continuous.pow 2).continuousOn.integrableOn_compact
    (μ := volume) (isCompact_closedBall p (r/2))
  have hie := hu.continuous.continuousOn.integrableOn_compact
    (μ := volume) (isCompact_closedBall 0 R)
  have hmass : (∫ x in Metric.closedBall p (r/2), u x) ≤ E :=
    setIntegral_mono_set hie (Eventually.of_forall fun x => (hpos x).le)
      (Eventually.of_forall fun _ hx => Metric.ball_subset_closedBall (hsub (hhalf hx)))
  have he : (∫ x in Metric.closedBall p (r/2), (u x) ^ 2) ≤ 4 * u p * E := by
    calc
      _ ≤ ∫ x in Metric.closedBall p (r/2), (4 * u p) * u x := by
        apply integral_mono_ae hiu2 (hiu.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
        change (u x) ^ 2 ≤ (4 * u p) * u x
        nlinarith only [mul_le_mul_of_nonneg_right (hbound x (hhalf hx)) (hpos x).le]
      _ = (4 * u p) * (∫ x in Metric.closedBall p (r/2), u x) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  have hsq := hm.trans (mul_le_mul_of_nonneg_left he (sq_nonneg C))
  have hpoint : r ^ 2 * u p ≤ 4 * C ^ 2 * E := by
    apply (mul_le_mul_iff_right₀ hup).mp; nlinarith only [hsq]
  have hT : s ^ 2 * u p ≤ (4 * C ^ 2 * E) * B := by
    apply (div_le_iff₀ hBp).mp; simpa only [hrsq, div_mul_eq_mul_div] using hpoint
  have hsm := mul_le_mul_of_nonneg_right hsmall (mul_nonneg (sq_nonneg s) hup.le)
  change (32 * C ^ 2 * K * E) * (s ^ 2 * u p) ≤ 1 * (s ^ 2 * u p) at hsm
  have hE : 0 ≤ E := integral_nonneg fun x => (hpos x).le
  have hs1 : s ^ 2 ≤ 1 := by nlinarith only [hs, hsR, hR1]
  have hLE := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ C ^ 2 * L * E)
  change R ^ 2 * u 0 ≤ 32 * C ^ 2 * (1 + L) * E
  dsimp only [B] at hT
  nlinarith only [hcenter, hT, hsm, hLE]

end PoincareConjecture.M60
