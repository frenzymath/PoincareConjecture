import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityEnergy
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityWeightedPotential











set_option autoImplicit false

open MeasureTheory Set Filter Metric
open scoped Topology SchwartzMap LineDeriv InnerProductSpace ContDiff

namespace PoincareConjecture.M65Boundary

open EuclideanTranslationNative EuclideanDerivativeNative DeTurckDomainRegularityNative
  DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem regularized_test (χ : 𝓢(E, ℝ)) (hc : HasCompactSupport χ)
    (x : E) (α ε : ℝ) (hε : 0 < ε) :
    ∃ η : 𝓢(E, ℝ), HasCompactSupport η ∧ tsupport η ⊆ tsupport χ ∧
      (∀ z, η z ^ 2 = χ z ^ 2 * (‖z - x‖ ^ 2 + ε ^ 2) ^ (-α / 2)) ∧
      ∀ z (i : Fin 2),
        2 * η z * fderiv ℝ η z (EuclideanSpace.single i 1) =
          2 * χ z * (‖z - x‖ ^ 2 + ε ^ 2) ^ (-α / 2) *
            fderiv ℝ χ z (EuclideanSpace.single i 1) -
          α * χ z ^ 2 * (‖z - x‖ ^ 2 + ε ^ 2) ^ (-α / 2) /
            (‖z - x‖ ^ 2 + ε ^ 2) * (z i - x i) := by
  let q := fun z : E => ‖z - x‖ ^ 2 + ε ^ 2
  have hq (z : E) : 0 < q z := by dsimp only [q]; positivity
  have hqs : ContDiff ℝ ∞ q :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).add contDiff_const
  let w := fun z : E => q z ^ (-α / 4)
  have hws : ContDiff ℝ ∞ w := hqs.rpow_const_of_ne (fun z => (hq z).ne')
  have hs : HasCompactSupport (fun z => χ z * w z) := hc.mul_right
  let η : 𝓢(E, ℝ) := hs.toSchwartzMap ((χ.smooth ⊤).mul hws)
  have heta (z : E) : η z = χ z * w z := rfl
  have hw2 (z : E) : w z * w z = q z ^ (-α / 2) := by
    dsimp only [w]
    rw [← Real.rpow_add (hq z)]
    congr 1
    ring
  refine ⟨η, hs, ?_, ?_, ?_⟩
  · exact tsupport_mul_subset_left
  · intro z
    rw [heta, mul_pow, sq (w z), hw2]
  intro z i
  have hDq : HasFDerivAt q (2 • innerSL ℝ (z - x)) z := by
    have hD := ((hasStrictFDerivAt_norm_sq (z - x)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub_const x)).add_const (ε ^ 2)
    simpa +instances only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq, q] using! hD
  have hDw := hDq.rpow_const (p := -α / 4) (Or.inl (hq z).ne')
  have hDη := (χ.differentiable z).hasFDerivAt.mul hDw
  change HasFDerivAt (fun z => χ z * w z) _ z at hDη
  have hDval : fderiv ℝ η z (EuclideanSpace.single i 1) =
      w z * fderiv ℝ χ z (EuclideanSpace.single i 1) +
        χ z * ((-α / 4) * q z ^ (-α / 4 - 1) * (2 * (z i - x i))) := by
    change fderiv ℝ (fun z => χ z * w z) z (EuclideanSpace.single i 1) = _
    rw [hDη.fderiv]
    simp only [add_apply, smul_apply,
      smul_eq_mul, innerSL_apply_apply, EuclideanSpace.inner_single_right,
      one_mul, conj_trivial, PiLp.sub_apply, w, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [heta, hDval, Real.rpow_sub_one (hq z).ne']
  change 2 * (χ z * w z) *
      (w z * fderiv ℝ χ z (EuclideanSpace.single i 1) +
        χ z * ((-α / 4) * (w z / q z) * (2 * (z i - x i)))) = _
  calc
    _ = 2 * χ z * (w z * w z) * fderiv ℝ χ z (EuclideanSpace.single i 1) -
        α * χ z ^ 2 * (w z * w z) / q z * (z i - x i) := by ring
    _ = _ := by rw [hw2]

private theorem multiplier_energy_integral {N : ℕ} (η : 𝓢(E, ℝ))
    (d : Fin N → Fin 2 → ScalarL2 2) :
    Integrable (fun z => η z ^ 2 * ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) ∧
      (∫ z, η z ^ 2 * ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) =
        ∑ j : Fin N, ∑ i : Fin 2, ‖schwartzMultiplier η (d j i)‖ ^ 2 := by
  have hsingle (j : Fin N) (i : Fin 2) :
      Integrable (fun z => η z ^ 2 * (d j i z) ^ 2) := by
    apply (Lp.memLp (schwartzMultiplier η (d j i))).integrable_sq.congr
    filter_upwards [schwartzMultiplier_coe η (d j i)] with z hz
    rw [hz]
    ring
  constructor
  · simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ
      (fun j _ => integrable_finsetSum Finset.univ (fun i _ => hsingle j i))
  · simp only [Finset.mul_sum]
    rw [integral_finsetSum _ (fun j _ =>
      integrable_finsetSum Finset.univ (fun i _ => hsingle j i))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum _ (fun i _ => hsingle j i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [scalarLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [schwartzMultiplier_coe η (d j i)] with z hz
    rw [hz]
    ring

private theorem energy_absorption {N : ℕ} (u : Fin N → ScalarL2 2)
    (d : Fin N → Fin 2 → ScalarL2 2) (f : Fin N → E → ℝ)
    (hf : ∀ j, Integrable (f j)) {U : Set E} (hU : IsOpen U)
    (hweak : ∀ j i (φ : 𝓢(E, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ j (φ : 𝓢(E, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z))
    {B : ℝ} (hbound : ∀ j, ∀ᵐ z ∂volume, ‖u j z‖ ≤ B)
    (hsmall : ∀ᵐ z ∂volume, z ∈ U →
      |∑ j : Fin N, f j z * u j z| ≤ (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) / 2)
    (η : 𝓢(E, ℝ)) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    (∑ j : Fin N, ∑ i : Fin 2, ‖schwartzMultiplier η (d j i)‖ ^ 2) ≤
      -4 * ∑ j : Fin N, ∑ i : Fin 2,
        ⟪schwartzMultiplier η (d j i),
          schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} η) (u j)⟫_ℝ := by
  have hfinite (j : Fin N) : Integrable (fun z => η z ^ 2 * (f j z * u j z)) := by
    have hb : ∀ᵐ z ∂volume, ‖η z ^ 2 * u j z‖ ≤ (SchwartzMap.seminorm ℝ 0 0 η) ^ 2 * B := by
      filter_upwards [hbound j] with z hz
      rw [norm_mul, norm_pow]
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (η.norm_le_seminorm ℝ z) 2) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hz (sq_nonneg _))
    have hi := (hf j).mul_bdd ((η.continuous.pow 2).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (u j))) hb
    apply hi.congr
    filter_upwards [] with z
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    ring
  have hpairing : Integrable (fun z => η z ^ 2 * (∑ j : Fin N, f j z * u j z)) := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun j _ => hfinite j)
  have hi := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ =>
    weighted_energy_identity (u j) (d j) (f j) (hf j) hU
      (hweak j) (heq j) (hbound j) η hc hs)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib] at hi
  rw [← integral_finsetSum _ (fun j _ => hfinite j)] at hi
  simp only [← Finset.mul_sum] at hi
  obtain ⟨hEint, hEeq⟩ := multiplier_energy_integral η d
  have hforcing : -(∫ z, η z ^ 2 * (∑ j : Fin N, f j z * u j z)) ≤
      (∑ j : Fin N, ∑ i : Fin 2, ‖schwartzMultiplier η (d j i)‖ ^ 2) / 2 := by
    rw [← integral_neg, ← hEeq, ← integral_div]
    apply integral_mono_ae hpairing.neg (hEint.div_const 2)
    filter_upwards [hsmall] with z hz
    dsimp only [Pi.neg_apply]
    by_cases hzU : z ∈ U
    · have hp := (neg_le_abs (∑ j : Fin N, f j z * u j z)).trans (hz hzU)
      nlinarith only [mul_le_mul_of_nonneg_left hp (sq_nonneg (η z))]
    · have hzη : η z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzU (hs h))
      simp only [hzη, zero_pow (by decide : 2 ≠ 0), zero_mul, neg_zero, zero_div, le_refl]
  linarith only [hi, hforcing]

private theorem radial_weight_bound {r ε α β : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) :
    (r ^ 2 + ε ^ 2) ^ (-α / 2) / (r ^ 2 + ε ^ 2) * r * r ^ β ≤
      r ^ (-(α + 1 - β)) := by
  have hq : 0 < r ^ 2 + ε ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) (sq_nonneg ε)
  have hpow : (r ^ 2 + ε ^ 2) ^ (-α / 2 - 1) ≤ (r ^ 2) ^ (-α / 2 - 1) :=
    Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hr) (le_add_of_nonneg_right (sq_nonneg ε))
      (by linarith)
  calc
    _ = (r ^ 2 + ε ^ 2) ^ (-α / 2 - 1) * r * r ^ β := by
      rw [Real.rpow_sub_one hq.ne']
    _ ≤ (r ^ 2) ^ (-α / 2 - 1) * r * r ^ β :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hr.le)
        (Real.rpow_nonneg hr.le _)
    _ = r ^ (-(α + 1 - β)) := by
      calc
        _ = r ^ (2 * (-α / 2 - 1)) * r ^ (1 : ℝ) * r ^ β := by
          have hs := Real.rpow_natCast_mul hr.le 2 (-α / 2 - 1)
          norm_num only [Nat.cast_ofNat] at hs
          rw [hs, Real.rpow_one]
        _ = r ^ (2 * (-α / 2 - 1) + 1 + β) := by
          rw [Real.rpow_add hr, Real.rpow_add hr]
        _ = _ := by congr 1; ring

private theorem weighted_cross_point {r ε α β H ρ c t v d s : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hα : 0 ≤ α) (hH : 0 ≤ H)
    (hc : |c| ≤ 1) (hs : |s| ≤ r) (hv : |v| ≤ H * r ^ β)
    (ht : r < ρ → t = 0) :
    -(2 * c * (r ^ 2 + ε ^ 2) ^ (-α / 2) * t -
        α * c ^ 2 * (r ^ 2 + ε ^ 2) ^ (-α / 2) / (r ^ 2 + ε ^ 2) * s) * v * d ≤
      c ^ 2 * (r ^ 2 + ε ^ 2) ^ (-α / 2) * d ^ 2 / 4 +
        4 * ρ ^ (-α) * (t * v) ^ 2 + α * H * r ^ (-(α + 1 - β)) * |d| := by
  let weight := (r ^ 2 + ε ^ 2) ^ (-α / 2)
  let q := r ^ 2 + ε ^ 2
  have hq : 0 < q := add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) (sq_nonneg ε)
  have hweight : 0 ≤ weight := Real.rpow_nonneg hq.le _
  have hc2 : c ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg c) hc 2
  have hcut : weight * (t * v) ^ 2 ≤ ρ ^ (-α) * (t * v) ^ 2 := by
    by_cases hrρ : r < ρ
    · simp only [ht hrρ, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
    have hsquares : ρ ^ 2 ≤ r ^ 2 + ε ^ 2 := by
      have hl := le_of_not_gt hrρ
      nlinarith [sq_nonneg ε]
    have hp := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hρ) hsquares (by linarith : -α / 2 ≤ 0)
    have hscale : (ρ ^ 2) ^ (-α / 2) = ρ ^ (-α) := by
      rw [← Real.rpow_natCast_mul hρ.le 2]
      congr 1
      ring
    rw [hscale] at hp
    exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)
  have hyoung : -2 * c * weight * t * v * d ≤
      c ^ 2 * weight * d ^ 2 / 4 + 4 * weight * (t * v) ^ 2 := by
    nlinarith only [mul_nonneg hweight (sq_nonneg (c * d / 2 + 2 * t * v))]
  have hrad : α * c ^ 2 * weight / q * s * v * d ≤
      α * H * r ^ (-(α + 1 - β)) * |d| := by
    calc
      _ ≤ |α * c ^ 2 * weight / q * s * v * d| := le_abs_self _
      _ = α * c ^ 2 * (weight / q) * |s| * |v| * |d| := by
        rw [abs_mul, abs_mul, abs_mul, abs_div, abs_mul, abs_mul,
          abs_of_nonneg hα, abs_of_nonneg (sq_nonneg c), abs_of_nonneg hweight, abs_of_pos hq]
        ring
      _ ≤ α * 1 * (weight / q) * r * (H * r ^ β) * |d| := by gcongr
      _ = α * H * (weight / q * r * r ^ β) * |d| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (radial_weight_bound hr hα) (mul_nonneg hα hH))
        (abs_nonneg d)
  change -(2 * c * weight * t - α * c ^ 2 * weight / q * s) * v * d ≤ _
  nlinarith only [hyoung, hcut, hrad]





theorem regularized_weighted_energy_step {N : ℕ} (u : Fin N → ScalarL2 2)
    (d : Fin N → Fin 2 → ScalarL2 2) (f : Fin N → E → ℝ)
    (hf : ∀ j, Integrable (f j)) {U : Set E} (hU : IsOpen U)
    (hweak : ∀ j i (φ : 𝓢(E, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ j (φ : 𝓢(E, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z))
    {B H α β ρ ε : ℝ} (hbound : ∀ j, ∀ᵐ z ∂volume, ‖u j z‖ ≤ B)
    (hsmall : ∀ᵐ z ∂volume, z ∈ U →
      |∑ j : Fin N, f j z * u j z| ≤ (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) / 2)
    (x : E) (hH : 0 ≤ H) (hα : 0 ≤ α) (hρ : 0 < ρ) (hε : 0 < ε)
    (hholder : ∀ j, ∀ᵐ z ∂volume, z ∈ U → |u j z| ≤ H * ‖z - x‖ ^ β)
    (χ : 𝓢(E, ℝ)) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U)
    (hχ : ∀ z, |χ z| ≤ 1)
    (hflat : ∀ z, ‖z - x‖ < ρ → ∀ i : Fin 2,
      fderiv ℝ χ z (EuclideanSpace.single i 1) = 0)
    (hJ : Integrable (fun z => ‖z - x‖ ^ (-(α + 1 - β)) *
      (∑ j : Fin N, ∑ i : Fin 2, |d j i z|))) :
    Integrable (fun z => χ z ^ 2 * (‖z - x‖ ^ 2 + ε ^ 2) ^ (-α / 2) *
      (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)) ∧
      (∫ z, χ z ^ 2 * (‖z - x‖ ^ 2 + ε ^ 2) ^ (-α / 2) *
        (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)) ≤
        16 * ρ ^ (-α) * (∑ j : Fin N, ∑ i : Fin 2,
          ‖schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ) (u j)‖ ^ 2) +
          4 * α * H * ∫ z, ‖z - x‖ ^ (-(α + 1 - β)) *
            (∑ j : Fin N, ∑ i : Fin 2, |d j i z|) := by
  obtain ⟨η, hηc, hηs, hη2, hηD⟩ := regularized_test χ hc x α ε hε
  let Dη (i : Fin 2) := ∂_{EuclideanSpace.single i (1 : ℝ)} η
  let Dχ (i : Fin 2) := ∂_{EuclideanSpace.single i (1 : ℝ)} χ
  let cross (z : E) := ∑ j : Fin N, ∑ i : Fin 2,
    η z * Dη i z * u j z * d j i z
  let err (z : E) := ∑ j : Fin N, ∑ i : Fin 2, (Dχ i z * u j z) ^ 2
  let en (z : E) := η z ^ 2 * ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2
  let J (z : E) := ‖z - x‖ ^ (-(α + 1 - β)) * ∑ j : Fin N, ∑ i : Fin 2, |d j i z|
  have hp (j : Fin N) (i : Fin 2) :
      Integrable (fun z => η z * Dη i z * u j z * d j i z) ∧
        (∫ z, η z * Dη i z * u j z * d j i z) =
          ⟪schwartzMultiplier η (d j i), schwartzMultiplier (Dη i) (u j)⟫_ℝ := by
    constructor
    · apply ((Lp.memLp (schwartzMultiplier η (d j i))).integrable_mul
        (Lp.memLp (schwartzMultiplier (Dη i) (u j)))).congr
      filter_upwards [schwartzMultiplier_coe η (d j i),
        schwartzMultiplier_coe (Dη i) (u j)] with z h1 h2
      dsimp only [Pi.mul_apply]
      rw [h1, h2]
      ring
    · rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [schwartzMultiplier_coe η (d j i),
        schwartzMultiplier_coe (Dη i) (u j)] with z h1 h2
      rw [h1, h2]
      simp only [Real.inner_apply]
      ring
  have hdi (j : Fin N) (i : Fin 2) :
      Integrable (fun z => (Dχ i z * u j z) ^ 2) ∧
        (∫ z, (Dχ i z * u j z) ^ 2) = ‖schwartzMultiplier (Dχ i) (u j)‖ ^ 2 := by
    constructor
    · apply (Lp.memLp (schwartzMultiplier (Dχ i) (u j))).integrable_sq.congr
      filter_upwards [schwartzMultiplier_coe (Dχ i) (u j)] with z hz
      rw [hz]
    · rw [scalarLp_norm_sq]
      apply integral_congr_ae
      filter_upwards [schwartzMultiplier_coe (Dχ i) (u j)] with z hz
      rw [hz]
  have hcross : Integrable cross := integrable_finsetSum Finset.univ
    (fun j _ => integrable_finsetSum Finset.univ (fun i _ => (hp j i).1))
  have herr : Integrable err := integrable_finsetSum Finset.univ
    (fun j _ => integrable_finsetSum Finset.univ (fun i _ => (hdi j i).1))
  have hcrossEq : (∫ z, cross z) = ∑ j : Fin N, ∑ i : Fin 2,
      ⟪schwartzMultiplier η (d j i), schwartzMultiplier (Dη i) (u j)⟫_ℝ := by
    rw [show cross = _ from rfl, integral_finsetSum _ (fun j _ =>
      integrable_finsetSum Finset.univ (fun i _ => (hp j i).1))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum _ (fun i _ => (hp j i).1)]
    exact Finset.sum_congr rfl (fun i _ => (hp j i).2)
  have herrEq : (∫ z, err z) = ∑ j : Fin N, ∑ i : Fin 2,
      ‖schwartzMultiplier (Dχ i) (u j)‖ ^ 2 := by
    rw [show err = _ from rfl, integral_finsetSum _ (fun j _ =>
      integrable_finsetSum Finset.univ (fun i _ => (hdi j i).1))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum _ (fun i _ => (hdi j i).1)]
    exact Finset.sum_congr rfl (fun i _ => (hdi j i).2)
  obtain ⟨hen, henEq⟩ := multiplier_energy_integral η d
  have habs := energy_absorption u d f hf hU hweak heq hbound hsmall η hηc (hηs.trans hs)
  rw [← henEq, ← hcrossEq] at habs
  have hne : ∀ᵐ z : E ∂volume, z ≠ x := ae_iff.mpr (by simp)
  have hpoint : ∀ᵐ z ∂volume,
      -2 * cross z ≤ en z / 4 + 4 * ρ ^ (-α) * err z + α * H * J z := by
    filter_upwards [hne, ae_all_iff.mpr hholder] with z hzx hzH
    have hr : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
    have hterm (j : Fin N) (i : Fin 2) :
        -2 * (η z * Dη i z * u j z * d j i z) ≤ η z ^ 2 * (d j i z) ^ 2 / 4 +
          4 * ρ ^ (-α) * (Dχ i z * u j z) ^ 2 +
            α * H * ‖z - x‖ ^ (-(α + 1 - β)) * |d j i z| := by
      by_cases hzU : z ∈ U
      · have hcoord : |z i - x i| ≤ ‖z - x‖ := by
          simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (z - x) i
        have h := weighted_cross_point (ε := ε) (d := d j i z)
          hr hρ hα hH (hχ z) hcoord (hzH j hzU)
          (fun hlt => hflat z hlt i)
        rw [← hη2 z, ← hηD z i] at h
        simpa only [Dχ, Dη, SchwartzMap.lineDerivOp_apply_eq_fderiv,
          neg_mul, mul_assoc] using h
      · have hzη : η z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzU (hηs.trans hs h))
        simp only [hzη, zero_mul, mul_zero,
          zero_pow (by decide : 2 ≠ 0), zero_div, zero_add]
        positivity
    have hsums := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm j i))
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div,
      cross, en, err, J, mul_assoc] using hsums
  have hint := integral_mono_ae (hcross.const_mul (-2))
    (((hen.div_const 4).add (herr.const_mul (4 * ρ ^ (-α)))).add (hJ.const_mul (α * H))) hpoint
  dsimp only [Pi.add_apply] at hint
  rw [integral_add (f := fun z => en z / 4 + 4 * ρ ^ (-α) * err z)
    (g := fun z => α * H * J z)
    ((hen.div_const 4).add (herr.const_mul (4 * ρ ^ (-α))))
    (hJ.const_mul (α * H)), integral_add (f := fun z => en z / 4)
      (g := fun z => 4 * ρ ^ (-α) * err z) (hen.div_const 4)
      (herr.const_mul (4 * ρ ^ (-α))),
    integral_const_mul, integral_div, integral_const_mul, integral_const_mul, herrEq] at hint
  constructor
  · simpa only [hη2] using hen
  · have hresult : (∫ z, en z) ≤
        16 * ρ ^ (-α) * (∑ j : Fin N, ∑ i : Fin 2,
          ‖schwartzMultiplier (Dχ i) (u j)‖ ^ 2) + 4 * α * H * ∫ z, J z := by
      linarith only [habs, hint]
    simpa only [en, J, Dχ, hη2] using hresult

private theorem singular_weight_limit (x : E) {α C : ℝ} {F : E → ℝ}
    (hF : AEStronglyMeasurable F volume) (hF0 : ∀ᵐ z ∂volume, 0 ≤ F z)
    (hbound : ∀ ε : ℝ, 0 < ε →
      Integrable (fun z => (‖z - x‖ ^ 2 + ε ^ 2) ^ (-α / 2) * F z) ∧
        (∫ z, (‖z - x‖ ^ 2 + ε ^ 2) ^ (-α / 2) * F z) ≤ C) :
    Integrable (fun z => ‖z - x‖ ^ (-α) * F z) ∧
      (∫ z, ‖z - x‖ ^ (-α) * F z) ≤ C := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  let f (n : ℕ) (z : E) := (‖z - x‖ ^ 2 + ε n ^ 2) ^ (-α / 2) * F z
  let g (z : E) := ‖z - x‖ ^ (-α) * F z
  have hfi (n : ℕ) : Integrable (f n) := (hbound (ε n) (hε n)).1
  have hf0 (n : ℕ) : ∀ᵐ z ∂volume, 0 ≤ f n z := by
    filter_upwards [hF0] with z hz
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) hz
  have hg : AEStronglyMeasurable g volume := by
    exact (by fun_prop : Measurable (fun z : E => ‖z - x‖ ^ (-α))).aestronglyMeasurable.mul hF
  have hg0 : ∀ᵐ z ∂volume, 0 ≤ g z := by
    filter_upwards [hF0] with z hz
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hz
  have hnormInt (n : ℕ) : (∫ z, ‖f n z‖) = ∫ z, f n z := by
    apply integral_congr_ae
    filter_upwards [hf0 n] with z hz
    exact Real.norm_of_nonneg hz
  have hgnormInt : (∫ z, ‖g z‖) = ∫ z, g z := by
    apply integral_congr_ae
    filter_upwards [hg0] with z hz
    exact Real.norm_of_nonneg hz
  have hC : 0 ≤ C := (integral_nonneg_of_ae (hf0 0)).trans (hbound (ε 0) (hε 0)).2
  have hnorm (n : ℕ) : eLpNorm (f n) 1 volume ≤ ENNReal.ofReal C := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hfi n), hnormInt]
    exact ENNReal.ofReal_le_ofReal (hbound (ε n) (hε n)).2
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hne : ∀ᵐ z : E ∂volume, z ≠ x := ae_iff.mpr (by simp)
  have hlim : ∀ᵐ z ∂volume, Tendsto (fun n => f n z) atTop (𝓝 (g z)) := by
    filter_upwards [hne] with z hz
    have hr : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
    have hq : Tendsto (fun n => ‖z - x‖ ^ 2 + ε n ^ 2) atTop (𝓝 (‖z - x‖ ^ 2)) := by
      simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using
        (hεlim.pow 2).const_add (‖z - x‖ ^ 2)
    have hp := (hq.rpow_const (p := -α / 2) (Or.inl (sq_pos_of_pos hr).ne')).mul_const (F z)
    have heq : (‖z - x‖ ^ 2) ^ (-α / 2) = ‖z - x‖ ^ (-α) := by
      rw [← Real.rpow_natCast_mul hr.le 2]
      congr 1
      ring
    simpa only [f, g, heq] using hp
  have hnormG : eLpNorm g 1 volume ≤ ENNReal.ofReal C :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hnorm) (fun n => (hfi n).1) hlim
  have hgi : Integrable g := memLp_one_iff_integrable.mp ⟨hg,
    hnormG.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hgi, ?_⟩
  have hnormGreal : ENNReal.ofReal (∫ z, g z) ≤ ENNReal.ofReal C := by
    rwa [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hgi,
      hgnormInt] at hnormG
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hnormGreal






theorem weighted_energy_step {N : ℕ} (u : Fin N → ScalarL2 2)
    (d : Fin N → Fin 2 → ScalarL2 2) (f : Fin N → E → ℝ)
    (hf : ∀ j, Integrable (f j)) {U : Set E} (hU : IsOpen U)
    (hweak : ∀ j i (φ : 𝓢(E, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ j (φ : 𝓢(E, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z))
    {B H α β ρ : ℝ} (hbound : ∀ j, ∀ᵐ z ∂volume, ‖u j z‖ ≤ B)
    (hsmall : ∀ᵐ z ∂volume, z ∈ U →
      |∑ j : Fin N, f j z * u j z| ≤ (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) / 2)
    (x : E) (hH : 0 ≤ H) (hα : 0 ≤ α) (hρ : 0 < ρ)
    (hholder : ∀ j, ∀ᵐ z ∂volume, z ∈ U → |u j z| ≤ H * ‖z - x‖ ^ β)
    (χ : 𝓢(E, ℝ)) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U)
    (hχ : ∀ z, |χ z| ≤ 1)
    (hflat : ∀ z, ‖z - x‖ < ρ → ∀ i : Fin 2,
      fderiv ℝ χ z (EuclideanSpace.single i 1) = 0)
    (hJ : Integrable (fun z => ‖z - x‖ ^ (-(α + 1 - β)) *
      (∑ j : Fin N, ∑ i : Fin 2, |d j i z|))) :
    Integrable (fun z => χ z ^ 2 * ‖z - x‖ ^ (-α) *
      (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)) ∧
      (∫ z, χ z ^ 2 * ‖z - x‖ ^ (-α) *
        (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)) ≤
        16 * ρ ^ (-α) * (∑ j : Fin N, ∑ i : Fin 2,
          ‖schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ) (u j)‖ ^ 2) +
          4 * α * H * ∫ z, ‖z - x‖ ^ (-(α + 1 - β)) *
            (∑ j : Fin N, ∑ i : Fin 2, |d j i z|) := by
  let F := fun z => χ z ^ 2 * ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2
  have hF : AEStronglyMeasurable F volume := by
    apply (χ.continuous.pow 2).aestronglyMeasurable.mul
    exact Finset.aestronglyMeasurable_fun_sum _ (fun j _ =>
      Finset.aestronglyMeasurable_fun_sum _ (fun i _ => (Lp.aestronglyMeasurable (d j i)).pow 2))
  have hF0 : ∀ᵐ z ∂volume, 0 ≤ F z := ae_of_all _ fun z => by
    dsimp only [F]
    positivity
  have hprod (ε : ℝ) (hε : 0 < ε) :=
    regularized_weighted_energy_step u d f hf hU hweak heq hbound hsmall x hH hα hρ hε
      hholder χ hc hs hχ hflat hJ
  have hresult := singular_weight_limit (α := α) x hF hF0 (fun ε hε => by
    simpa only [F, mul_left_comm, mul_assoc] using hprod ε hε)
  simpa only [F, mul_left_comm, mul_assoc] using hresult

end PoincareConjecture.M65Boundary
