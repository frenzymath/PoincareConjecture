import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalWeakTest
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Coefficients
import Mathlib.Analysis.MeanInequalitiesPow









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal Convolution
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.DifferenceQuotient
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergStandardTest

noncomputable section

namespace PoincareConjecture.M60

private abbrev Plane := EuclideanSpace ℝ (Fin 2)




theorem suNaturalGrowth_potential_bound
    {n : ℕ} {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤) (hq : 1 ≤ q)
    [ENNReal.HolderConjugate q p]
    {O : Set Plane} (hO : IsOpen O)
    {F du : Fin n → Fin 2 → Plane → ℝ} {b u : Fin n → Plane → ℝ}
    {ξ H W : Plane → ℝ} {ν B δ C₀ : ℝ}
    (hν : 0 < ν)
    (hsmall : B * δ ≤ ν / 4)
    (hH : ∀ x, 0 ≤ H x) (hW : ∀ x, 0 ≤ W x)
    (hF : ∀ k i, MemLp (F k i) q volume) (hb : ∀ k, Integrable (b k))
    (hu : ∀ k, Continuous (u k)) (hdu : ∀ k i, MemLp (du k i) p volume)
    (hweak : ∀ k i, HasWeakPartialDeriv i (du k i) (u k) univ)
    (hξ : ContDiff ℝ ∞ ξ) (hξc : HasCompactSupport ξ) (hξO : tsupport ξ ⊆ O)
    (heq : ∀ k (φ : Plane → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x, ∑ i : Fin 2, F k i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, b k x * φ x)
    (hcoercive : ∀ x, ν * H x - C₀ ≤ ∑ k, ∑ i, F k i x * du k i x)
    (hsource : ∀ x, (∑ k, b k x * u k x) ≤ B * δ * H x)
    (hcross : ∀ x, (∑ k, ∑ i, F k i x * u k x *
      fderiv ℝ ξ x (EuclideanSpace.single i 1)) ^ 2 ≤
      B ^ 2 * δ ^ 2 * H x * W x *
        ∑ i : Fin 2, (fderiv ℝ ξ x (EuclideanSpace.single i 1)) ^ 2)
    (hHI : Integrable (fun x => H x * ξ x ^ 2))
    (hWI : Integrable (fun x => W x *
      ∑ i : Fin 2, (fderiv ℝ ξ x (EuclideanSpace.single i 1)) ^ 2)) :
    ν / 2 * (∫ x, H x * ξ x ^ 2) ≤ C₀ * (∫ x, ξ x ^ 2) +
      (4 * B ^ 2 * δ ^ 2 / ν) *
        ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ ξ x (EuclideanSpace.single i 1)) ^ 2 := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : Fact (1 ≤ q) := ⟨hq⟩
  let dξ (i : Fin 2) (x : Plane) := fderiv ℝ ξ x (EuclideanSpace.single i 1)
  let v (k : Fin n) (x : Plane) := ξ x ^ 2 * u k x
  let dv (k : Fin n) (i : Fin 2) (x : Plane) :=
    ξ x ^ 2 * du k i x + 2 * ξ x * dξ i x * u k x
  have hξ2c : HasCompactSupport (fun x => ξ x ^ 2) := by
    exact hξc.of_isClosed_subset (isClosed_tsupport _) <|
      tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) ξ
  have hξ2top : MemLp (fun x => ξ x ^ 2) ⊤ volume :=
    (hξ.continuous.pow 2).memLp_of_hasCompactSupport hξ2c
  have hdξ (i : Fin 2) : Continuous (dξ i) :=
    (hξ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdv (k : Fin n) (i : Fin 2) : MemLp (dv k i) p volume := by
    apply ((hdu k i).mul' hξ2top).add
    have hc : Continuous (fun x => 2 * ξ x * dξ i x * u k x) :=
      ((continuous_const.mul hξ.continuous).mul (hdξ i)).mul (hu k)
    exact hc.memLp_of_hasCompactSupport ((hξc.mul_left.mul_right).mul_right)
  have hv (k : Fin n) : MemLp (v k) ⊤ volume :=
    ((hξ.continuous.pow 2).mul (hu k)).memLp_of_hasCompactSupport hξ2c.mul_right
  have hleft (k : Fin n) (i : Fin 2) : Integrable (fun x => F k i x * dv k i x) :=
    memLp_one_iff_integrable.mp ((hdv k i).mul' (hF k i))
  have hright (k : Fin n) : Integrable (fun x => b k x * v k x) :=
    memLp_one_iff_integrable.mp ((hv k).mul' (memLp_one_iff_integrable.mpr (hb k)))
  let L (x : Plane) := ∑ k, ∑ i, F k i x * dv k i x
  let T (x : Plane) := ∑ k, b k x * v k x
  have hLI : Integrable L := integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun i _ => hleft k i
  have hTI : Integrable T := integrable_finsetSum _ fun k _ => hright k
  have hLT : (∫ x, L x) = ∫ x, T x := by
    rw [show L = fun x => ∑ k, ∑ i, F k i x * dv k i x from rfl,
      integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun i _ => hleft k i),
      show T = fun x => ∑ k, b k x * v k x from rfl,
      integral_finsetSum _ (fun k _ => hright k)]
    apply Finset.sum_congr rfl
    intro k _
    exact suNaturalGrowth_cutoff_test hp hpfin hq hO (hF k) (hb k)
      (hu k) (hdu k) (hweak k) hξ hξc hξO (heq k)
  have hξI : Integrable (fun x => ξ x ^ 2) :=
    (hξ.continuous.pow 2).integrable_of_hasCompactSupport hξ2c
  have hpoint (x : Plane) : ν / 2 * (H x * ξ x ^ 2) ≤
      L x - T x + C₀ * ξ x ^ 2 +
        (4 * B ^ 2 * δ ^ 2 / ν) * (W x * ∑ i, dξ i x ^ 2) := by
    let Z := ∑ k, ∑ i, F k i x * u k x * dξ i x
    have hG : 0 ≤ ∑ i : Fin 2, dξ i x ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hHx := hH x
    have hWx := hW x
    have hyoung : 2 * (-(ξ x * Z)) ≤ ν / 4 * (H x * ξ x ^ 2) +
        (4 * B ^ 2 * δ ^ 2 / ν) * (W x * ∑ i, dξ i x ^ 2) := by
      apply two_mul_le_add_of_sq_le_mul (by positivity) (by positivity)
      calc
        (-(ξ x * Z)) ^ 2 = ξ x ^ 2 * Z ^ 2 := by ring
        _ ≤ ξ x ^ 2 * (B ^ 2 * δ ^ 2 * H x * W x * ∑ i, dξ i x ^ 2) :=
          mul_le_mul_of_nonneg_left (hcross x) (sq_nonneg _)
        _ = _ := by field_simp
    have hc := mul_le_mul_of_nonneg_left (hcoercive x) (sq_nonneg (ξ x))
    have hs := mul_le_mul_of_nonneg_left (hsource x) (sq_nonneg (ξ x))
    have hsm := mul_le_mul_of_nonneg_right hsmall
      (mul_nonneg (hH x) (sq_nonneg (ξ x)))
    have hL : L x = ξ x ^ 2 * (∑ k, ∑ i, F k i x * du k i x) + 2 * ξ x * Z := by
      simp only [L, dv, Z, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;>
        apply Finset.sum_congr rfl <;> intro i _ <;> ring
    have hT : T x = ξ x ^ 2 * (∑ k, b k x * u k x) := by
      simp only [T, v, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hL, hT]
    nlinarith
  have hbound := integral_mono (hHI.const_mul (ν / 2))
    (((hLI.sub hTI).add (hξI.const_mul C₀)).add
      (hWI.const_mul (4 * B ^ 2 * δ ^ 2 / ν))) hpoint
  rw [integral_const_mul, integral_add' ((hLI.sub hTI).add (hξI.const_mul C₀))
      (hWI.const_mul (4 * B ^ 2 * δ ^ 2 / ν)),
    integral_add' (hLI.sub hTI) (hξI.const_mul C₀), integral_sub' hLI hTI,
    hLT, sub_self, zero_add, integral_const_mul, integral_const_mul] at hbound
  exact hbound



def suAlphaFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (c alpha : ℝ) (v : E) : E →L[ℝ] ℝ :=
  (2 * alpha * (c + B v v) ^ (alpha - 1)) • B v

theorem suAlphaFlux_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, 0 ≤ B v v)
    (hsymm : ∀ v w, B v w = B w v) {c : ℝ} (hc : 0 < c) (alpha : ℝ) (v : E) :
    HasFDerivAt (fun w => (c + B w w) ^ alpha) (suAlphaFlux B c alpha v) v := by
  have hQ : HasFDerivAt (fun w => c + B w w) ((2 : ℝ) • B v) v := by
    have hd := (hasFDerivAt_const c v).add (B.hasFDerivAt.clm_apply (hasFDerivAt_id v))
    have heq : (B v).comp (ContinuousLinearMap.id ℝ E) + B.flip v = (2 : ℝ) • B v := by
      ext w
      simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply]
      rw [hsymm w v]
      ring
    simpa only [zero_add, id_eq, heq, Pi.add_def] using! hd
  have hr := hQ.rpow_const (p := alpha) (Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg hc (hB v))))
  convert hr using 1
  ext w
  simp only [suAlphaFlux, smul_apply, smul_eq_mul]
  ring




theorem suAlphaFlux_weighted_monotone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, 0 ≤ B v v)
    (hsymm : ∀ v w, B v w = B w v) {c alpha : ℝ} (hc : 0 ≤ c) (ha : 1 ≤ alpha)
    (v w : E) :
    alpha * ((c + B v v) ^ (alpha - 1) + (c + B w w) ^ (alpha - 1)) *
      B (v - w) (v - w) ≤ (suAlphaFlux B c alpha v - suAlphaFlux B c alpha w) (v - w) := by
  let a := (c + B v v) ^ (alpha - 1)
  let b := (c + B w w) ^ (alpha - 1)
  have hm : 0 ≤ (a - b) * (B v v - B w w) := by
    by_cases h : B v v ≤ B w w
    · have hab : a ≤ b := Real.rpow_le_rpow (add_nonneg hc (hB v))
        (add_le_add (le_refl c) h) (by linarith)
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hab) (sub_nonpos.mpr h)
    · have hab : b ≤ a := Real.rpow_le_rpow (add_nonneg hc (hB w))
        (add_le_add (le_refl c) (le_of_not_ge h)) (by linarith)
      exact mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr (le_of_not_ge h))
  have heq : (suAlphaFlux B c alpha v - suAlphaFlux B c alpha w) (v - w) -
      alpha * (a + b) * B (v - w) (v - w) =
        alpha * ((a - b) * (B v v - B w w)) := by
    simp only [suAlphaFlux, sub_apply, smul_apply, smul_eq_mul, map_sub]
    rw [hsymm w v]
    dsimp only [a, b]
    ring
  have hp := mul_nonneg (show 0 ≤ alpha by linarith) hm
  rw [← heq] at hp
  exact sub_nonneg.mp hp

def suAlphaFluxLinearization {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (c alpha : ℝ) (v : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (2 * alpha * (c + B v v) ^ (alpha - 1)) • B +
    ((4 * alpha * (alpha - 1) * (c + B v v) ^ (alpha - 2)) • B v).smulRight (B v)

theorem suAlphaFluxLinearization_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, 0 ≤ B v v)
    (hsymm : ∀ v w, B v w = B w v) {c : ℝ} (hc : 0 < c) (alpha : ℝ) (v : E) :
    HasFDerivAt (suAlphaFlux B c alpha) (suAlphaFluxLinearization B c alpha v) v := by
  have hQ : HasFDerivAt (fun w => c + B w w) ((2 : ℝ) • B v) v := by
    simpa only [Real.rpow_one, suAlphaFlux, mul_one, sub_self, Real.rpow_zero]
      using suAlphaFlux_hasFDerivAt B hB hsymm hc 1 v
  have hpow := hQ.rpow_const (p := alpha - 1)
    (Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg hc (hB v))))
  have hd := (hpow.const_mul (2 * alpha)).smul B.hasFDerivAt
  have heq : (2 * alpha) • (((alpha - 1) * (c + B v v) ^ (alpha - 1 - 1)) •
      ((2 : ℝ) • B v)) =
      (4 * alpha * (alpha - 1) * (c + B v v) ^ (alpha - 2)) • B v := by
    rw [show alpha - 1 - 1 = alpha - 2 by ring]
    simp only [smul_smul]
    congr 1
    ring
  simpa only [suAlphaFlux, suAlphaFluxLinearization, Pi.smul_def, heq] using! hd



theorem suAlphaFluxLinearization_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, 0 ≤ B v v)
    {c alpha : ℝ} (hc : 0 ≤ c) (ha : 1 ≤ alpha) (v w : E) :
    2 * alpha * (c + B v v) ^ (alpha - 1) * B w w ≤
      suAlphaFluxLinearization B c alpha v w w := by
  have hq : 0 ≤ (c + B v v) ^ (alpha - 2) := Real.rpow_nonneg (add_nonneg hc (hB v)) _
  have hp := mul_nonneg
    (mul_nonneg (mul_nonneg (by positivity : 0 ≤ 4 * alpha) (by linarith : 0 ≤ alpha - 1)) hq)
    (sq_nonneg (B v w))
  simpa only [suAlphaFluxLinearization, add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply, pow_two, mul_assoc] using
    le_add_of_nonneg_right (a := 2 * alpha * (c + B v v) ^ (alpha - 1) * B w w) hp



theorem suAlphaFluxLinearization_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {c alpha κ : ℝ}
    (hc : 0 < c) (ha : 1 ≤ alpha) (hκ : 0 < κ)
    (hB : ∀ v, κ * ‖v‖ ^ 2 ≤ B v v) (v : E) :
    ‖suAlphaFluxLinearization B c alpha v‖ ≤
      2 * alpha * (‖B‖ + 2 * (alpha - 1) * ‖B‖ ^ 2 / κ) *
        (c + B v v) ^ (alpha - 1) := by
  let q := c + B v v
  have hpos : 0 < q := by
    have := hB v
    have := mul_nonneg hκ.le (sq_nonneg ‖v‖)
    dsimp [q]
    linarith
  have hsq : κ * ‖B v‖ ^ 2 ≤ ‖B‖ ^ 2 * q := by
    have hn := B.le_opNorm v
    have hnorm : ‖B v‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖v‖ ^ 2 := by
      nlinarith [norm_nonneg (B v), norm_nonneg B, norm_nonneg v]
    calc
      κ * ‖B v‖ ^ 2 ≤ κ * (‖B‖ ^ 2 * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left hnorm hκ.le
      _ = ‖B‖ ^ 2 * (κ * ‖v‖ ^ 2) := by ring
      _ ≤ ‖B‖ ^ 2 * B v v := mul_le_mul_of_nonneg_left (hB v) (sq_nonneg _)
      _ ≤ ‖B‖ ^ 2 * q := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        dsimp [q]
        linarith
  have hpower : q ^ (alpha - 2) * q = q ^ (alpha - 1) := by
    have ht := Real.rpow_add hpos (alpha - 2) 1
    rw [Real.rpow_one, show alpha - 2 + 1 = alpha - 1 by ring] at ht
    exact ht.symm
  have hw : q ^ (alpha - 2) * ‖B v‖ ^ 2 ≤ ‖B‖ ^ 2 / κ * q ^ (alpha - 1) := by
    apply (mul_le_mul_iff_right₀ hκ).mp
    calc
      κ * (q ^ (alpha - 2) * ‖B v‖ ^ 2) = q ^ (alpha - 2) * (κ * ‖B v‖ ^ 2) := by ring
      _ ≤ q ^ (alpha - 2) * (‖B‖ ^ 2 * q) :=
        mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hpos.le _)
      _ = κ * (‖B‖ ^ 2 / κ * q ^ (alpha - 1)) := by
        rw [mul_left_comm (q ^ (alpha - 2)), hpower]
        field_simp
  have hn := norm_add_le
    ((2 * alpha * q ^ (alpha - 1)) • B)
    (((4 * alpha * (alpha - 1) * q ^ (alpha - 2)) • B v).smulRight (B v))
  have ha' : 0 ≤ 2 * alpha * q ^ (alpha - 1) := by positivity
  have hnormB : ‖(2 * alpha * q ^ (alpha - 1)) • B‖ ≤
      (2 * alpha * q ^ (alpha - 1)) * ‖B‖ := by
    apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
    intro x y
    change ‖(2 * alpha * q ^ (alpha - 1)) * B x y‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ha']
    exact (mul_le_mul_of_nonneg_left (B.le_opNorm₂ x y) ha').trans_eq (by ring)
  simp only [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 4 * alpha * (alpha - 1) * q ^ (alpha - 2))] at hn
  have hmul := mul_le_mul_of_nonneg_left hw
    (by positivity : 0 ≤ 4 * alpha * (alpha - 1))
  change ‖(2 * alpha * q ^ (alpha - 1)) • B +
    ((4 * alpha * (alpha - 1) * q ^ (alpha - 2)) • B v).smulRight (B v)‖ ≤ _
  change _ ≤ 2 * alpha * (‖B‖ + 2 * (alpha - 1) * ‖B‖ ^ 2 / κ) * q ^ (alpha - 1)
  simp only [div_eq_mul_inv] at hmul ⊢
  nlinarith only [hn, hnormB, hmul]




theorem suAlphaFlux_weighted_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {c alpha κ : ℝ}
    (hc : 0 < c) (ha : 1 ≤ alpha) (ha2 : alpha ≤ 2) (hκ : 0 < κ)
    (hB : ∀ v, κ * ‖v‖ ^ 2 ≤ B v v) (hsymm : ∀ v w, B v w = B w v)
    (v w : E) :
    ‖suAlphaFlux B c alpha v - suAlphaFlux B c alpha w‖ ≤
      (2 * alpha * (‖B‖ + 2 * (alpha - 1) * ‖B‖ ^ 2 / κ) *
        ((c + B v v) ^ (alpha - 1) + (c + B w w) ^ (alpha - 1))) * ‖v - w‖ := by
  have hpos (z : E) : 0 ≤ B z z := le_trans (mul_nonneg hκ.le (sq_nonneg _)) (hB z)
  let C := 2 * alpha * (‖B‖ + 2 * (alpha - 1) * ‖B‖ ^ 2 / κ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hseg (z : E) (hz : z ∈ segment ℝ w v) : B z z ≤ B v v + B w w := by
    rcases hz with ⟨a, b, ha0, hb0, hab, rfl⟩
    have heq : a * B w w + b * B v v - B (a • w + b • v) (a • w + b • v) =
        a * b * B (w - v) (w - v) := by
      simp only [map_add, map_smul, smul_apply, smul_eq_mul, add_apply, map_sub, sub_apply]
      rw [hsymm v w]
      have hb : b = 1 - a := by linarith
      rw [hb]
      ring
    have hp := mul_nonneg (mul_nonneg ha0 hb0) (hpos (w - v))
    have haw : a * B w w ≤ B w w :=
      mul_le_of_le_one_left (hpos w) (by linarith)
    have hbv : b * B v v ≤ B v v :=
      mul_le_of_le_one_left (hpos v) (by linarith)
    linarith
  have hb (z : E) (hz : z ∈ segment ℝ w v) :
      ‖suAlphaFluxLinearization B c alpha z‖ ≤
        C * ((c + B v v) ^ (alpha - 1) + (c + B w w) ^ (alpha - 1)) := by
    apply (suAlphaFluxLinearization_norm B hc ha hκ hB z).trans
    apply mul_le_mul_of_nonneg_left _ hC
    calc
      (c + B z z) ^ (alpha - 1) ≤
          ((c + B v v) + (c + B w w)) ^ (alpha - 1) :=
        Real.rpow_le_rpow (add_nonneg hc.le (hpos z)) (by linarith [hseg z hz]) (by linarith)
      _ ≤ (c + B v v) ^ (alpha - 1) + (c + B w w) ^ (alpha - 1) :=
        Real.rpow_add_le_add_rpow (add_nonneg hc.le (hpos v))
          (add_nonneg hc.le (hpos w)) (by linarith) (by linarith)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (suAlphaFluxLinearization_hasFDerivAt B hpos hsymm hc alpha z).differentiableAt)
    (fun z hz => by
      rw [(suAlphaFluxLinearization_hasFDerivAt B hpos hsymm hc alpha z).fderiv]
      exact hb z hz)
    (convex_segment w v) (left_mem_segment ℝ w v) (right_mem_segment ℝ w v)




theorem suWeightedPotential_diffQuot_bound
    {p r t : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤)
    [Fact (1 ≤ r)] [Fact (1 ≤ t)]
    [ENNReal.HolderTriple p p t] [ENNReal.HolderConjugate r t]
    {O : Set Plane} (hO : IsOpen O) {H W u ξ : Plane → ℝ}
    {du : Fin 2 → Plane → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hH : Integrable H) (hW : MemLp W r volume) (hW0 : ∀ x, 0 ≤ W x)
    (hu : Continuous u) (hdu : ∀ i, MemLp (du i) p volume)
    (hweak : ∀ i, HasWeakPartialDeriv i (du i) u univ)
    (hξ : ContDiff ℝ ∞ ξ) (hξc : HasCompactSupport ξ) (hξO : tsupport ξ ⊆ O)
    (hbound : ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x, H x * φ x ^ 2) ≤ c *
        ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2)
    (k : Fin 2) (h : ℝ) :
    (∫ x, H x * (ξ x * diffQuot k h u x) ^ 2) ≤ 2 * c *
      ((∫ x, W x * ∑ i : Fin 2, (ξ x * diffQuot k h (du i) x) ^ 2) +
        ∫ x, W x * ∑ i : Fin 2,
          (fderiv ℝ ξ x (EuclideanSpace.single i 1) * diffQuot k h u x) ^ 2) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let v (x : Plane) := ξ x * diffQuot k h u x
  let a (i : Fin 2) (x : Plane) := ξ x * diffQuot k h (du i) x
  let b (i : Fin 2) (x : Plane) :=
    fderiv ℝ ξ x (EuclideanSpace.single i 1) * diffQuot k h u x
  have hcont := continuous_diffQuot_of_continuous k h hu
  have ha (i : Fin 2) : MemLp (a i) p volume :=
    (suWeakMap_diffQuot_memLp (hdu i) k h).mul'
      (hξ.continuous.memLp_of_hasCompactSupport hξc : MemLp ξ ⊤ volume)
  have hb (i : Fin 2) : MemLp (b i) p volume :=
    (((hξ.continuous_fderiv (by simp)).clm_apply continuous_const).mul hcont
      ).memLp_of_hasCompactSupport ((hξc.fderiv_apply (𝕜 := ℝ) _).mul_right)
  have hw (i : Fin 2) : HasWeakPartialDeriv i (a i + b i) v univ := by
    have hd := NirenbergDiffQuotTestFunction.hasWeakPartialDeriv_diffQuot k i h
      (by simpa only [Measure.restrict_univ] using hu.locallyIntegrable)
      (by simpa only [Measure.restrict_univ] using (hdu i).locallyIntegrable hp) (hweak i)
    exact hd.mul_smooth isOpen_univ hξ
      (by simpa only [Measure.restrict_univ] using hcont.locallyIntegrable)
      (by simpa only [Measure.restrict_univ] using
        (suWeakMap_diffQuot_memLp (hdu i) k h).locallyIntegrable hp)
  have ht := suWeightedPotential_weak_bound (t := t) hp hpfin hO hH hW
    (hξ.continuous.mul hcont) hξc.mul_right (tsupport_mul_subset_left.trans hξO)
    (fun i => (ha i).add (hb i)) hw hbound
  have hi {f : Plane → ℝ} (hf : MemLp f p volume) : Integrable (fun x => W x * f x ^ 2) := by
    have hsq : MemLp (fun x => f x ^ 2) t volume := by simpa only [pow_two] using hf.mul' hf
    exact memLp_one_iff_integrable.mp (hsq.mul' hW)
  have hs (f : Fin 2 → Plane → ℝ) (hf : ∀ i, MemLp (f i) p volume) :
      Integrable (fun x => W x * ∑ i : Fin 2, f i x ^ 2) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ (fun i _ => hi (hf i))
  have hestimate : (∫ x, W x * ∑ i : Fin 2, (a i x + b i x) ^ 2) ≤
      2 * ((∫ x, W x * ∑ i : Fin 2, a i x ^ 2) +
        ∫ x, W x * ∑ i : Fin 2, b i x ^ 2) := by
    calc
      _ ≤ ∫ x, 2 * ((W x * ∑ i : Fin 2, a i x ^ 2) +
          W x * ∑ i : Fin 2, b i x ^ 2) := by
        apply integral_mono (hs (fun i => a i + b i) (fun i => (ha i).add (hb i)))
          (((hs a ha).add (hs b hb)).const_mul 2)
        intro x
        have he : (∑ i : Fin 2, (a i x + b i x) ^ 2) ≤
            2 * ((∑ i : Fin 2, a i x ^ 2) + ∑ i : Fin 2, b i x ^ 2) := by
          calc
            _ ≤ ∑ i : Fin 2, 2 * (a i x ^ 2 + b i x ^ 2) :=
              Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (a i x - b i x)]
            _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
        exact (mul_le_mul_of_nonneg_left he (hW0 x)).trans_eq (by
          dsimp only [Pi.add_apply]
          ring)
      _ = _ := by rw [integral_const_mul, integral_add (hs a ha) (hs b hb)]
  exact ht.trans ((mul_le_mul_of_nonneg_left hestimate hc).trans_eq (by ring))





theorem suNaturalGrowth_diffQuot_absorb
    {n : ℕ} {p q r t : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤) (hq : 1 ≤ q)
    [Fact (1 ≤ r)] [Fact (1 ≤ t)]
    [ENNReal.HolderConjugate q p] [ENNReal.HolderTriple p p t]
    [ENNReal.HolderConjugate r t]
    {O : Set Plane} (hO : IsOpen O)
    {F du : Fin n → Fin 2 → Plane → ℝ} {b u : Fin n → Plane → ℝ}
    {ξ H W : Plane → ℝ} {ν B κ : ℝ}
    (hν : 0 < ν) (hB : 0 ≤ B) (hκ : 0 ≤ κ) (hsmall : 2 * B * κ ≤ ν / 2)
    (hH : Integrable H) (hW : MemLp W r volume) (hW0 : ∀ x, 0 ≤ W x)
    (hF : ∀ a i, MemLp (F a i) q volume) (hb : ∀ a, Integrable (b a))
    (hu : ∀ a, Continuous (u a)) (hdu : ∀ a i, MemLp (du a i) p volume)
    (hweak : ∀ a i, HasWeakPartialDeriv i (du a i) (u a) univ)
    (hξ : ContDiff ℝ ∞ ξ) (hξc : HasCompactSupport ξ) (hξO : tsupport ξ ⊆ O)
    (heq : ∀ a (φ : Plane → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x, ∑ i : Fin 2, F a i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, b a x * φ x)
    (hpotential : ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O → (∫ x, H x * φ x ^ 2) ≤ κ *
        ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2)
    (k : Fin 2) {h : ℝ} (hh : h ≠ 0) (hsupp : cthickening |h| (tsupport ξ) ⊆ O)
    (hpoint : ∀ x,
      ν * (W x * ∑ a : Fin n, ∑ i : Fin 2, (ξ x * diffQuot k h (du a i) x) ^ 2) ≤
        (∑ a : Fin n, ∑ i : Fin 2, diffQuot k h (F a i) x *
          (ξ x ^ 2 * diffQuot k h (du a i) x + 2 * ξ x *
            fderiv ℝ ξ x (EuclideanSpace.single i 1) * diffQuot k h (u a) x)) -
        (∑ a : Fin n, diffQuot k h (b a) x * (ξ x ^ 2 * diffQuot k h (u a) x)) +
        B * ((H x * ξ x ^ 2 + ∑ a : Fin n, H x * (ξ x * diffQuot k h (u a) x) ^ 2) +
          W x * ∑ a : Fin n, ∑ i : Fin 2,
            (fderiv ℝ ξ x (EuclideanSpace.single i 1) * diffQuot k h (u a) x) ^ 2)) :
    (∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, (ξ x * diffQuot k h (du a i) x) ^ 2) ≤
      (2 * B / ν) * ((∫ x, H x * ξ x ^ 2) + (1 + 2 * κ) *
        ∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2,
          (fderiv ℝ ξ x (EuclideanSpace.single i 1) * diffQuot k h (u a) x) ^ 2) := by
  let dξ (i : Fin 2) (x : Plane) := fderiv ℝ ξ x (EuclideanSpace.single i 1)
  let U (a : Fin n) := diffQuot k h (u a)
  let A (a : Fin n) (i : Fin 2) (x : Plane) := ξ x * diffQuot k h (du a i) x
  let J (a : Fin n) (i : Fin 2) (x : Plane) := dξ i x * U a x
  let V (a : Fin n) (x : Plane) := ξ x ^ 2 * U a x
  let DV (a : Fin n) (i : Fin 2) (x : Plane) :=
    ξ x ^ 2 * diffQuot k h (du a i) x + 2 * ξ x * dξ i x * U a x
  have hUc (a : Fin n) : Continuous (U a) := continuous_diffQuot_of_continuous k h (hu a)
  have hAc (a : Fin n) (i : Fin 2) : MemLp (A a i) p volume :=
    (suWeakMap_diffQuot_memLp (hdu a i) k h).mul'
      (hξ.continuous.memLp_of_hasCompactSupport hξc : MemLp ξ ⊤ volume)
  have hJc (a : Fin n) (i : Fin 2) : MemLp (J a i) p volume :=
    (((hξ.continuous_fderiv (by simp)).clm_apply continuous_const).mul (hUc a)
      ).memLp_of_hasCompactSupport ((hξc.fderiv_apply (𝕜 := ℝ) _).mul_right)
  have hξsqc : HasCompactSupport (fun x => ξ x ^ 2) :=
    hξc.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset (g := fun s : ℝ => s ^ 2) (by simp) ξ)
  have hV (a : Fin n) : MemLp (V a) ⊤ volume :=
    ((hξ.continuous.pow 2).mul (hUc a)).memLp_of_hasCompactSupport hξsqc.mul_right
  have hDV (a : Fin n) (i : Fin 2) : MemLp (DV a i) p volume := by
    have hfirst : MemLp (fun x => ξ x * A a i x) p volume := (hAc a i).mul'
      (hξ.continuous.memLp_of_hasCompactSupport hξc : MemLp ξ ⊤ volume)
    have hsecond : MemLp (fun x => (2 * ξ x) * J a i x) p volume := (hJc a i).mul'
      ((continuous_const.mul hξ.continuous).memLp_of_hasCompactSupport hξc.mul_left :
        MemLp (fun x => 2 * ξ x) ⊤ volume)
    convert hfirst.add hsecond using 1
    funext x
    dsimp only [A, J, DV, Pi.add_apply]
    ring
  have hsquare {v : Plane → ℝ} (hv : MemLp v p volume) :
      Integrable (fun x => W x * v x ^ 2) := by
    have hsq : MemLp (fun x => v x ^ 2) t volume := by simpa only [pow_two] using hv.mul' hv
    exact memLp_one_iff_integrable.mp (hsq.mul' hW)
  have hweighted (f : Fin n → Fin 2 → Plane → ℝ) (hf : ∀ a i, MemLp (f a i) p volume) :
      Integrable (fun x => W x * ∑ a : Fin n, ∑ i : Fin 2, f a i x ^ 2) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun a _ =>
      integrable_finsetSum _ fun i _ => hsquare (hf a i)
  have hAI := hweighted A hAc
  have hJI := hweighted J hJc
  have hPI (a : Fin n) : Integrable (fun x => H x * (ξ x * U a x) ^ 2) := by
    have hc := (hξ.continuous.mul (hUc a)).pow 2
    have hs : HasCompactSupport (fun x => (ξ x * U a x) ^ 2) :=
      hξc.mul_right.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_comp_subset (g := fun s : ℝ => s ^ 2) (by simp) (fun x => ξ x * U a x))
    exact memLp_one_iff_integrable.mp
      ((hc.memLp_of_hasCompactSupport hs : MemLp _ ⊤ volume).mul'
        (memLp_one_iff_integrable.mpr hH))
  have hKI : Integrable (fun x => H x * ξ x ^ 2) := by
    have hs : HasCompactSupport (fun x => ξ x ^ 2) := hξc.of_isClosed_subset
      (isClosed_tsupport _) (tsupport_comp_subset (g := fun s : ℝ => s ^ 2) (by simp) ξ)
    exact memLp_one_iff_integrable.mp
      (((hξ.continuous.pow 2).memLp_of_hasCompactSupport hs : MemLp _ ⊤ volume).mul'
        (memLp_one_iff_integrable.mpr hH))
  let L (x : Plane) := ∑ a : Fin n, ∑ i : Fin 2, diffQuot k h (F a i) x * DV a i x
  let T (x : Plane) := ∑ a : Fin n, diffQuot k h (b a) x * V a x
  have hLI : Integrable L := integrable_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun i _ => memLp_one_iff_integrable.mp
      ((hDV a i).mul' (suWeakMap_diffQuot_memLp (hF a i) k h))
  have hTI : Integrable T := integrable_finsetSum _ fun a _ =>
    memLp_one_iff_integrable.mp ((hV a).mul'
      (suWeakMap_diffQuot_memLp (memLp_one_iff_integrable.mpr (hb a)) k h))
  have hequal : (∫ x, L x) = ∫ x, T x := by
    rw [show L = fun x => ∑ a : Fin n, ∑ i : Fin 2,
        diffQuot k h (F a i) x * DV a i x from rfl,
      integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun i _ =>
        memLp_one_iff_integrable.mp ((hDV a i).mul'
          (suWeakMap_diffQuot_memLp (hF a i) k h))),
      show T = fun x => ∑ a : Fin n, diffQuot k h (b a) x * V a x from rfl,
      integral_finsetSum _ (fun a _ => memLp_one_iff_integrable.mp ((hV a).mul'
        (suWeakMap_diffQuot_memLp (memLp_one_iff_integrable.mpr (hb a)) k h)))]
    apply Finset.sum_congr rfl
    intro a _
    exact suNaturalGrowth_nirenberg_identity hp hpfin hq hO (hF a) (hb a)
      (hu a) (hdu a) (hweak a) hξ hξc (heq a) k hh hsupp
  have hpot := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin n))) =>
    suWeightedPotential_diffQuot_bound (t := t) hp hpfin hO hκ hH hW hW0
      (hu a) (hdu a) (hweak a) hξ hξc hξO hpotential k h)
  have hsumW (f : Fin n → Fin 2 → Plane → ℝ) (hf : ∀ a i, MemLp (f a i) p volume) :
      (∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, f a i x ^ 2) =
        ∑ a : Fin n, ∫ x, W x * ∑ i : Fin 2, f a i x ^ 2 := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ fun a _ => integrable_finsetSum _ fun i _ => hsquare (hf a i)
  have hpotential' : (∫ x, ∑ a : Fin n, H x * (ξ x * U a x) ^ 2) ≤
      2 * κ * ((∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, A a i x ^ 2) +
        ∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, J a i x ^ 2) := by
    rw [integral_finsetSum _ (fun a _ => hPI a), hsumW A hAc, hsumW J hJc]
    simpa only [U, A, J, dξ, mul_add, Finset.mul_sum, Finset.sum_add_distrib] using hpot
  have hmain := integral_mono (hAI.const_mul ν)
    ((hLI.sub hTI).add ((hKI.add (integrable_finsetSum _ (fun a _ => hPI a))
      |>.add hJI).const_mul B)) hpoint
  rw [integral_const_mul, integral_add' (hLI.sub hTI)
      (((hKI.add (integrable_finsetSum _ (fun a _ => hPI a))).add hJI).const_mul B),
    integral_sub' hLI hTI,
    hequal, sub_self, zero_add, integral_const_mul,
    integral_add' (hKI.add (integrable_finsetSum _ (fun a _ => hPI a))) hJI,
    integral_add' hKI (integrable_finsetSum _ (fun a _ => hPI a))] at hmain
  have hI0 : 0 ≤ ∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, A a i x ^ 2 :=
    integral_nonneg fun x => mul_nonneg (hW0 x)
      (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hsm := mul_le_mul_of_nonneg_right hsmall hI0
  have hpB := mul_le_mul_of_nonneg_left hpotential' hB
  change (∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, A a i x ^ 2) ≤
    (2 * B / ν) * ((∫ x, H x * ξ x ^ 2) + (1 + 2 * κ) *
      ∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, J a i x ^ 2)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hν).mpr
  nlinarith



theorem suWeightedCutoff_diffQuot_bounded
    {p r t : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤) [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p p t] [ENNReal.HolderConjugate r t]
    {u ξ W : Plane → ℝ} {du : Fin 2 → Plane → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hdu : ∀ i, MemLp (du i) p volume)
    (hweak : ∀ i, HasWeakPartialDeriv i (du i) u univ)
    (hξ : ContDiff ℝ ∞ ξ) (hξc : HasCompactSupport ξ) (hW : MemLp W r volume) :
    ∃ C : Fin 2 → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ (i k : Fin 2) (h : ℝ),
      Integrable (fun x => (W x + translate k h W x) *
        (fderiv ℝ ξ x (EuclideanSpace.single i 1) * diffQuot k h u x) ^ 2) ∧
      (∫ x, (W x + translate k h W x) *
        (fderiv ℝ ξ x (EuclideanSpace.single i 1) * diffQuot k h u x) ^ 2) ≤ C i := by
  obtain ⟨CU, hCU, hUbound⟩ := suWeakMap_diffQuot_bounded hp hpfin hu huc hdu hweak
  let d (i : Fin 2) (x : Plane) := fderiv ℝ ξ x (EuclideanSpace.single i 1)
  have hd (i : Fin 2) : MemLp (d i) ⊤ volume :=
    ((hξ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hξc.fderiv_apply (𝕜 := ℝ) _)
  let CV (i : Fin 2) := eLpNorm (d i) ⊤ volume * CU
  let CB (i : Fin 2) := (eLpNorm W r volume + eLpNorm W r volume) * (CV i * CV i)
  have hCV (i : Fin 2) : CV i < ⊤ := ENNReal.mul_lt_top (hd i).2 hCU
  have hCB (i : Fin 2) : CB i < ⊤ := ENNReal.mul_lt_top
    (ENNReal.add_lt_top.mpr ⟨hW.2, hW.2⟩) (ENNReal.mul_lt_top (hCV i) (hCV i))
  refine ⟨fun i => (CB i).toReal, fun i => ENNReal.toReal_nonneg, fun i k h => ?_⟩
  let U := diffQuot k h u
  let V (x : Plane) := d i x * U x
  let S (x : Plane) := W x + translate k h W x
  have hU : MemLp U p volume := suWeakMap_diffQuot_memLp
    (hu.memLp_of_hasCompactSupport huc) k h
  have hV : MemLp V p volume := hU.mul' (hd i)
  have hVbound : eLpNorm V p volume ≤ CV i := by
    have hb := eLpNorm_smul_le_mul_eLpNorm (p := ⊤) (q := p) (r := p) hU.1 (hd i).1
    have hb' : eLpNorm V p volume ≤ eLpNorm (d i) ⊤ volume * eLpNorm U p volume := by
      simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def, V] using hb
    exact hb'.trans (mul_le_mul' le_rfl (hUbound k h))
  have hS : MemLp S r volume := hW.add (memLp_translate k h hW)
  have hSbound : eLpNorm S r volume ≤ eLpNorm W r volume + eLpNorm W r volume := by
    have ht : eLpNorm (translate k h W) r volume = eLpNorm W r volume :=
      eLpNorm_comp_measurePreserving hW.1
        (measurePreserving_add_right volume (h • EuclideanSpace.single k (1 : ℝ)))
    exact (eLpNorm_add_le hW.1 (memLp_translate k h hW).1 Fact.out).trans_eq (by rw [ht])
  have hVsq : MemLp (fun x => V x ^ 2) t volume := by simpa only [pow_two] using hV.mul' hV
  have hVsqbound : eLpNorm (fun x => V x ^ 2) t volume ≤ CV i * CV i := by
    have hb := eLpNorm_smul_le_mul_eLpNorm (p := p) (q := p) (r := t) hV.1 hV.1
    have hb' : eLpNorm (fun x => V x ^ 2) t volume ≤ eLpNorm V p volume *
        eLpNorm V p volume := by
      simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def, pow_two] using hb
    exact hb'.trans (mul_le_mul' hVbound hVbound)
  have hI : Integrable (fun x => S x * V x ^ 2) :=
    memLp_one_iff_integrable.mp (hVsq.mul' hS)
  refine ⟨hI, ?_⟩
  have hprod : eLpNorm (fun x => S x * V x ^ 2) 1 volume ≤ CB i := by
    have hb := eLpNorm_smul_le_mul_eLpNorm (p := r) (q := t) (r := 1) hVsq.1 hS.1
    have hb' : eLpNorm (fun x => S x * V x ^ 2) 1 volume ≤
        eLpNorm S r volume * eLpNorm (fun x => V x ^ 2) t volume := by
      simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def] using hb
    exact hb'.trans (mul_le_mul' hSbound hVsqbound)
  have hint : ‖∫ x, S x * V x ^ 2‖ₑ ≤ CB i := by
    apply (enorm_integral_le_lintegral_enorm _).trans
    simpa only [eLpNorm_one_eq_lintegral_enorm] using hprod
  have ht := ENNReal.toReal_mono (hCB i).ne hint
  have habs : |∫ x, S x * V x ^ 2| ≤ (CB i).toReal := by
    simpa only [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using ht
  exact (le_abs_self _).trans habs



theorem suWeakMap_localization {m : ℕ} {p r R : ℝ} (hp : 1 < p) (hrR : r < R)
    {center : LoopPlane} {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)}
    (hu : ContinuousOn u (Metric.closedBall center R))
    (hup : MemLp u (ENNReal.ofReal p) (volume.restrict (Metric.ball center R)))
    (hV : ∀ i, MemLp (V i) (ENNReal.ofReal p) (volume.restrict (Metric.ball center R)))
    (hw : ∀ (i : Fin 2) (a : Fin m), HasWeakPartialDeriv i (fun x => V i x a)
      (fun x => u x a) (Metric.ball center R)) :
    ∃ chi : LoopPlane → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ Metric.ball center R ∧
      (∀ x ∈ Metric.ball center r, chi x = 1 ∧ fderiv ℝ chi x = 0) ∧
      ∀ a : Fin m,
        let U := fun x => chi x * (u x a - u center a)
        let DU := fun i x => chi x * V i x a +
          fderiv ℝ chi x (EuclideanSpace.single i 1) * (u x a - u center a)
        Continuous U ∧ HasCompactSupport U ∧ MemLp U (ENNReal.ofReal p) volume ∧
          ∀ i : Fin 2, MemLp (DU i) (ENNReal.ofReal p) volume ∧
            HasWeakPartialDeriv i (DU i) U univ := by
  let mu := volume.restrict (Metric.ball center R)
  let : IsFiniteMeasure mu := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  obtain ⟨chi, hchi, hchic, _, hchi1, hchiO⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      (isCompact_closedBall center ((r + R) / 2)) isOpen_ball
      (Metric.closedBall_subset_ball (by linarith : (r + R) / 2 < R))
  refine ⟨chi, hchi, hchic, hchiO, ?_, ?_⟩
  · intro x hx
    have hxmid : x ∈ Metric.ball center ((r + R) / 2) :=
      Metric.ball_subset_ball (by linarith : r ≤ (r + R) / 2) hx
    have he : chi =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hxmid)
        (fun y hy => hchi1 y (Metric.ball_subset_closedBall hy))
    exact ⟨he.self_of_nhds, by simpa using he.fderiv_eq (𝕜 := ℝ)⟩
  · intro a
    have hp1 : 1 ≤ ENNReal.ofReal p := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
    exact suWeakMap_compact_cutoff isOpen_ball hp
      (((EuclideanSpace.proj a).continuous.comp_continuousOn
        (hu.mono Metric.ball_subset_closedBall)).sub continuousOn_const)
      ((hup.eval_piLp a).sub (memLp_const _)) (fun i => (hV i).eval_piLp a)
      (fun i => suWeakMap_sub_const isOpen_ball
        ((hup.eval_piLp a).locallyIntegrable hp1) (hw i a) (u center a))
      hchi hchic hchiO

end PoincareConjecture.M60
