import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityWeakTests
import PoincareConjecture.Proofs.M03.Existence.DeTurckHigherDomainNative

set_option autoImplicit false

open MeasureTheory Set Filter Metric
open scoped Topology SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture.M65Boundary

open EuclideanTranslationNative EuclideanDerivativeNative DeTurckDomainRegularityNative
  DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem multiplier_product (a b : 𝓢(E, ℝ)) (u : ScalarL2 2) :
    schwartzMultiplier (schwartzProduct a b) u =
      schwartzMultiplier a (schwartzMultiplier b u) := by
  apply Lp.ext
  filter_upwards [schwartzMultiplier_coe (schwartzProduct a b) u,
    schwartzMultiplier_coe a (schwartzMultiplier b u), schwartzMultiplier_coe b u]
    with z hleft hright hb
  rw [hleft, hright, hb, schwartzProduct_apply, mul_assoc]

private theorem multiplier_derivative_square (a : 𝓢(E, ℝ)) (u : ScalarL2 2) (v : E) :
    schwartzMultiplier (∂_{v} (schwartzProduct a a)) u =
      (2 : ℝ) • schwartzMultiplier a (schwartzMultiplier (∂_{v} a) u) := by
  apply Lp.ext
  filter_upwards [schwartzMultiplier_coe (∂_{v} (schwartzProduct a a)) u,
    Lp.coeFn_smul (2 : ℝ) (schwartzMultiplier a (schwartzMultiplier (∂_{v} a) u)),
    schwartzMultiplier_coe a (schwartzMultiplier (∂_{v} a) u),
    schwartzMultiplier_coe (∂_{v} a) u] with z hl hr ha hd
  rw [hl, hr, Pi.smul_apply, smul_eq_mul, ha, hd, lineDeriv_schwartzProduct]
  simp only [add_apply, schwartzProduct_apply]
  ring

private theorem weighted_value_bound (a : 𝓢(E, ℝ)) (u : ScalarL2 2) {B : ℝ}
    (hb : ∀ᵐ z ∂volume, ‖u z‖ ≤ B) :
    ∀ᵐ z ∂volume, ‖a z * u z‖ ≤ SchwartzMap.seminorm ℝ 0 0 a * B := by
  filter_upwards [hb] with z hz
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (a.norm_le_seminorm ℝ z) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hz (apply_nonneg _ _))

theorem weighted_energy_identity (u : ScalarL2 2) (d : Fin 2 → ScalarL2 2)
    (f : E → ℝ) (hf : Integrable f volume) {U : Set E} (hU : IsOpen U)
    (hweak : ∀ i (φ : 𝓢(E, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ φ : 𝓢(E, ℝ), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f z * φ z))
    {B : ℝ} (hbound : ∀ᵐ z ∂volume, ‖u z‖ ≤ B)
    (η : 𝓢(E, ℝ)) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    (∑ i : Fin 2, ‖schwartzMultiplier η (d i)‖ ^ 2) +
      2 * (∑ i : Fin 2, ⟪schwartzMultiplier η (d i),
        schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} η) u⟫_ℝ) =
      -(∫ z, η z ^ 2 * (f z * u z)) := by
  let a := schwartzProduct η η
  let w := schwartzMultiplier a u
  let dw (i : Fin 2) := schwartzMultiplier a (d i) +
    schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} a) u
  have hw : ∀ᵐ z ∂volume, ‖w z‖ ≤ SchwartzMap.seminorm ℝ 0 0 a * B := by
    filter_upwards [schwartzMultiplier_coe a u, weighted_value_bound a u hbound]
      with z hz hb
    simpa only [w, hz] using hb
  have hwK : ∀ᵐ z ∂volume, z ∉ tsupport η → w z = 0 := by
    filter_upwards [schwartzMultiplier_coe a u] with z hz
    intro hnot
    rw [hz]
    change (η z * η z) * u z = 0
    rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul, zero_mul]
  have hdw (i : Fin 2) (φ : 𝓢(E, ℝ)) :
      ⟪dw i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, w z * fderiv ℝ φ z (EuclideanSpace.single i 1)) := by
    have hh := HasWeakSchwartzDerivative.mul u (d i) (EuclideanSpace.single i 1)
      (hasWeakSchwartzDerivative_of_integral u (d i)
        (EuclideanSpace.single i 1) (hweak i)) a φ
    simpa only [inner_schwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hh
  have htest := weak_equation_bounded_test d f hf hU heq w dw hc hs hwK hdw hw
  have hdiag (i : Fin 2) : ⟪d i, schwartzMultiplier a (d i)⟫_ℝ =
      ‖schwartzMultiplier η (d i)‖ ^ 2 := by
    rw [multiplier_product, ← schwartzMultiplier_selfAdjoint, real_inner_self_eq_norm_sq]
  have hcross (i : Fin 2) :
      ⟪d i, schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} a) u⟫_ℝ =
        2 * ⟪schwartzMultiplier η (d i),
          schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} η) u⟫_ℝ := by
    rw [multiplier_derivative_square, real_inner_smul_right,
      ← schwartzMultiplier_selfAdjoint]
  have hforcing : (∫ z, f z * w z) = ∫ z, η z ^ 2 * (f z * u z) := by
    apply integral_congr_ae
    filter_upwards [schwartzMultiplier_coe a u] with z hz
    rw [hz]
    change f z * (η z * η z * u z) = _
    ring
  simpa only [dw, inner_add_right, hdiag, hcross, Finset.sum_add_distrib,
    ← Finset.mul_sum, hforcing] using htest

theorem caccioppoli {N : ℕ} (u : Fin N → ScalarL2 2)
    (d : Fin N → Fin 2 → ScalarL2 2) (f : Fin N → E → ℝ)
    (hf : ∀ j, Integrable (f j) volume) {U : Set E} (hU : IsOpen U)
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
      16 * (∑ j : Fin N, ∑ i : Fin 2,
        ‖schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} η) (u j)‖ ^ 2) := by
  let X (j : Fin N) (i : Fin 2) := schwartzMultiplier η (d j i)
  let Y (j : Fin N) (i : Fin 2) :=
    schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} η) (u j)
  let energy := ∑ j : Fin N, ∑ i : Fin 2, ‖X j i‖ ^ 2
  let error := ∑ j : Fin N, ∑ i : Fin 2, ‖Y j i‖ ^ 2
  let cross := ∑ j : Fin N, ∑ i : Fin 2, ⟪X j i, Y j i⟫_ℝ
  have hfinite (j : Fin N) : Integrable (fun z => η z ^ 2 * (f j z * u j z)) volume := by
    have hb := weighted_value_bound (schwartzProduct η η) (u j) (hbound j)
    have hi := (hf j).mul_bdd
      ((schwartzProduct η η).continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable (u j))) hb
    exact hi.congr (Eventually.of_forall fun z => by
      dsimp only [Pi.mul_apply, schwartzProduct_apply]
      ring)
  have hpairing : Integrable (fun z => η z ^ 2 * (∑ j : Fin N, f j z * u j z)) volume := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun j _ => hfinite j)
  have hident : energy + 2 * cross =
      -(∫ z, η z ^ 2 * (∑ j : Fin N, f j z * u j z)) := by
    have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ =>
      weighted_energy_identity (u j) (d j) (f j) (hf j) hU
        (hweak j) (heq j) (hbound j) η hc hs)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib] at hh
    rw [← integral_finsetSum _ (fun j _ => hfinite j)] at hh
    simpa only [energy, cross, X, Y, Finset.mul_sum] using hh
  have hXint (j : Fin N) (i : Fin 2) :
      Integrable (fun z => η z ^ 2 * (d j i z) ^ 2) volume := by
    apply (Lp.memLp (X j i)).integrable_sq.congr
    filter_upwards [schwartzMultiplier_coe η (d j i)] with z hz
    rw [hz]
    ring
  have henergyInt : Integrable
      (fun z => η z ^ 2 * (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)) volume := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ
      (fun j _ => integrable_finsetSum Finset.univ (fun i _ => hXint j i))
  have henergyEq : (∫ z, η z ^ 2 * (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)) = energy := by
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ (fun j _ =>
      integrable_finsetSum Finset.univ (fun i _ => hXint j i))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum _ (fun i _ => hXint j i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [scalarLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [schwartzMultiplier_coe η (d j i)] with z hz
    rw [hz]
    ring
  have hforcing : -(∫ z, η z ^ 2 * (∑ j : Fin N, f j z * u j z)) ≤ energy / 2 := by
    rw [← integral_neg, ← henergyEq, ← integral_div]
    apply integral_mono_ae hpairing.neg (henergyInt.div_const 2)
    filter_upwards [hsmall] with z hz
    dsimp only [Pi.neg_apply]
    by_cases hzU : z ∈ U
    · have hp := (neg_le_abs (∑ j : Fin N, f j z * u j z)).trans (hz hzU)
      nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg (η z))]
    · have hzη : η z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzU (hs h))
      simp only [hzη, zero_pow (by decide : 2 ≠ 0), zero_mul, neg_zero, zero_div, le_refl]
  have hcross : -2 * cross ≤ energy / 4 + 4 * error := by
    have hpoint (j : Fin N) (i : Fin 2) :
        -2 * ⟪X j i, Y j i⟫_ℝ ≤ ‖X j i‖ ^ 2 / 4 + 4 * ‖Y j i‖ ^ 2 := by
      have hn := sq_nonneg ‖(1 / 2 : ℝ) • X j i + (2 : ℝ) • Y j i‖
      rw [norm_add_sq_real] at hn
      simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left, real_inner_smul_right] at hn
      norm_num at hn
      nlinarith
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint j i))
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_div,
      cross, energy, error] using hh
  change energy ≤ 16 * error
  linarith only [hident, hforcing, hcross]

end PoincareConjecture.M65Boundary
