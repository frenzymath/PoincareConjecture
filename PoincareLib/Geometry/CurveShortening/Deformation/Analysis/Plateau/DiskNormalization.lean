import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-!
# Genuine disk automorphisms for the three-point condition

Conjugating a positive real affine half-plane map by the Cayley map
gives a rational disk automorphism with no pole on the closed disk.
The canceled formula is used also at the boundary point 1. These are
the actual reparametrizations in Morrey's boundary normalization,
ICM pp. 181-182, for MT Lemma 19.2, pp. 437-439. See M65 derivation 28.
-/

set_option autoImplicit false

open Set Metric
open scoped Topology ContDiff

namespace Complex

/-- Numerator of the pole-free Cayley-affine disk transformation;
Morrey's three-point normalization, ICM pp. 181-182, derivation 28. -/
def plateauDiskNumerator (b c : ℝ) (z : ℂ) : ℂ :=
  (z + 1) - c * (1 - z) + I * b * (1 - z)

/-- Denominator of the actual Cayley-affine disk transformation;
it will be proved nonzero on the closed disk when c is positive.
Morrey ICM pp. 181-182, derivation 28. -/
def plateauDiskDenominator (b c : ℝ) (z : ℂ) : ℂ :=
  (z + 1) + c * (1 - z) + I * b * (1 - z)

/-- The canceled Cayley-affine transformation. Its value at 1 is the
actual continuous extension, not the totalized Cayley pole value.
Morrey ICM pp. 181-182, derivation 28. -/
noncomputable def plateauDiskMap (b c : ℝ) (z : ℂ) : ℂ :=
  plateauDiskNumerator b c z / plateauDiskDenominator b c z

/-- The exact norm identity locating the image of the disk, needed for
the genuine boundary normalization in Morrey ICM pp. 181-182. -/
theorem plateauDisk_normSq_difference (b c : ℝ) (z : ℂ) :
    normSq (plateauDiskDenominator b c z) - normSq (plateauDiskNumerator b c z) =
      4 * c * (1 - normSq z) := by
  simp only [plateauDiskDenominator, plateauDiskNumerator, normSq_apply,
    add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im,
    one_re, one_im, I_re, I_im]
  ring

/-- No denominator is zero on the closed disk. In particular the
three-point normalization is genuinely defined at its entire boundary;
Morrey ICM pp. 181-182, derivation 28. -/
theorem plateauDiskDenominator_ne_zero (b : ℝ) {c : ℝ} (hc : 0 < c)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : plateauDiskDenominator b c z ≠ 0 := by
  intro hzero
  have hzsq : normSq z ≤ 1 := by
    rw [normSq_eq_norm_sq]
    exact (sq_le_one_iff_abs_le_one _).mpr (by simpa only [abs_norm] using hz)
  have hdiff := plateauDisk_normSq_difference b c z
  rw [hzero, normSq_zero] at hdiff
  have hn : plateauDiskNumerator b c z = 0 := normSq_eq_zero.mp (by
    nlinarith [normSq_nonneg (plateauDiskNumerator b c z)])
  have hsub : (2 : ℂ) * c * (1 - z) = 0 := by
    calc
      _ = plateauDiskDenominator b c z - plateauDiskNumerator b c z := by
        dsimp only [plateauDiskDenominator, plateauDiskNumerator]
        ring
      _ = 0 := by rw [hzero, hn, sub_self]
  have hz1 : z = 1 := by
    have hcz : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left (mul_ne_zero (by norm_num) hcz))).symm
  simp only [plateauDiskDenominator, hz1, sub_self, mul_zero, add_zero,
    one_add_one_eq_two, OfNat.ofNat_ne_zero] at hzero

/-- The actual transformation preserves the closed disk; this checks
the domain before forming its inverse or changing variables.
Morrey ICM pp. 181-182, derivation 28. -/
theorem plateauDiskMap_norm_le_one (b : ℝ) {c : ℝ} (hc : 0 < c)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖plateauDiskMap b c z‖ ≤ 1 := by
  have hD := plateauDiskDenominator_ne_zero b hc hz
  have hzsq : ‖z‖ ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mpr (by simpa only [abs_norm] using hz)
  have hdiff := plateauDisk_normSq_difference b c z
  simp only [normSq_eq_norm_sq] at hdiff
  have hnorm : ‖plateauDiskNumerator b c z‖ ≤ ‖plateauDiskDenominator b c z‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith)
  rw [plateauDiskMap, norm_div]
  exact (div_le_one (norm_pos_iff.mpr hD)).mpr hnorm

/-- Boundary points remain on the unit circle, including 1. This is
needed for a genuine circle reparameterization, not just a disk map;
Morrey ICM pp. 181-182, derivation 28. -/
theorem plateauDiskMap_norm_eq_one (b : ℝ) {c : ℝ} (hc : 0 < c)
    {z : ℂ} (hz : ‖z‖ = 1) : ‖plateauDiskMap b c z‖ = 1 := by
  have hD := plateauDiskDenominator_ne_zero b hc hz.le
  have hdiff := plateauDisk_normSq_difference b c z
  simp only [normSq_eq_norm_sq, hz, one_pow, sub_self, mul_zero] at hdiff
  have heq : ‖plateauDiskNumerator b c z‖ = ‖plateauDiskDenominator b c z‖ := by
    nlinarith [norm_nonneg (plateauDiskNumerator b c z),
      norm_pos_iff.mpr hD]
  rw [plateauDiskMap, norm_div, heq, div_self (norm_ne_zero_iff.mpr hD)]

/-- Inverse real affine parameters give the genuine inverse disk map.
The nonzero denominators are established on both actual disk points;
Morrey ICM pp. 181-182, derivation 28. -/
theorem plateauDiskMap_left_inverse (b : ℝ) {c : ℝ} (hc : 0 < c)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    plateauDiskMap (-b / c) (1 / c) (plateauDiskMap b c z) = z := by
  have hD := plateauDiskDenominator_ne_zero b hc hz
  have hD' := plateauDiskDenominator_ne_zero (-b / c) (one_div_pos.mpr hc)
    (plateauDiskMap_norm_le_one b hc hz)
  apply (div_eq_iff hD').mpr
  let N := plateauDiskNumerator b c z
  let D := plateauDiskDenominator b c z
  change (N / D + 1) - (↑(1 / c) : ℂ) * (1 - N / D) +
      I * (↑(-b / c) : ℂ) * (1 - N / D) =
    z * ((N / D + 1) + (↑(1 / c) : ℂ) * (1 - N / D) +
      I * (↑(-b / c) : ℂ) * (1 - N / D))
  push_cast
  field_simp [show D ≠ 0 from hD, ofReal_ne_zero.mpr hc.ne']
  dsimp only [N, D, plateauDiskNumerator, plateauDiskDenominator]
  ring

/-- These actual disk reparametrizations are smooth on a neighborhood
of every point of the closed disk, including its boundary. This is the
regularity needed for the area/energy change of variables in Morrey's
normalization, ICM pp. 181-182; M65 derivation 28. -/
theorem plateauDiskMap_contDiffAt (b : ℝ) {c : ℝ} (hc : 0 < c)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : ContDiffAt ℂ ∞ (plateauDiskMap b c) z := by
  have hD := plateauDiskDenominator_ne_zero b hc hz
  unfold plateauDiskMap plateauDiskNumerator plateauDiskDenominator
  fun_prop (disch := exact hD)

/-- A concrete homeomorphism of the full closed disk from a positive
real affine half-plane change, with the actual inverse. This is the
normalizing map used in Morrey ICM pp. 181-182; M65 derivation 28. -/
noncomputable def plateauDiskHomeomorph (b : ℝ) {c : ℝ} (hc : 0 < c) :
    closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 where
  toFun z := ⟨plateauDiskMap b c z, by
    simpa only [mem_closedBall, dist_zero_right] using
      plateauDiskMap_norm_le_one b hc
        (by simpa only [mem_closedBall, dist_zero_right] using z.property)⟩
  invFun z := ⟨plateauDiskMap (-b / c) (1 / c) z, by
    simpa only [mem_closedBall, dist_zero_right] using
      plateauDiskMap_norm_le_one (-b / c) (one_div_pos.mpr hc)
        (by simpa only [mem_closedBall, dist_zero_right] using z.property)⟩
  left_inv z := Subtype.ext (plateauDiskMap_left_inverse b hc
    (by simpa only [mem_closedBall, dist_zero_right] using z.property))
  right_inv z := by
    apply Subtype.ext
    have h := plateauDiskMap_left_inverse (-b / c) (one_div_pos.mpr hc)
      (z := (z : ℂ)) (by simpa only [mem_closedBall, dist_zero_right] using z.property)
    have hb : -(-b / c) / (1 / c) = b := by field_simp
    simpa only [hb, one_div_one_div] using h
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((plateauDiskMap_contDiffAt b hc
      (by simpa only [mem_closedBall, dist_zero_right] using z.property)).continuousAt.comp
      continuousAt_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((plateauDiskMap_contDiffAt (-b / c) (one_div_pos.mpr hc)
      (by simpa only [mem_closedBall, dist_zero_right] using z.property)).continuousAt.comp
      continuousAt_subtype_val)

end Complex
