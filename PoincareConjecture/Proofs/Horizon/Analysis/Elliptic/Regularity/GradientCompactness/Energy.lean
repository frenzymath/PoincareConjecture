import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.FluxBound

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal BigOperators
open Poincare.Analysis.Sobolev.Weak

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integral_partial_sq_le_flux_energy
    {O : Set E} (hO : IsOpen O) [IsFiniteMeasure (volume.restrict O)]
    {F G : Fin d → E → ℝ} {u v φ : E → ℝ}
    {A B : E → Fin d → Fin d → ℝ} {L : ℝ≥0} {c δ : ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict O))
    (hG : ∀ i, MemLp (G i) 2 (volume.restrict O))
    (hu : LipschitzOnWith L u O) (hv : LipschitzOnWith L v O)
    (hp : MemLp φ ∞ (volume.restrict O))
    (hp0 : ∀ x ∈ O, 0 ≤ φ x) (hp1 : ∀ x ∈ O, φ x ≤ 1)
    (hδ : 0 ≤ δ)
    (hcoeff : ∀ x ∈ O, ∀ i j, |A x i j - B x i j| ≤ δ)
    (hell : ∀ x ∈ O, ∀ w : Fin d → ℝ,
      c * ∑ i, (w i) ^ 2 ≤ ∑ i, ∑ j, A x i j * w j * w i)
    (hFid : ∀ x ∈ O, ∀ i, F i x =
      -(∑ j, A x i j * fderiv ℝ u x (EuclideanSpace.single j 1)))
    (hGid : ∀ x ∈ O, ∀ i, G i x =
      -(∑ j, B x i j * fderiv ℝ v x (EuclideanSpace.single j 1))) :
    c * (∫ x in O, φ x * ∑ i,
      (fderiv ℝ u x (EuclideanSpace.single i 1) -
        fderiv ℝ v x (EuclideanSpace.single i 1)) ^ 2) ≤
      (∫ x in O, φ x * ∑ i, (G i x - F i x) *
        (fderiv ℝ u x (EuclideanSpace.single i 1) -
          fderiv ℝ v x (EuclideanSpace.single i 1))) +
      (d : ℝ) ^ 2 * δ * (2 * (L : ℝ) ^ 2) * volume.real O := by
  let du := fun i x => fderiv ℝ u x (EuclideanSpace.single i 1)
  let dv := fun i x => fderiv ℝ v x (EuclideanSpace.single i 1)
  let q := fun x => φ x * ∑ i, (du i x - dv i x) ^ 2
  let energy := fun x => φ x * ∑ i, (G i x - F i x) * (du i x - dv i x)
  let error := (d : ℝ) ^ 2 * δ * (2 * (L : ℝ) ^ 2)
  have hd (i) : MemLp (fun x => du i x - dv i x) ∞ (volume.restrict O) :=
    (memLp_top_fderiv_apply_of_lipschitzOn hO hu _).sub
      (memLp_top_fderiv_apply_of_lipschitzOn hO hv _)
  have hq : MemLp q ∞ (volume.restrict O) := by
    have hsum : MemLp (fun x => ∑ i, (du i x - dv i x) ^ 2)
        ∞ (volume.restrict O) := by
      apply memLp_finsetSum
      intro i _
      simpa only [pow_two] using (hd i).mul' (r := ∞) (hd i)
    exact hsum.mul' hp
  have he : MemLp energy 2 (volume.restrict O) := by
    have hsum : MemLp (fun x => ∑ i, (G i x - F i x) * (du i x - dv i x))
        2 (volume.restrict O) := by
      apply memLp_finsetSum
      intro i _
      exact (hd i).mul' ((hG i).sub (hF i))
    exact hsum.mul' hp
  have herror : 0 ≤ error := by dsimp only [error]; positivity
  have hpoint (x) (hx : x ∈ O) : c * q x ≤ energy x + error := by
    have h := matrix_flux_coercivity L.coe_nonneg hδ (hell x hx)
      (fun i => abs_partial_le_of_lipschitzOn hO hu hx i)
      (fun i => abs_partial_le_of_lipschitzOn hO hv hx i) (hcoeff x hx)
    have hid : (∑ i, ((∑ j, A x i j * du j x) - ∑ j, B x i j * dv j x) *
        (du i x - dv i x)) = ∑ i, (G i x - F i x) * (du i x - dv i x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hFid x hx i, hGid x hx i, neg_sub_neg]
    change c * (∑ i, (du i x - dv i x) ^ 2) ≤ _ + error at h
    rw [hid] at h
    have hmul := mul_le_mul_of_nonneg_left h (hp0 x hx)
    have he' : φ x * error ≤ error := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hp1 x hx) herror
    dsimp only [q, energy]
    nlinarith
  have h := setIntegral_mono_on ((hq.const_mul c).integrable le_top)
    ((he.integrable (by norm_num)).add (integrable_const error)) hO.measurableSet hpoint
  change c * (∫ x in O, q x) ≤ (∫ x in O, energy x) + error * volume.real O
  simpa only [Pi.add_apply, integral_const_mul, integral_add (he.integrable (by norm_num))
    (integrable_const error), integral_const, smul_eq_mul,
    measureReal_restrict_apply_univ, mul_comm (volume.real O) error] using h

end Poincare.Analysis.Elliptic
