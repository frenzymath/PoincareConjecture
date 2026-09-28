import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.Profile
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev Plane (v : E3) := Hemisphere.Plane v

private def quadraticEndWeight (u : Real) : Real :=
  Real.smoothTransition (4 * u - 1) * (1 - Real.smoothTransition (2 * u - 2))

private theorem quadraticEndWeight_nonneg (u : Real) : 0 ≤ quadraticEndWeight u :=
  mul_nonneg (Real.smoothTransition.nonneg _)
    (sub_nonneg.mpr (Real.smoothTransition.le_one _))

private theorem quadraticEndWeight_le_one (u : Real) : quadraticEndWeight u ≤ 1 := by
  calc
    _ ≤ 1 * (1 - Real.smoothTransition (2 * u - 2)) :=
      mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
        (sub_nonneg.mpr (Real.smoothTransition.le_one _))
    _ ≤ 1 := by linarith [Real.smoothTransition.nonneg (2 * u - 2)]

private theorem quadraticEndWeight_zero_low {u : Real} (hu : u ≤ 1 / 4) :
    quadraticEndWeight u = 0 := by
  simp [quadraticEndWeight, Real.smoothTransition.zero_of_nonpos (by linarith : 4 * u - 1 ≤ 0)]

private theorem quadraticEndWeight_zero_high {u : Real} (hu : 3 / 2 ≤ u) :
    quadraticEndWeight u = 0 := by
  simp [quadraticEndWeight, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * u - 2)]

private theorem quadraticEndWeight_one {u : Real} (hu : u ∈ Icc (1 / 2) 1) :
    quadraticEndWeight u = 1 := by
  simp [quadraticEndWeight,
    Real.smoothTransition.one_of_one_le (by linarith [hu.1] : 1 ≤ 4 * u - 1),
    Real.smoothTransition.zero_of_nonpos (by linarith [hu.2] : 2 * u - 2 ≤ 0)]

private def quadraticEndBase (u : Real) : Real :=
  (1 - quadraticEndWeight u) + quadraticEndWeight u * u

private theorem quadraticEndBase_pos (u : Real) : 0 < quadraticEndBase u := by
  by_cases hu : u ≤ 1 / 4
  · simp [quadraticEndBase, quadraticEndWeight_zero_low hu]
  have hw0 := quadraticEndWeight_nonneg u
  have hw1 := quadraticEndWeight_le_one u
  have hmul := mul_nonneg hw0 (show 0 ≤ u - 1 / 4 by linarith)
  dsimp only [quadraticEndBase]
  nlinarith

private theorem contDiff_quadraticEndBase : ContDiff Real ∞ quadraticEndBase := by
  have hw : ContDiff Real ∞ quadraticEndWeight :=
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
      (contDiff_const.sub (Real.smoothTransition.contDiff.comp
        ((contDiff_const.mul contDiff_id).sub contDiff_const)))
  exact (contDiff_const.sub hw).add (hw.mul contDiff_id)

private def heightDilation {v : E3} (hv : ‖v‖ = 1)
    (k : Real → Real) (hk : ContDiff Real ∞ k) (hkpos : ∀ t, 0 < k t) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := by
  let P : Diffeomorph 𝓘(Real, Real × Plane v) 𝓘(Real, Real × Plane v)
      (Real × Plane v) (Real × Plane v) ∞ := {
    toEquiv := {
      toFun := fun z => (z.1, k z.1 • z.2)
      invFun := fun z => (z.1, (k z.1)⁻¹ • z.2)
      left_inv := by intro z; simp [smul_smul, (hkpos z.1).ne']
      right_inv := by intro z; simp [smul_smul, (hkpos z.1).ne'] }
    contMDiff_toFun :=
      (contDiff_fst.prodMk ((hk.comp contDiff_fst).smul contDiff_snd)).contMDiff
    contMDiff_invFun :=
      (contDiff_fst.prodMk (((hk.inv (fun t => (hkpos t).ne')).comp contDiff_fst).smul
        contDiff_snd)).contMDiff }
  let H := (Poincare.Geometry.Euclidean.heightCoordinates hv).toDiffeomorph
  exact (H.symm.trans P).trans H

private theorem heightDilation_apply {v : E3} (hv : ‖v‖ = 1)
    (k : Real → Real) (hk : ContDiff Real ∞ k) (hkpos : ∀ t, 0 < k t)
    (t : Real) (x : Plane v) :
    heightDilation hv k hk hkpos (t • v + (x : E3)) =
      t • v + (k t • x : Plane v) := by
  let H := (Poincare.Geometry.Euclidean.heightCoordinates hv).toDiffeomorph
  change H ((H.symm (H (t, x))).1, k (H.symm (H (t, x))).1 • (H.symm (H (t, x))).2) = _
  rw [H.symm_apply_apply]
  rfl

theorem exists_quadratic_minimum_cylindrical_end_with_profile {v : E3} (hv : ‖v‖ = 1)
    (c : Real) {r : Real} (hr : 0 < r) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, inner Real v (D y) = inner Real v y) ∧
      (∀ y, inner Real v y ≤ c + r ^ 2 / 4 → D y = y) ∧
      (∀ y, c + 3 * r ^ 2 / 2 ≤ inner Real v y → D y = y) ∧
      (∀ x : Plane v, ‖x‖ ≤ r →
        D ((x : E3) + (c + ‖x‖ ^ 2) • v) =
          ((Real.sqrt (minimumCapDenominator (‖x‖ ^ 2 / r ^ 2)))⁻¹ • x : Plane v) +
            (c + ‖x‖ ^ 2) • v) ∧
      ∀ (q : Plane v) (ρ : Real), ‖q‖ = 1 → 0 < ρ →
        r ^ 2 / 2 ≤ ρ ^ 2 → ρ ^ 2 ≤ r ^ 2 →
        D ((ρ • q : Plane v) + (c + ρ ^ 2) • v) =
          (r • q : Plane v) + (c + ρ ^ 2) • v := by
  let u : Real → Real := fun t => (t - c) / r ^ 2
  let k : Real → Real := fun t => (Real.sqrt (quadraticEndBase (u t)))⁻¹
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hu : ContDiff Real ∞ u := (contDiff_id.sub contDiff_const).div_const _
  have hbase : ContDiff Real ∞ (fun t => quadraticEndBase (u t)) :=
    contDiff_quadraticEndBase.comp hu
  have hk : ContDiff Real ∞ k := by
    apply ContDiff.inv _ (fun t => (Real.sqrt_pos.mpr (quadraticEndBase_pos _)).ne')
    exact hbase.sqrt (fun t => (quadraticEndBase_pos _).ne')
  have hkpos (t : Real) : 0 < k t :=
    inv_pos.mpr (Real.sqrt_pos.mpr (quadraticEndBase_pos _))
  let D := heightDilation hv k hk hkpos
  have hcoord (t : Real) (x : Plane v) :
      D (t • v + (x : E3)) = t • v + (k t • x : Plane v) :=
    heightDilation_apply hv k hk hkpos t x
  have hdecomp (y : E3) :
      inner Real v y • v + ((Plane v).orthogonalProjectionOnto y : E3) = y :=
    (Poincare.Geometry.Euclidean.heightCoordinates hv).apply_symm_apply y
  have hfix (y : E3) (hkone : k (inner Real v y) = 1) : D y = y := by
    nth_rw 1 [← hdecomp y]
    rw [hcoord, hkone, one_smul, hdecomp]
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    nth_rw 1 [← hdecomp y]
    rw [hcoord]
    exact Poincare.Geometry.Euclidean.inner_heightCoordinates hv
      (inner Real v y, k (inner Real v y) • (Plane v).orthogonalProjectionOnto y)
  · intro y hy
    apply hfix
    have hlu : u (inner Real v y) ≤ 1 / 4 := (div_le_iff₀ hr2).mpr (by linarith)
    simp [k, quadraticEndBase, quadraticEndWeight_zero_low hlu]
  · intro y hy
    apply hfix
    have hlu : 3 / 2 ≤ u (inner Real v y) := (le_div_iff₀ hr2).mpr (by linarith)
    simp [k, quadraticEndBase, quadraticEndWeight_zero_high hlu]
  · intro x hx
    have hxu : ‖x‖ ^ 2 / r ^ 2 ≤ 1 := by
      apply (div_le_iff₀ hr2).mpr
      simpa only [one_mul] using (sq_le_sq₀ (norm_nonneg x) hr.le).mpr hx
    have hweight : quadraticEndWeight (‖x‖ ^ 2 / r ^ 2) =
        minimumCapWeight (‖x‖ ^ 2 / r ^ 2) := by
      rw [quadraticEndWeight,
        Real.smoothTransition.zero_of_nonpos (by linarith : 2 * (‖x‖ ^ 2 / r ^ 2) - 2 ≤ 0)]
      simp [minimumCapWeight]
    have hkx : k (c + ‖x‖ ^ 2) =
        (Real.sqrt (minimumCapDenominator (‖x‖ ^ 2 / r ^ 2)))⁻¹ := by
      simp only [k, u, add_sub_cancel_left, quadraticEndBase, hweight, minimumCapDenominator]
    rw [add_comm, hcoord, hkx, add_comm]
  · intro q ρ _ hρ hρlo hρhi
    have huρ : u (c + ρ ^ 2) ∈ Icc (1 / 2) 1 := by
      dsimp [u]
      constructor
      · apply (le_div_iff₀ hr2).mpr
        linarith
      · apply (div_le_iff₀ hr2).mpr
        linarith
    have hbaseρ : quadraticEndBase (u (c + ρ ^ 2)) = ρ ^ 2 / r ^ 2 := by
      rw [quadraticEndBase, quadraticEndWeight_one huρ]
      simp [u]
    have hsqrt : Real.sqrt (quadraticEndBase (u (c + ρ ^ 2))) = ρ / r := by
      rw [hbaseρ, Real.sqrt_div (sq_nonneg ρ), Real.sqrt_sq hρ.le, Real.sqrt_sq hr.le]
    have hkr : k (c + ρ ^ 2) * ρ = r := by
      dsimp only [k]
      rw [hsqrt]
      field_simp
    rw [add_comm, hcoord, smul_smul, hkr, add_comm]

theorem exists_quadratic_minimum_cylindrical_end {v : E3} (hv : ‖v‖ = 1)
    (c : Real) {r : Real} (hr : 0 < r) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, inner Real v (D y) = inner Real v y) ∧
      (∀ y, inner Real v y ≤ c + r ^ 2 / 4 → D y = y) ∧
      (∀ y, c + 3 * r ^ 2 / 2 ≤ inner Real v y → D y = y) ∧
      ∀ (q : Plane v) (ρ : Real), ‖q‖ = 1 → 0 < ρ →
        r ^ 2 / 2 ≤ ρ ^ 2 → ρ ^ 2 ≤ r ^ 2 →
        D ((ρ • q : Plane v) + (c + ρ ^ 2) • v) =
          (r • q : Plane v) + (c + ρ ^ 2) • v := by
  obtain ⟨D, hheight, hlow, hhigh, _, hcylinder⟩ :=
    exists_quadratic_minimum_cylindrical_end_with_profile hv c hr
  exact ⟨D, hheight, hlow, hhigh, hcylinder⟩

end Poincare.Manifold.Schoenflies
