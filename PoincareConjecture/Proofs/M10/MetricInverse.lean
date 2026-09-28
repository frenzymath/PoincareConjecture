import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt









set_option autoImplicit false

open scoped ContDiff Topology

namespace PoincareConjecture.M10

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [FiniteDimensional ℝ Y]


theorem positive_bilinear_isInvertible (B : Y →L[ℝ] Y →L[ℝ] ℝ)
    (hpos : ∀ v : Y, v ≠ 0 → 0 < B v v) : B.IsInvertible := by
  have hinj : Function.Injective B := by
    intro v w hvw
    apply sub_eq_zero.mp
    by_contra hne
    have hz : B (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have hp := hpos (v - w) hne
    rw [hz] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  have hdim : Module.finrank ℝ Y = Module.finrank ℝ (Y →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ Y).toLinearEquiv.finrank_eq
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := B.toLinearMap) hdim).mp hinj
  exact ⟨(LinearEquiv.ofBijective B.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩


noncomputable def phaseVelocity (B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ)
    (a : ℝ × Y × (Y →L[ℝ] ℝ)) : Y :=
  (2 * Real.sqrt a.1)⁻¹ • (B (a.2.1, a.1)).inverse a.2.2


theorem phaseVelocity_contDiffAt {B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ}
    {a : ℝ × Y × (Y →L[ℝ] ℝ)} {k : ℕ∞ω}
    (hB : ContDiffAt ℝ k B (a.2.1, a.1)) (ht : 0 < a.1)
    (hi : (B (a.2.1, a.1)).IsInvertible) :
    ContDiffAt ℝ k (phaseVelocity B) a := by
  have hcoords : ContDiffAt ℝ k
      (fun b : ℝ × Y × (Y →L[ℝ] ℝ) ↦ (b.2.1, b.1)) a :=
    contDiffAt_snd.fst.prodMk contDiffAt_fst
  have hBinv := hi.contDiffAt_map_inverse.comp a (hB.comp a hcoords)
  exact ((contDiffAt_const.mul (contDiffAt_fst.sqrt ht.ne')).inv
    (mul_ne_zero two_ne_zero (Real.sqrt_pos.mpr ht).ne')).smul
      (hBinv.clm_apply contDiffAt_snd.snd)

omit [FiniteDimensional ℝ Y] in

theorem phaseVelocity_of_momentum (B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ)
    (x : Y) {t : ℝ} (ht : 0 < t) (hi : (B (x, t)).IsInvertible) (v : Y) :
    phaseVelocity B (t, x, (2 * Real.sqrt t) • B (x, t) v) = v := by
  dsimp only [phaseVelocity]
  rw [map_smul, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero two_ne_zero (Real.sqrt_pos.mpr ht).ne'),
    one_smul, hi.inverse_apply_self]

end PoincareConjecture.M10
