import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryPhaseCircleColumns









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Proofs.M58



theorem m64WeakPhase_circle_current
    {O : Set LoopPlane} (hO : IsOpen O)
    {u : LoopPlane → ℝ} {V : Fin 2 → LoopPlane → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i, HasWeakPartialDeriv i (V i) u O)
    (q : LoopPlane → LoopPlane) (Z : Fin 2 → LoopPlane → LoopPlane)
    (hZ : ∀ i, MemLp (Z i) 2 (volume.restrict O))
    (hq : ∀ i j, HasWeakPartialDeriv i (fun p => Z i p j) (fun p => q p j) O)
    (k : ℝ) (hphase : q =ᵐ[volume.restrict O] fun p => angularPoint (k * u p)) :
    ∀ i, ∀ᵐ p ∂volume.restrict O,
      M64.planarCircleCurrent (q p) (Z i p) = k * V i p := by
  let C := fun x : ℝ => Real.cos (k * x)
  let S := fun x : ℝ => Real.sin (k * x)
  have hC : ContDiff ℝ 1 C := Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
  have hS : ContDiff ℝ 1 S := Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have hdC (x : ℝ) : deriv C x = -Real.sin (k * x) * k := by
    simpa only [C, mul_one, id_eq] using ((hasDerivAt_id x).const_mul k).cos.deriv
  have hdS (x : ℝ) : deriv S x = Real.cos (k * x) * k := by
    simpa only [S, mul_one, id_eq] using ((hasDerivAt_id x).const_mul k).sin.deriv
  have hK : 0 < |k| + 1 := by positivity
  have hbC (x : ℝ) : |deriv C x| ≤ |k| + 1 := by
    rw [hdC, abs_mul, abs_neg]
    have h := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (k * x)) (abs_nonneg k)
    linarith
  have hbS (x : ℝ) : |deriv S x| ≤ |k| + 1 := by
    rw [hdS, abs_mul]
    have h := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one (k * x)) (abs_nonneg k)
    linarith
  have hqC : (fun p => q p 0) =ᵐ[volume.restrict O] fun p => C (u p) := by
    filter_upwards [hphase] with p hp
    rw [hp]
    rfl
  have hqS : (fun p => q p 1) =ᵐ[volume.restrict O] fun p => S (u p) := by
    filter_upwards [hphase] with p hp
    rw [hp]
    rfl
  intro i
  have hcolC := m64WeakPhase_scalar_C1_column hO hu hV hw hC hK hbC
    ((hZ i).eval_piLp 0) (m64WeakPartialDeriv_ae_congr hqC EventuallyEq.rfl (hq i 0))
  have hcolS := m64WeakPhase_scalar_C1_column hO hu hV hw hS hK hbS
    ((hZ i).eval_piLp 1) (m64WeakPartialDeriv_ae_congr hqS EventuallyEq.rfl (hq i 1))
  filter_upwards [hcolC, hcolS, hphase] with p hpC hpS hp
  unfold M64.planarCircleCurrent
  rw [hpC, hpS, hdC, hdS, hp]
  simp only [angularPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    _ = k * V i p * (Real.sin (k * u p) ^ 2 + Real.cos (k * u p) ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]

end PoincareConjecture
