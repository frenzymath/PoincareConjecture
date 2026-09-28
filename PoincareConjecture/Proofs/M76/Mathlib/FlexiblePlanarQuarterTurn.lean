import PoincareConjecture.Proofs.M76.Mathlib.PLFiberCompression
import PoincareConjecture.Proofs.M76.Mathlib.SupportedPlanarQuarterTurn

set_option autoImplicit false

open Set Geometry

namespace PLFiberCompression

noncomputable def scalarHomeomorph (delta w : ℝ) (hd : 0 < delta) (hw : 0 ≤ w) :
    ℝ ≃ₜ ℝ where
  toFun := value delta w
  invFun := value delta⁻¹ w
  left_inv := inverse_value hd hw
  right_inv t := by simpa only [inv_inv] using inverse_value (inv_pos.mpr hd) hw t
  continuous_toFun := (continuous_value delta).comp (continuous_const.prodMk continuous_id)
  continuous_invFun := (continuous_value delta⁻¹).comp (continuous_const.prodMk continuous_id)

end PLFiberCompression

namespace SupportedPlanarShear

theorem exists_quarterTurn_homeomorph_of_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
      F.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ) ∧
      (∀ z, ‖z‖ ≤ a → F z = (-z.2, z.1)) ∧
      ∀ z, b ≤ ‖z‖ → F z = z := by
  let delta := (b - a) / (3 * a)
  have hd : 0 < delta := div_pos (sub_pos.mpr hab) (mul_pos (by norm_num) ha)
  let r := PLFiberCompression.scalarHomeomorph delta a hd ha.le
  let R := r.prodCongr r
  have hRval (z : ℝ × ℝ) : R z =
      (PLFiberCompression.value delta a z.1, PLFiberCompression.value delta a z.2) := rfl
  have hRPL : R.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
    have hw := locallyPiecewiseAffineOn_affine
      (ContinuousAffineMap.const ℝ (ℝ × ℝ) a) isOpen_univ
    have hx := locallyPiecewiseAffineOn_affine
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap isOpen_univ
    have hy := locallyPiecewiseAffineOn_affine
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap isOpen_univ
    apply (mem_piecewiseAffineGroupoid_iff_forward R.toOpenPartialHomeomorph).mpr
    exact (PLFiberCompression.locallyPiecewiseAffineOn_value delta hw hx).prod_mk
      (PLFiberCompression.locallyPiecewiseAffineOn_value delta hw hy)
  have hRcore (z : ℝ × ℝ) (hz : ‖z‖ ≤ a) : R z = z := by
    have hx : |z.1| ≤ a := (norm_fst_le z).trans hz
    have hy : |z.2| ≤ a := (norm_snd_le z).trans hz
    rw [hRval, PLFiberCompression.value_of_mem (abs_le.mp hx),
      PLFiberCompression.value_of_mem (abs_le.mp hy)]
  have hRinvcore (z : ℝ × ℝ) (hz : ‖z‖ ≤ a) : R.symm z = z := by
    calc
      R.symm z = R.symm (R z) := congrArg R.symm (hRcore z hz).symm
      _ = z := R.symm_apply_apply z
  have hhi : PLFiberCompression.value delta a (4 * a) = b := by
    rw [PLFiberCompression.value_of_width_le ha.le (by linarith)]
    dsimp only [delta]
    field_simp
    ring
  have hlo : PLFiberCompression.value delta a (-(4 * a)) = -b := by
    rw [PLFiberCompression.value_of_le_neg ha.le (by linarith)]
    dsimp only [delta]
    field_simp
    ring
  have hmono := PLFiberCompression.strictMono_value hd ha.le
  have hrange (t : ℝ) (ht : |t| < 4 * a) :
      |PLFiberCompression.value delta a t| < b := by
    apply abs_lt.mpr
    constructor
    · rw [← hlo]
      exact hmono (abs_lt.mp ht).1
    · rw [← hhi]
      exact hmono (abs_lt.mp ht).2
  have hRexterior (z : ℝ × ℝ) (hz : b ≤ ‖z‖) : 4 * a ≤ ‖R.symm z‖ := by
    by_contra hn
    have hp : ‖R.symm z‖ < 4 * a := lt_of_not_ge hn
    have hx := hrange (R.symm z).1 (lt_of_le_of_lt (norm_fst_le (R.symm z)) hp)
    have hy := hrange (R.symm z).2 (lt_of_le_of_lt (norm_snd_le (R.symm z)) hp)
    have hnorm : ‖R (R.symm z)‖ < b := by
      rw [hRval, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_lt hx hy
    rw [R.apply_symm_apply] at hnorm
    exact (not_lt_of_ge hz) hnorm
  obtain ⟨H, hHPL, hHcore, hHfix⟩ := exists_quarterTurn_homeomorph ha
  let F := R.symm.trans (H.trans R)
  refine ⟨F, ?_, ?_, ?_⟩
  · dsimp only [F]
    rw [Homeomorph.trans_toOpenPartialHomeomorph, Homeomorph.trans_toOpenPartialHomeomorph]
    exact (piecewiseAffineGroupoid (ℝ × ℝ)).trans
      ((piecewiseAffineGroupoid (ℝ × ℝ)).symm hRPL)
      ((piecewiseAffineGroupoid (ℝ × ℝ)).trans hHPL hRPL)
  · intro z hz
    change R (H (R.symm z)) = (-z.2, z.1)
    rw [hRinvcore z hz, hHcore z hz]
    apply hRcore
    simpa only [Prod.norm_def, norm_neg, max_comm] using hz
  · intro z hz
    change R (H (R.symm z)) = z
    rw [hHfix (R.symm z) (hRexterior z hz), R.apply_symm_apply]

end SupportedPlanarShear
