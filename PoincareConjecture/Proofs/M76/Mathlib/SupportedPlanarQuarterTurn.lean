import PoincareConjecture.Proofs.M76.Mathlib.SupportedPlanarShear












set_option autoImplicit false

open Set Geometry

namespace SupportedPlanarShear




theorem exists_vertical_shear_homeomorph (R c : ℝ) (hc : |c| < 1) :
    ∃ V : (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
      V.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ) ∧
      (∀ z, R ≤ ‖z‖ → V z = z) ∧
      ∀ z, 2 * ‖z‖ ≤ R → V z = (z.1, z.2 + c * z.1) := by
  obtain ⟨H, hHPL, _, hHfix, hHcore⟩ := exists_shear_homeomorph R c hc
  let S := Homeomorph.prodComm ℝ ℝ
  have hSPL : S.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
    apply (mem_piecewiseAffineGroupoid_iff_forward S.toOpenPartialHomeomorph).mpr
    exact locallyPiecewiseAffineOn_affine
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap.toContinuousAffineMap
      isOpen_univ
  let V := S.trans (H.trans S)
  have hval (z : ℝ × ℝ) : V z = (H z.swap).swap := rfl
  refine ⟨V, ?_, ?_, ?_⟩
  · dsimp only [V]
    rw [Homeomorph.trans_toOpenPartialHomeomorph, Homeomorph.trans_toOpenPartialHomeomorph]
    exact (piecewiseAffineGroupoid (ℝ × ℝ)).trans hSPL
      ((piecewiseAffineGroupoid (ℝ × ℝ)).trans hHPL hSPL)
  · intro z hz
    have hz' : R ≤ ‖z.swap‖ := by simpa [Prod.norm_def, max_comm] using hz
    rw [hval, hHfix z.swap hz', Prod.swap_swap]
  · intro z hz
    have hz' : 2 * ‖z.swap‖ ≤ R := by simpa [Prod.norm_def, max_comm] using hz
    rw [hval, hHcore z.swap hz']
    rfl





theorem exists_quarterTurn_homeomorph {a : ℝ} (ha : 0 < a) :
    ∃ F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
      F.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ) ∧
      (∀ z, ‖z‖ ≤ a → F z = (-z.2, z.1)) ∧
      ∀ z, 4 * a ≤ ‖z‖ → F z = z := by
  obtain ⟨H, hHPL, _, hHfix, hHcore⟩ :=
    exists_shear_homeomorph (4 * a) (-1 / 2) (by norm_num)
  obtain ⟨V, hVPL, hVfix, hVcore⟩ :=
    exists_vertical_shear_homeomorph (4 * a) (1 / 2) (by norm_num)
  let A := H.trans H
  let B := V.trans V
  let F := A.trans (B.trans A)
  have htrans (G₁ G₂ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ))
      (h₁ : G₁.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ))
      (h₂ : G₂.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ)) :
      (G₁.trans G₂).toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
    rw [Homeomorph.trans_toOpenPartialHomeomorph]
    exact (piecewiseAffineGroupoid (ℝ × ℝ)).trans h₁ h₂
  have hA : A.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ) :=
    htrans H H hHPL hHPL
  have hB : B.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ) :=
    htrans V V hVPL hVPL
  have hHlin (x y : ℝ) (h : ‖(x, y)‖ ≤ 2 * a) :
      H (x, y) = (x - y / 2, y) := by
    rw [hHcore (x, y) (by linarith)]
    congr 1
    ring
  have hVlin (x y : ℝ) (h : ‖(x, y)‖ ≤ 2 * a) :
      V (x, y) = (x, y + x / 2) := by
    rw [hVcore (x, y) (by linarith)]
    congr 1
    ring
  refine ⟨F, htrans A (B.trans A) hA (htrans B A hB hA), ?_, ?_⟩
  · rintro ⟨x, y⟩ hz
    have hx : -a ≤ x ∧ x ≤ a := abs_le.mp ((norm_fst_le (x, y)).trans hz)
    have hy : -a ≤ y ∧ y ≤ a := abs_le.mp ((norm_snd_le (x, y)).trans hz)
    have h₀ : ‖(x, y)‖ ≤ 2 * a := by linarith
    have h₁ : ‖(x - y / 2, y)‖ ≤ 2 * a := by
      simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
      constructor <;> constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have h₂ : ‖(x - y, y)‖ ≤ 2 * a := by
      simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
      constructor <;> constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have h₃ : ‖(x - y, y + (x - y) / 2)‖ ≤ 2 * a := by
      simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
      constructor <;> constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have h₄ : ‖(x - y, x)‖ ≤ 2 * a := by
      simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
      constructor <;> constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have h₅ : ‖(x - y - x / 2, x)‖ ≤ 2 * a := by
      simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
      constructor <;> constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hstep₁ : H (H (x, y)) = (x - y, y) := by
      rw [hHlin x y h₀, hHlin (x - y / 2) y h₁]
      congr 1
      ring
    have hstep₂ : V (V (x - y, y)) = (x - y, x) := by
      rw [hVlin (x - y) y h₂, hVlin (x - y) (y + (x - y) / 2) h₃]
      congr 1
      ring
    have hstep₃ : H (H (x - y, x)) = (-y, x) := by
      rw [hHlin (x - y) x h₄, hHlin (x - y - x / 2) x h₅]
      congr 1
      ring
    change H (H (V (V (H (H (x, y)))))) = (-y, x)
    rw [hstep₁, hstep₂, hstep₃]
  · intro z hz
    change H (H (V (V (H (H z))))) = z
    simp only [hHfix z hz, hVfix z hz]

end SupportedPlanarShear
