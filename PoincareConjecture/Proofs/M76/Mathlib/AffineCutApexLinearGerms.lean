import PoincareConjecture.Proofs.M76.Mathlib.HeightPlaneAffineCoordinates

set_option autoImplicit false

namespace ContinuousAffineEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_apex_linear_height_cut_germ
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (A : E →ₗ[ℝ] ℝ)
    {p : E} (hf0 : f 0 = p) (hp : p ≠ 0)
    (hheight : ∀ x, A (f x) = x.1.1)
    (hapex : (f.symm 0).2 = 0) {σ : ℝ} (hσ : σ ≠ 0) :
    ∃ (k : ℝ) (e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ)),
      k = σ / (-(f.symm 0).1.2) ∧ k ≠ 0 ∧
      e p = ((0, σ), 0) ∧
      (∀ x : (ℝ × ℝ) × ℝ,
        e (f x) = ((x.1.1, k * (x.1.2 - (f.symm 0).1.2)), x.2)) ∧
      (∀ x : E, (e x).1.1 = A x) ∧
      ∀ t z : ℝ, e (f ((t, 0), z)) = ((t, σ), z) := by
  let s : ℝ := (f.symm 0).1.2
  have hfirst : (f.symm 0).1.1 = 0 := by
    have h := hheight (f.symm 0)
    rw [f.apply_symm_apply, map_zero] at h
    exact h.symm
  have hinverse : f.symm 0 = ((0, s), 0) := by
    exact Prod.ext (Prod.ext hfirst rfl) hapex
  have hs : s ≠ 0 := by
    intro hs
    have hz : f.symm 0 = 0 := by
      rw [hinverse, hs]
      rfl
    apply hp
    rw [← hf0, ← hz, f.apply_symm_apply]
  let k : ℝ := σ / (-s)
  have hk : k ≠ 0 := div_ne_zero hσ (neg_ne_zero.mpr hs)
  let L := f.symm.toAffineEquiv.linear
  have hL (x : E) : L x = f.symm x - f.symm 0 := by
    have h := f.symm.toAffineEquiv.toAffineMap.linearMap_vsub x 0
    change L (x - 0) = f.symm x - f.symm 0 at h
    simpa only [sub_zero] using h
  let S : ((ℝ × ℝ) × ℝ) ≃ₗ[ℝ] ((ℝ × ℝ) × ℝ) :=
    ((LinearEquiv.refl ℝ ℝ).prodCongr
      (LinearEquiv.smulOfNeZero ℝ ℝ k hk)).prodCongr (LinearEquiv.refl ℝ ℝ)
  let e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ) := (L.trans S).toContinuousLinearEquiv
  have hformula (x : (ℝ × ℝ) × ℝ) :
      e (f x) = ((x.1.1, k * (x.1.2 - s)), x.2) := by
    change S (L (f x)) = _
    rw [hL, f.symm_apply_apply, hinverse]
    ext <;> simp [S]
  have hks : k * (-s) = σ := by
    exact div_mul_cancel₀ σ (neg_ne_zero.mpr hs)
  have hlateral (t z : ℝ) : e (f ((t, 0), z)) = ((t, σ), z) := by
    rw [hformula]
    simp only [zero_sub, hks]
  refine ⟨k, e, rfl, hk, ?_, hformula, ?_, hlateral⟩
  · rw [← hf0]
    exact hlateral 0 0
  · intro x
    have h := congrArg (fun y : (ℝ × ℝ) × ℝ => y.1.1) (hformula (f.symm x))
    have hh := hheight (f.symm x)
    rw [f.apply_symm_apply] at h
    rw [f.apply_symm_apply] at hh
    exact h.trans hh.symm

end ContinuousAffineEquiv
