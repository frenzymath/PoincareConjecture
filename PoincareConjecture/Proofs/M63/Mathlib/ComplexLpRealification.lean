import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Fin.VecNotation











set_option autoImplicit false

open scoped ENNReal

namespace PoincareConjecture.M63

variable {ι : Type*}




theorem memℓp_complex_coords_iff (f : ι → ℂ) :
    Memℓp (fun p : ι × Fin 2 => ![(f p.1).re, (f p.1).im] p.2) 2 ↔ Memℓp f 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal),
    memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  have hsq (i : ι) : (∑' j : Fin 2, ‖![(f i).re, (f i).im] j‖ ^ 2) = ‖f i‖ ^ 2 := by
    simp only [tsum_fintype, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.norm_eq_abs, sq_abs,
      Complex.sq_norm, Complex.normSq_apply]
    ring
  simp_rw [hsq]
  exact ⟨And.right, fun h => ⟨fun _ => (hasSum_fintype _).summable, h⟩⟩




noncomputable def complexLpRealEquiv :
    lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℝ] lp (fun _ : ι × Fin 2 => ℝ) 2 := by
  let R : lp (fun _ : ι => ℂ) 2 → lp (fun _ : ι × Fin 2 => ℝ) 2 := fun z =>
    ⟨fun p => ![(z p.1).re, (z p.1).im] p.2, (memℓp_complex_coords_iff z).mpr z.prop⟩
  let C : lp (fun _ : ι × Fin 2 => ℝ) 2 → lp (fun _ : ι => ℂ) 2 := fun u =>
    ⟨fun i => ⟨u (i, 0), u (i, 1)⟩, by
      apply (memℓp_complex_coords_iff _).mp
      have heq : (fun p : ι × Fin 2 => ![u (p.1, 0), u (p.1, 1)] p.2) = u := by
        funext p
        rcases p with ⟨i, j⟩
        fin_cases j <;> rfl
      change Memℓp (fun p : ι × Fin 2 => ![u (p.1, 0), u (p.1, 1)] p.2) 2
      rw [heq]
      exact u.prop⟩
  refine
    { toFun := R
      invFun := C
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_
      norm_map' := ?_ }
  · intro z w
    apply lp.ext
    funext p
    rcases p with ⟨i, j⟩
    fin_cases j <;> rfl
  · intro r z
    apply lp.ext
    funext p
    rcases p with ⟨i, j⟩
    fin_cases j <;> simp [R]
  · intro z
    apply lp.ext
    funext i
    rfl
  · intro u
    apply lp.ext
    funext p
    rcases p with ⟨i, j⟩
    fin_cases j <;> rfl
  · intro z
    change ‖R z‖ = ‖z‖
    have hr := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (R z)
    have hc := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) z
    have hs := (lp.memℓp (R z)).summable (by norm_num : 0 < (2 : ENNReal).toReal)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hr hc hs
    have hsq : ‖R z‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [hr, hc, hs.tsum_prod]
      congr 1
      funext i
      simp only [R, tsum_fintype, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Real.norm_eq_abs, sq_abs,
        Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg (R z), norm_nonneg z]



theorem complexLpRealEquiv_apply (z : lp (fun _ : ι => ℂ) 2) (p : ι × Fin 2) :
    complexLpRealEquiv z p = ![(z p.1).re, (z p.1).im] p.2 := rfl




theorem complexLpRealEquiv_symm_apply (u : lp (fun _ : ι × Fin 2 => ℝ) 2) (i : ι) :
    complexLpRealEquiv.symm u i = (u (i, 0) : ℂ) + Complex.I * (u (i, 1) : ℂ) := by
  change (⟨u (i, 0), u (i, 1)⟩ : ℂ) = _
  apply Complex.ext <;> simp





theorem complexLpRealEquiv_real_weight_iff (m : ι → ℝ)
    (u v : lp (fun _ : ι => ℂ) 2) :
    (∀ i, v i = (m i : ℂ) * u i) ↔
      ∀ p : ι × Fin 2, complexLpRealEquiv v p = m p.1 * complexLpRealEquiv u p := by
  constructor
  · intro h p
    rcases p with ⟨i, j⟩
    fin_cases j <;> simp [complexLpRealEquiv_apply, h i]
  · intro h i
    apply Complex.ext
    · simpa [complexLpRealEquiv_apply] using h (i, 0)
    · simpa [complexLpRealEquiv_apply] using h (i, 1)

end PoincareConjecture.M63
