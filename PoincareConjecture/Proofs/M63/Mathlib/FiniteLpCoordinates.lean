import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Real










set_option autoImplicit false

open scoped ENNReal

namespace PoincareConjecture.M63

variable {α ι E : Type*} [NormedAddCommGroup E]




theorem memℓp_prod_finite_iff [Finite ι] (f : α × ι → E) :
    Memℓp f 2 ↔ ∀ i, Memℓp (fun a => f (a, i)) 2 := by
  let := Fintype.ofFinite ι
  simp only [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal),
    ENNReal.toReal_ofNat, Real.rpow_two]
  constructor
  · intro h
    exact (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mp h.prod_symm |>.1
  · intro h
    have hs : Summable (fun p : ι × α => ‖f (p.2, p.1)‖ ^ 2) :=
      (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
        ⟨h, (hasSum_fintype _).summable⟩
    exact hs.prod_symm

variable [Fintype ι] (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]




noncomputable def lpFinitePiEquiv :
    lp (fun _ : α × ι => E) 2 ≃L[𝕜] (ι → lp (fun _ : α => E) 2) := by
  let S : lp (fun _ : α × ι => E) 2 → (ι → lp (fun _ : α => E) 2) :=
    fun u i => ⟨fun a => u (a, i), (memℓp_prod_finite_iff u).mp u.prop i⟩
  let J : (ι → lp (fun _ : α => E) 2) → lp (fun _ : α × ι => E) 2 :=
    fun v => ⟨fun p => v p.2 p.1, (memℓp_prod_finite_iff _).mpr (fun i => (v i).prop)⟩
  let e : lp (fun _ : α × ι => E) 2 ≃ₗ[𝕜] (ι → lp (fun _ : α => E) 2) :=
    { toFun := S
      invFun := J
      map_add' := by intro u v; rfl
      map_smul' := by intro c u; rfl
      left_inv := by intro u; rfl
      right_inv := by intro v; rfl }
  have henergy (u : lp (fun _ : α × ι => E) 2) :
      ‖u‖ ^ 2 = ∑ i, ‖S u i‖ ^ 2 := by
    have hu := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) u
    have hi (i : ι) := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ENNReal).toReal) (S u i)
    have hs := (lp.memℓp u).summable (by norm_num : 0 < (2 : ENNReal).toReal)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hu hi hs
    rw [hu, ← (Equiv.prodComm ι α).tsum_eq (fun p : α × ι => ‖u p‖ ^ 2)]
    change (∑' p : ι × α, ‖u p.swap‖ ^ 2) = _
    rw [hs.prod_symm.tsum_prod, tsum_fintype]
    exact Finset.sum_congr rfl (fun i _ => (hi i).symm)
  refine e.toContinuousLinearEquivOfBounds 1 (1 + (Fintype.card ι : ℝ)) ?_ ?_
  · intro u
    change ‖S u‖ ≤ 1 * ‖u‖
    rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg u)]
    intro i
    have hi : ‖S u i‖ ^ 2 ≤ ∑ j, ‖S u j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖S u j‖) (Finset.mem_univ i)
    rw [← henergy] at hi
    nlinarith [norm_nonneg (S u i), norm_nonneg u]
  · intro v
    change ‖J v‖ ≤ (1 + (Fintype.card ι : ℝ)) * ‖v‖
    have he : ‖J v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := henergy (J v)
    have hs : (∑ i, ‖v i‖ ^ 2) ≤ (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
      calc
        _ ≤ ∑ _i : ι, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
        _ = _ := by simp
    have hN : 0 ≤ (Fintype.card ι : ℝ) := by positivity
    have hmul : (Fintype.card ι : ℝ) * ‖v‖ ^ 2 ≤
        ((1 + (Fintype.card ι : ℝ)) * ‖v‖) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (Fintype.card ι : ℝ)) (sq_nonneg ‖v‖),
        mul_nonneg hN (sq_nonneg ‖v‖)]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (he.trans_le (hs.trans hmul))




theorem lpFinitePiEquiv_norm_sq (u : lp (fun _ : α × ι => E) 2) :
    ‖u‖ ^ 2 = ∑ i, ‖lpFinitePiEquiv 𝕜 u i‖ ^ 2 := by
  have hu := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) u
  have hi (i : ι) := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ENNReal).toReal) (lpFinitePiEquiv 𝕜 u i)
  have hs := (lp.memℓp u).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hu hi hs
  rw [hu, ← (Equiv.prodComm ι α).tsum_eq (fun p : α × ι => ‖u p‖ ^ 2)]
  change (∑' p : ι × α, ‖u p.swap‖ ^ 2) = _
  rw [hs.prod_symm.tsum_prod, tsum_fintype]
  exact Finset.sum_congr rfl (fun i _ => (hi i).symm)




theorem norm_lpFinitePiEquiv_le (u : lp (fun _ : α × ι => E) 2) :
    ‖lpFinitePiEquiv 𝕜 u‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg u)]
  intro i
  have hi : ‖lpFinitePiEquiv 𝕜 u i‖ ^ 2 ≤ ∑ j, ‖lpFinitePiEquiv 𝕜 u j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖lpFinitePiEquiv 𝕜 u j‖) (Finset.mem_univ i)
  rw [← lpFinitePiEquiv_norm_sq] at hi
  nlinarith [norm_nonneg (lpFinitePiEquiv 𝕜 u i), norm_nonneg u]




theorem norm_lpFinitePiEquiv_symm_le (v : ι → lp (fun _ : α => E) 2) :
    ‖(lpFinitePiEquiv 𝕜).symm v‖ ≤ (1 + (Fintype.card ι : ℝ)) * ‖v‖ := by
  have he := lpFinitePiEquiv_norm_sq 𝕜 ((lpFinitePiEquiv 𝕜).symm v)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at he
  have hs : (∑ i, ‖v i‖ ^ 2) ≤ (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
    calc
      _ ≤ ∑ _i : ι, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
      _ = _ := by simp
  have hN : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hmul : (Fintype.card ι : ℝ) * ‖v‖ ^ 2 ≤
      ((1 + (Fintype.card ι : ℝ)) * ‖v‖) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (Fintype.card ι : ℝ)) (sq_nonneg ‖v‖),
      mul_nonneg hN (sq_nonneg ‖v‖)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (he.trans_le (hs.trans hmul))

end PoincareConjecture.M63
