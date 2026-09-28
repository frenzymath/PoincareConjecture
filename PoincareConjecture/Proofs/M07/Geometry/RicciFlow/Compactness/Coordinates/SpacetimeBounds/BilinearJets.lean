import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.OperatorComponentJets



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000

open scoped ContDiff BigOperators

namespace PoincareConjecture.SpacetimeBounds

open CoordinateExponential

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem bilinear_eq_sum_dual {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    B = ∑ i, ∑ j, B (b i) (b j) • (innerSL ℝ (b i)).smulRight (innerSL ℝ (b j)) := by
  classical
  ext u v
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul,
    Finset.mul_sum, OrthonormalBasis.repr_apply_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring



theorem norm_iteratedFDeriv_bilinear_le_of_components {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) {F : P → E →L[ℝ] E →L[ℝ] ℝ} {x : P}
    (hF : ContDiffAt ℝ ∞ F x) (m : ℕ) {C : ℝ}
    (h : ∀ i j, ‖iteratedFDeriv ℝ m (fun y => F y (b i) (b j)) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ m F x‖ ≤ n * n * C := by
  classical
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  have hm : (m : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  let c (i j : Fin n) (y : P) := F y (b i) (b j)
  have hc (i j) : ContDiffAt ℝ ∞ (c i j) x :=
    (hF.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  let f (i j : Fin n) (y : P) :=
    c i j y • (innerSL ℝ (b i)).smulRight (innerSL ℝ (b j))
  have hf (i j) : ContDiffAt ℝ ∞ (f i j) x := (hc i j).smul contDiffAt_const
  have hb (i j) : ‖iteratedFDeriv ℝ m (f i j) x‖ ≤ C := by
    let L : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
      (ContinuousLinearMap.id ℝ ℝ).smulRight
        ((innerSL ℝ (b i)).smulRight (innerSL ℝ (b j)))
    have hL : ‖L‖ = 1 := by
      simp only [L, ContinuousLinearMap.norm_smulRight_apply,
        ContinuousLinearMap.norm_id, innerSL_apply_norm, b.norm_eq_one, mul_one]
    have hh := L.norm_iteratedFDeriv_comp_left (hc i j) hm
    rw [hL, one_mul] at hh
    exact hh.trans (h i j)
  have hi (i) := norm_iteratedFDeriv_sum_le_const
    (fun j => (hf i j).of_le hm) (hb i)
  have hall := norm_iteratedFDeriv_sum_le_const
    (fun i => ContDiffAt.sum (fun j _ => (hf i j).of_le hm)) hi
  have he : (fun y => ∑ i, ∑ j, f i j y) = F :=
    funext fun y => (bilinear_eq_sum_dual b (F y)).symm
  rw [he] at hall
  simpa only [Fintype.card_fin, mul_assoc] using hall

end PoincareConjecture.SpacetimeBounds
