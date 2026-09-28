import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FrameJetBounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff BigOperators

namespace PoincareConjecture.CoordinateExponential

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem operator_eq_sum_rankOne {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (L : E →L[ℝ] E) :
    L = ∑ i, ∑ a, inner ℝ (b a) (L (b i)) • InnerProductSpace.rankOne ℝ (b a) (b i) := by
  classical
  let : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  ext w
  calc
    L w = ∑ i, b.repr w i • L (b i) := by
      simpa only [map_sum, map_smul] using congrArg L (b.sum_repr w).symm
    _ = ∑ i, ∑ a, inner ℝ (b a) (L (b i)) •
        (InnerProductSpace.rankOne ℝ (b a) (b i) w) := by
      apply Finset.sum_congr rfl
      intro i _
      nth_rw 1 [← b.sum_repr (L (b i))]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [OrthonormalBasis.repr_apply_apply, InnerProductSpace.rankOne_apply,
        smul_smul]
      congr 1
      ring
    _ = _ := by simp only [sum_apply, smul_apply]

theorem norm_iteratedFDeriv_operator_le_of_components {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) {F : P → E →L[ℝ] E}
    (hF : ContDiff ℝ ∞ F) (m : ℕ) {x : P} {C : ℝ}
    (h : ∀ i a, ‖iteratedFDeriv ℝ m (fun y => inner ℝ (b a) (F y (b i))) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ m F x‖ ≤ n * n * C := by
  classical
  let : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  have hm : (m : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  let c (i a : Fin n) (y : P) := inner ℝ (b a) (F y (b i))
  have hc (i a) : ContDiff ℝ ∞ (c i a) :=
    (innerSL ℝ (b a)).contDiff.comp (hF.clm_apply contDiff_const)
  let f (i a : Fin n) (y : P) := c i a y • InnerProductSpace.rankOne ℝ (b a) (b i)
  have hf (i a) : ContDiff ℝ ∞ (f i a) := (hc i a).smul contDiff_const
  have hb (i a) : ‖iteratedFDeriv ℝ m (f i a) x‖ ≤ C := by
    let L : ℝ →L[ℝ] (E →L[ℝ] E) :=
      (ContinuousLinearMap.id ℝ ℝ).smulRight (InnerProductSpace.rankOne ℝ (b a) (b i))
    have hL : ‖L‖ = 1 := by
      simp only [L, ContinuousLinearMap.norm_smulRight_apply,
        ContinuousLinearMap.norm_id, InnerProductSpace.norm_rankOne, b.norm_eq_one, mul_one]
    have hh := L.norm_iteratedFDeriv_comp_left (x := x) (hc i a).contDiffAt hm
    rw [hL, one_mul] at hh
    exact hh.trans (h i a)
  have hi (i) := norm_iteratedFDeriv_sum_le_const
    (fun a => ((hf i a).of_le hm).contDiffAt) (hb i)
  have hall := norm_iteratedFDeriv_sum_le_const
    (fun i => ContDiffAt.sum (fun a _ => ((hf i a).of_le hm).contDiffAt)) hi
  have he : (fun y => ∑ i, ∑ a, f i a y) = F :=
    funext fun y => (operator_eq_sum_rankOne b (F y)).symm
  rw [he] at hall
  simpa only [Fintype.card_fin, mul_assoc] using hall

end PoincareConjecture.CoordinateExponential
