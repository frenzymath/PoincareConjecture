import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.GradientFrame
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped InnerProductSpace BigOperators

namespace Poincare.CurvatureIntegral

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

theorem norm_sum_smul_sq_lower_bound
    (v : ι → E) (c : ι → ℝ) {a δ : ℝ} (hδ : 0 ≤ δ)
    (hdiag : ∀ i, a ≤ ‖v i‖ ^ 2)
    (hcross : ∀ i j, i ≠ j → |⟪v i, v j⟫_ℝ| ≤ δ) :
    (a - (Fintype.card ι : ℝ) * δ) * (∑ i, c i ^ 2) ≤
      ‖∑ i, c i • v i‖ ^ 2 := by
  classical
  have hp (i j : ι) :
      (if i = j then a * c i ^ 2 else 0) - δ * |c i| * |c j| ≤
        c i * c j * ⟪v i, v j⟫_ℝ := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true, real_inner_self_eq_norm_sq]
      have h := mul_le_mul_of_nonneg_left (hdiag i) (sq_nonneg (c i))
      nlinarith [mul_nonneg hδ (sq_nonneg |c i|)]
    · rw [if_neg hij, zero_sub]
      have h := mul_le_mul_of_nonneg_left (hcross i j hij)
        (mul_nonneg (abs_nonneg (c i)) (abs_nonneg (c j)))
      have he : |c i * c j * ⟪v i, v j⟫_ℝ| ≤ δ * |c i| * |c j| := by
        simpa only [abs_mul, mul_comm, mul_left_comm, mul_assoc] using h
      exact (abs_le.mp he).1
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hp i j
  have hexp : ‖∑ i, c i • v i‖ ^ 2 =
      ∑ i, ∑ j, c i * c j * ⟪v i, v j⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsum : a * (∑ i, c i ^ 2) - δ * (∑ i, |c i|) ^ 2 ≤
      ‖∑ i, c i • v i‖ ^ 2 := by
    rw [hexp]
    convert hs using 1 <;> first
      | rfl
      | simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true, Finset.sum_mul, Finset.mul_sum, sq, mul_assoc]
    congr 1
    exact Finset.sum_comm
  have hCS : (∑ i, |c i|) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, c i ^ 2 := by
    simpa only [Finset.card_univ, sq_abs] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |c i|))
  have herr := mul_le_mul_of_nonneg_left hCS hδ
  nlinarith

theorem norm_starProjection_sq_le_of_inner_bounds
    [FiniteDimensional ℝ E]
    (v : ι → E) (z : E) {a δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hdiag : ∀ i, a ≤ ‖v i‖ ^ 2)
    (hcross : ∀ i j, i ≠ j → |⟪v i, v j⟫_ℝ| ≤ δ)
    (hpos : 0 < a - (Fintype.card ι : ℝ) * δ)
    (hz : ∀ i, |⟪z, v i⟫_ℝ| ≤ ε) :
    ‖(Submodule.span ℝ (Set.range v)).starProjection z‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ε ^ 2 / (a - (Fintype.card ι : ℝ) * δ) := by
  classical
  let V := Submodule.span ℝ (Set.range v)
  let p := V.starProjection z
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (V.starProjection_apply_mem z)
  have hgram := norm_sum_smul_sq_lower_bound v c hδ hdiag hcross
  rw [hc] at hgram
  change (a - (Fintype.card ι : ℝ) * δ) * (∑ i, c i ^ 2) ≤ ‖p‖ ^ 2 at hgram
  have hpair : ⟪z, p⟫_ℝ = ‖p‖ ^ 2 := by
    have h := V.starProjection_inner_eq_zero z p (V.starProjection_apply_mem z)
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
    exact sub_eq_zero.mp h
  have heq : ‖p‖ ^ 2 = ∑ i, c i * ⟪z, v i⟫_ℝ := by
    rw [← hpair, show p = ∑ i, c i • v i from hc.symm]
    simp only [inner_sum, real_inner_smul_right]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c (fun i => ⟪z, v i⟫_ℝ)
  have hb : (∑ i, ⟪z, v i⟫_ℝ ^ 2) ≤ (Fintype.card ι : ℝ) * ε ^ 2 := by
    calc
      _ ≤ ∑ _i : ι, ε ^ 2 := Finset.sum_le_sum fun i _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hε).mpr (hz i)
      _ = _ := by simp
  have hS : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ (Fintype.card ι : ℝ) * ε ^ 2 := by positivity
  have hbound : (‖p‖ ^ 2) ^ 2 ≤ (∑ i, c i ^ 2) *
      ((Fintype.card ι : ℝ) * ε ^ 2) := by
    rw [heq]
    exact hCS.trans (mul_le_mul_of_nonneg_left hb hS)
  have hbound' := mul_le_mul_of_nonneg_left hbound hpos.le
  have hgram' := mul_le_mul_of_nonneg_right hgram hB
  apply (le_div_iff₀ hpos).mpr
  change ‖p‖ ^ 2 * _ ≤ _
  by_cases hp : ‖p‖ ^ 2 = 0
  · rw [hp, zero_mul]
    exact hB
  · have hp' : 0 < ‖p‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hp)
    nlinarith

theorem norm_orthogonal_strainer_projection_ge_half
    [FiniteDimensional ℝ E]
    (v w : ι → E) (z z' : E) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (8 * ((Fintype.card ι : ℝ) + 1)))
    (hw : ∀ i, ‖w i‖ ≤ 1)
    (hopposite : ∀ i, ⟪v i, w i⟫_ℝ ≤ -1 + 2 * δ)
    (hcross : ∀ i j, i ≠ j → |⟪v i, v j⟫_ℝ| ≤ δ)
    (hz' : ‖z'‖ ≤ 1) (hzopp : ⟪z, z'⟫_ℝ ≤ -1 + 2 * δ)
    (hzcross : ∀ i, |⟪z, v i⟫_ℝ| ≤ δ) :
    1 / 2 ≤ ‖(Submodule.span ℝ (Set.range v))ᗮ.starProjection z‖ := by
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hproduct : 0 ≤ (Fintype.card ι : ℝ) * δ := mul_nonneg hk hδ
  have hmul := (le_div_iff₀
    (by positivity : (0 : ℝ) < 8 * ((Fintype.card ι : ℝ) + 1))).mp hsmall
  have hδsmall : δ ≤ 1 / 8 := by nlinarith
  have hkδ : (Fintype.card ι : ℝ) * δ ≤ 1 / 8 := by nlinarith
  have hlow : 0 ≤ 1 - 2 * δ := by linarith
  have hdiag (i : ι) : (1 - 2 * δ) ^ 2 ≤ ‖v i‖ ^ 2 :=
    (sq_le_sq₀ hlow (norm_nonneg _)).mpr
      (norm_lower_bound_of_opposite_pair (v i) (w i) (hw i) (hopposite i))
  have hden : 1 / 4 ≤ (1 - 2 * δ) ^ 2 - (Fintype.card ι : ℝ) * δ := by
    nlinarith [sq_nonneg δ]
  have hnum : (Fintype.card ι : ℝ) * δ ^ 2 ≤ 1 / 64 := by
    have h := mul_le_mul hkδ hδsmall hδ (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith
  have hp := norm_starProjection_sq_le_of_inner_bounds v z hδ hδ hdiag hcross
    (by linarith : 0 < (1 - 2 * δ) ^ 2 - (Fintype.card ι : ℝ) * δ) hzcross
  have hproj : ‖(Submodule.span ℝ (Set.range v)).starProjection z‖ ^ 2 ≤ 1 / 16 := by
    apply hp.trans
    apply (div_le_iff₀ (by linarith :
      0 < (1 - 2 * δ) ^ 2 - (Fintype.card ι : ℝ) * δ)).mpr
    linarith
  have hz := norm_lower_bound_of_opposite_pair z z' hz' hzopp
  have hzsq := (sq_le_sq₀ hlow (norm_nonneg z)).mpr hz
  have hpyth := (Submodule.span ℝ (Set.range v)).norm_sq_eq_add_norm_sq_starProjection z
  have ht := norm_nonneg ((Submodule.span ℝ (Set.range v))ᗮ.starProjection z)
  nlinarith [sq_nonneg δ]

end Poincare.CurvatureIntegral
