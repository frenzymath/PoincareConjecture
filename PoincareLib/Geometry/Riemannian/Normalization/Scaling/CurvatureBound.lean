import PoincareLib.Geometry.Riemannian.Normalization.Curvature.Bound
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Distance

/-!
# Curvature control after choosing a sufficiently large scale

If the original four-tensor evaluation is bounded by `B` times the product
of input norms, a `c g`-orthonormal component is bounded by `B / c`.
There are 81 components in dimension three, so `c >= 9 B` suffices for
the full tensor norm to be at most one. This avoids any assertion that the
two pointwise chosen orthonormal bases agree under rescaling.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem rescaledMetric_curvatureTensorNorm_le (D : LeviCivitaData g)
    (B : ℝ) (hB : ∀ x : M, ∀ v : Fin 4 → TangentSpace (𝓡 3) x,
      |D.riemannEvaluation x v| ≤ B * ∏ i, g.tangentNorm x (v i))
    (c : ℝ) (hc : 0 < c) (hcB : 9 * B ≤ c) (x : M) :
    (rescaledMetric_connection g D c hc).curvatureTensorNorm x ≤ 1 := by
  let g' := rescaledMetric g c hc
  let D' := rescaledMetric_connection g D c hc
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g'.toRiemannianMetric⟩
  let b := g'.orthonormalBasis x
  have hsqrt : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hnorm (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      g.tangentNorm x (b i) = 1 / Real.sqrt c := by
    have hb : g'.tangentNorm x (b i) = 1 := by
      rw [show g'.tangentNorm x (b i) = ‖b i‖ from (norm_eq_sqrt_real_inner (b i)).symm]
      exact b.norm_eq_one i
    change (rescaledMetric g c hc).tangentNorm x (b i) = 1 at hb
    rw [rescaledMetric_tangentNorm] at hb
    apply (eq_div_iff hsqrt).mpr
    nlinarith
  have hcomponent (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      |D'.curvatureTensor x (b i) (b j) (b k) (b l)| ≤ 1 / 9 := by
    have h := hB x ![b i, b j, b k, b l]
    simp only [LeviCivitaData.riemannEvaluation, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, hnorm, mul_one] at h
    have hfour : Real.sqrt c ^ 4 = c ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hc.le]
    calc
      |D'.curvatureTensor x (b i) (b j) (b k) (b l)| =
          c * |D.curvatureTensor x (b i) (b j) (b k) (b l)| := by
        rw [rescaledMetric_curvatureTensor, abs_mul, abs_of_pos hc]
      _ ≤ c * (B * ((1 / Real.sqrt c) * ((1 / Real.sqrt c) *
          ((1 / Real.sqrt c) * (1 / Real.sqrt c))))) := mul_le_mul_of_nonneg_left h hc.le
      _ = B / c := by
        rw [show (1 / Real.sqrt c) * ((1 / Real.sqrt c) *
          ((1 / Real.sqrt c) * (1 / Real.sqrt c))) = (1 / Real.sqrt c) ^ 4 by ring]
        rw [div_pow, one_pow, hfour]
        field_simp
      _ ≤ 1 / 9 := (div_le_iff₀ hc).mpr (by linarith)
  have hsq (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      (D'.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2 ≤ 1 / 81 := by
    have h := hcomponent i j k l
    nlinarith [sq_abs (D'.curvatureTensor x (b i) (b j) (b k) (b l)),
      abs_nonneg (D'.curvatureTensor x (b i) (b j) (b k) (b l))]
  apply Real.sqrt_le_iff.mpr
  refine ⟨zero_le_one, ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
        Finset.sum_le_sum (s := Finset.univ) (fun l _ => hsq i j k l))))
  norm_num [normalization_tangentSpace_finrank] at hsum
  simpa only [one_pow] using hsum

end PoincareMT
