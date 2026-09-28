import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_CurvatureDefectBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem abs_scalarCurvature_le_of_metric_error {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : E) {epsilon K : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4) (hK : 0 ≤ K)
    (hcurv : D.curvatureTensorNorm x ≤ K)
    (herror : ∀ j ≤ 2,
      g.tensorNorm (D.iteratedCovariantTensorDerivative (metricError g h) j) x ≤ epsilon) :
    |D'.scalarCurvature x| ≤ 72 * (K + 3) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : E → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let b := h.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    unfold TangentSpace
    simp
  have hpos (v : E) : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hsq (v : E) : g.tangentNorm x v ^ 2 = g.inner x v v := Real.sq_sqrt (hpos v)
  have hunit (i) : h.inner x (b i) (b i) = 1 := by
    change inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow]
  have hbackground (i) : g.inner x (b i) (b i) ≤ 2 := by
    have hz := metricError_jet_evaluation_le D 0 x (herror 0 (by omega)) ![b i, b i]
    simp! only [Nat.add_zero, LeviCivitaData.iteratedCovariantTensorDerivative,
      metricError, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      ← sq, hsq, hunit] at hz
    have hm := mul_le_mul_of_nonneg_right hsmall (hpos (b i))
    have hl := (abs_le.mp hz).1
    linarith
  let d := (K + 3) * epsilon + 10 * epsilon ^ 2
  have hcoef : K + d ≤ 2 * (K + 3) := by
    have hm := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ K + 3 by linarith)
    have hs : epsilon ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
      sq_le_sq₀ hepsilon (by norm_num) |>.mpr hsmall
    dsimp [d]
    nlinarith
  have hcoef0 : 0 ≤ 2 * (K + 3) := by positivity
  have hterm (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      |D'.curvatureTensor x (b i) (b j) (b i) (b j)| ≤ 8 * (K + 3) := by
    let A := g.inner x (b i) (b i) * g.inner x (b j) (b j)
    have hA0 : 0 ≤ A := mul_nonneg (hpos _) (hpos _)
    have hA : A ≤ 4 := by
      have h := mul_le_mul (hbackground i) (hbackground j) (hpos (b j))
        (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using h
    have hprod : g.tangentNorm x (b i) * g.tangentNorm x (b j) *
        g.tangentNorm x (b i) * g.tangentNorm x (b j) = A := by
      dsimp [A]
      rw [← hsq, ← hsq]
      ring
    have hd := abs_curvatureTensor_difference_le D D' x hepsilon hsmall hcurv herror
      (b i) (b j) (b i) (b j)
    rw [hprod] at hd
    have hb := D.abs_curvatureTensor_le_tangentNorm x (b i) (b j) (b i) (b j)
    have hb' : |D.curvatureTensor x (b i) (b j) (b i) (b j)| ≤ K * A := by
      have he : D.curvatureTensorNorm x * g.tangentNorm x (b i) *
          g.tangentNorm x (b j) * g.tangentNorm x (b i) * g.tangentNorm x (b j) =
            D.curvatureTensorNorm x * A := by rw [← hprod]; ring
      rw [he] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right hcurv hA0)
    calc
      _ ≤ |D'.curvatureTensor x (b i) (b j) (b i) (b j) -
          D.curvatureTensor x (b i) (b j) (b i) (b j)| +
          |D.curvatureTensor x (b i) (b j) (b i) (b j)| :=
        by simpa only [sub_add_cancel] using
          abs_add_le (D'.curvatureTensor x (b i) (b j) (b i) (b j) -
            D.curvatureTensor x (b i) (b j) (b i) (b j))
            (D.curvatureTensor x (b i) (b j) (b i) (b j))
      _ ≤ d * A + K * A := add_le_add hd hb'
      _ = (K + d) * A := by ring
      _ ≤ 2 * (K + 3) * A := mul_le_mul_of_nonneg_right hcoef hA0
      _ ≤ 2 * (K + 3) * 4 := mul_le_mul_of_nonneg_left hA hcoef0
      _ = _ := by ring
  change |∑ i, ∑ j, D'.curvatureTensor x (b i) (b j) (b i) (b j)| ≤ _
  calc
    _ ≤ ∑ i, ∑ j, |D'.curvatureTensor x (b i) (b j) (b i) (b j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)), 8 * (K + 3) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by simp [hdim]; ring

end PoincareConjecture.M44
