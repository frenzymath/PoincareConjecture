import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Calculus.ConnectionDifference

/-!
# Intrinsic bounds for the actual connection correction

The first error tensor bounds the lowered Koszul correction. The
zeroth error then converts this to its background tangent norm.
Morgan--Tian, pp. 3-7, Definition 9.76 and Lemma 11.2;
see M44 derivation 31.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

namespace PoincareMT.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- The intrinsic norm controls every evaluation of an actual error
jet. Multilinearity comes from smoothness. Source: Definition 2.16,
used in the perturbation calculation for Definition 9.76. -/
theorem metricError_jet_evaluation_le {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (m : ℕ) (x : E) {epsilon : ℝ}
    (hbound : g.tensorNorm (D.iteratedCovariantTensorDerivative (metricError g h) m) x ≤
      epsilon) (v : Fin (2 + m) → E) :
    |D.iteratedCovariantTensorDerivative (metricError g h) m x v| ≤
      epsilon * ∏ i, g.tangentNorm x (v i) := by
  obtain ⟨A, hA⟩ :=
    (D.iteratedCovariantTensorDerivative_isSmooth (metricError_isSmooth g h) m).1 x
  exact (abs_tensor_evaluation_le_tensorNorm g _ x A hA v).trans
    (mul_le_mul_of_nonneg_right hbound (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _))

/-- The first intrinsic error bounds the connection difference after
lowering with the actual metric. Source: the Koszul formula on pp. 3-4
in M44 derivation 31. -/
theorem abs_inner_connectionDifference_le {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : E) {epsilon : ℝ}
    (hbound : g.tensorNorm (D.iteratedCovariantTensorDerivative (metricError g h) 1) x ≤
      epsilon) (u v w : E) :
    |h.inner x (connectionDifference g h x u v) w| ≤
      (3 / 2 : ℝ) * epsilon * (g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w) := by
  have h1 := metricError_jet_evaluation_le D 1 x hbound ![u, v, w]
  have h2 := metricError_jet_evaluation_le D 1 x hbound ![v, w, u]
  have h3 := metricError_jet_evaluation_le D 1 x hbound ![w, u, v]
  simp only [LeviCivitaData.iteratedCovariantTensorDerivative, Fin.prod_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one] at h1 h2 h3
  have heq := inner_connectionDifference D D' x u v w
  have h : |D.covariantTensorDerivative (metricError g h) x ![u, v, w] +
      D.covariantTensorDerivative (metricError g h) x ![v, w, u] -
      D.covariantTensorDerivative (metricError g h) x ![w, u, v]| ≤
      |D.covariantTensorDerivative (metricError g h) x ![u, v, w]| +
      |D.covariantTensorDerivative (metricError g h) x ![v, w, u]| +
      |D.covariantTensorDerivative (metricError g h) x ![w, u, v]| :=
    (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [← heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  nlinarith! only [h, h1, h2, h3]

/-- Small zeroth and first intrinsic errors bound the actual connection
correction in the background metric. Source: Definition 9.76 in the
round perturbation estimate, M44 derivation 31. -/
theorem tangentNorm_connectionDifference_le {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : E) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hzero : g.tensorNorm (D.iteratedCovariantTensorDerivative (metricError g h) 0) x ≤
      epsilon)
    (hone : g.tensorNorm (D.iteratedCovariantTensorDerivative (metricError g h) 1) x ≤
      epsilon) (u v : E) :
    g.tangentNorm x (connectionDifference g h x u v) ≤
      2 * epsilon * (g.tangentNorm x u * g.tangentNorm x v) := by
  let c := connectionDifference g h x u v
  have hc0 : 0 ≤ g.tangentNorm x c := Real.sqrt_nonneg _
  have hp : 0 ≤ g.tangentNorm x u * g.tangentNorm x v :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hgg : 0 ≤ g.inner x c c := by
    by_cases hc : c = 0
    · simp [hc]
    · exact (g.pos x c hc).le
  have hsq : g.tangentNorm x c ^ 2 = g.inner x c c := Real.sq_sqrt hgg
  have herror := metricError_jet_evaluation_le D 0 x hzero ![c, c]
  simp! only [Nat.add_zero, LeviCivitaData.iteratedCovariantTensorDerivative, metricError,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ← sq, hsq] at herror
  have hmetric : (3 / 4 : ℝ) * g.tangentNorm x c ^ 2 ≤ h.inner x c c := by
    have hh := (abs_le.mp herror).1
    have he := mul_le_mul_of_nonneg_right hsmall hgg
    nlinarith! only [hh, he, hsq]
  have hconn := abs_inner_connectionDifference_le D D' x hone u v c
  change |h.inner x c c| ≤ _ at hconn
  have hc : (3 / 4 : ℝ) * g.tangentNorm x c ^ 2 ≤
      (3 / 2 : ℝ) * epsilon *
        (g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x c) :=
    hmetric.trans ((le_abs_self _).trans hconn)
  by_cases hz : g.tangentNorm x c = 0
  · rw [hz]
    exact mul_nonneg (mul_nonneg (by norm_num) hepsilon) hp
  · have hpos : 0 < g.tangentNorm x c := lt_of_le_of_ne hc0 (Ne.symm hz)
    nlinarith only [hc, hpos]

end PoincareMT.M44
