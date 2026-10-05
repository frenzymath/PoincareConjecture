import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Calculus.ConnectionBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Calculus.LoweredConnectionDerivative
import PoincareLib.Geometry.Riemannian.Curvature.Bounds.Operator

/-!
# Quantitative curvature control from the actual metric error

The lowered connection identity bounds its covariant derivative by
the first two intrinsic errors. The actual curvature identity then
gives the full four-tensor defect in the background norm.
Morgan--Tian, pp. 3-7, Definition 9.76 and Lemma 11.2;
see M44 derivation 31.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

namespace PoincareMT.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000 in
-- Four-slot contractions normalize products of the background tangent norms.
/-- The lowered covariant derivative of the actual connection
correction is bounded by the first two error jets. Source:
the differentiated Koszul identity in M44 derivation 31. -/
theorem abs_inner_covariantConnectionDifference_le {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : E) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (herror : ∀ j ≤ 2,
      g.tensorNorm (D.iteratedCovariantTensorDerivative (metricError g h) j) x ≤ epsilon)
    (d u v w : E) :
    |h.inner x (covariantConnectionDifference g h x d u v) w| ≤
      ((3 / 2 : ℝ) * epsilon + 2 * epsilon ^ 2) *
        (g.tangentNorm x d * g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w) := by
  let P := g.tangentNorm x d * g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w
  have hsecond (a b c e : E) :
      |D.iteratedCovariantTensorDerivative (metricError g h) 2 x ![a, b, c, e]| ≤
        epsilon * (g.tangentNorm x a * g.tangentNorm x b *
          g.tangentNorm x c * g.tangentNorm x e) := by
    simpa only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.prod_univ_zero, mul_one, mul_assoc] using
      metricError_jet_evaluation_le D 2 x (herror 2 le_rfl) ![a, b, c, e]
  have hfirst := metricError_jet_evaluation_le D 1 x (herror 1 (by omega))
    ![d, connectionDifference g h x u v, w]
  simp only [LeviCivitaData.iteratedCovariantTensorDerivative, Fin.prod_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one] at hfirst
  have hc := tangentNorm_connectionDifference_le D D' x hepsilon hsmall
    (herror 0 (by omega)) (herror 1 (by omega)) u v
  have hfirst' : |D.covariantTensorDerivative (metricError g h) x
      ![d, connectionDifference g h x u v, w]| ≤ 2 * epsilon ^ 2 * P := by
    calc
      _ ≤ epsilon * (g.tangentNorm x d *
          (g.tangentNorm x (connectionDifference g h x u v) * g.tangentNorm x w)) := hfirst
      _ = (epsilon * g.tangentNorm x d * g.tangentNorm x w) *
          g.tangentNorm x (connectionDifference g h x u v) := by ring
      _ ≤ (epsilon * g.tangentNorm x d * g.tangentNorm x w) *
          (2 * epsilon * (g.tangentNorm x u * g.tangentNorm x v)) :=
        mul_le_mul_of_nonneg_left hc
          (mul_nonneg (mul_nonneg hepsilon (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      _ = 2 * epsilon ^ 2 * P := by dsimp [P]; ring
  have heq := inner_covariantConnectionDifference D D' x d u v w
  have habs : |2 * h.inner x (covariantConnectionDifference g h x d u v) w| ≤
      |D.iteratedCovariantTensorDerivative (metricError g h) 2 x ![d, u, v, w]| +
      |D.iteratedCovariantTensorDerivative (metricError g h) 2 x ![d, v, w, u]| +
      |D.iteratedCovariantTensorDerivative (metricError g h) 2 x ![d, w, u, v]| +
      2 * |D.covariantTensorDerivative (metricError g h) x
        ![d, connectionDifference g h x u v, w]| := by
    rw [heq]
    calc
      _ ≤ |_ - _| + |2 * D.covariantTensorDerivative (metricError g h) x
          ![d, connectionDifference g h x u v, w]| := abs_sub _ _
      _ ≤ (|_| + |_| + |_|) + |2 * D.covariantTensorDerivative (metricError g h) x
          ![d, connectionDifference g h x u v, w]| :=
        add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl
      _ = _ := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habs
  have h1 : |D.iteratedCovariantTensorDerivative (metricError g h) 2 x ![d, u, v, w]| ≤
      epsilon * P := hsecond d u v w
  have h2 : |D.iteratedCovariantTensorDerivative (metricError g h) 2 x ![d, v, w, u]| ≤
      epsilon * P := (hsecond d v w u).trans_eq (by dsimp [P]; ring)
  have h3 : |D.iteratedCovariantTensorDerivative (metricError g h) 2 x ![d, w, u, v]| ≤
      epsilon * P := (hsecond d w u v).trans_eq (by dsimp [P]; ring)
  have hsum := habs.trans (add_le_add
    (add_le_add (add_le_add h1 h2) h3)
    (mul_le_mul_of_nonneg_left hfirst' (by norm_num : (0 : ℝ) ≤ 2)))
  change |h.inner x (covariantConnectionDifference g h x d u v) w| ≤
    ((3 / 2 : ℝ) * epsilon + 2 * epsilon ^ 2) * P
  linarith only [hsum]

set_option maxHeartbeats 800000 in
-- The finite curvature expansion identifies native and tangent-space vector sums.
/-- The actual four-covariant curvature error is uniformly controlled
by the first two intrinsic metric errors and the background curvature
norm. Source: pp. 5-7 in M44 derivation 31. -/
theorem abs_curvatureTensor_difference_le {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : E) {epsilon K : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hcurv : D.curvatureTensorNorm x ≤ K)
    (herror : ∀ j ≤ 2,
      g.tensorNorm (D.iteratedCovariantTensorDerivative (metricError g h) j) x ≤ epsilon)
    (u v w z : E) :
    |D'.curvatureTensor x u v w z - D.curvatureTensor x u v w z| ≤
      ((K + 3) * epsilon + 10 * epsilon ^ 2) *
        (g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w * g.tangentNorm x z) := by
  let P := g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w * g.tangentNorm x z
  have hp (a : E) : 0 ≤ g.tangentNorm x a := Real.sqrt_nonneg _
  have hquad (a b c d : E) :
      |h.inner x (connectionDifference g h x a (connectionDifference g h x b c)) d| ≤
        3 * epsilon ^ 2 *
          (g.tangentNorm x a * g.tangentNorm x b * g.tangentNorm x c * g.tangentNorm x d) := by
    have hh := abs_inner_connectionDifference_le D D' x (herror 1 (by omega))
      a (connectionDifference g h x b c) d
    have hc := tangentNorm_connectionDifference_le D D' x hepsilon hsmall
      (herror 0 (by omega)) (herror 1 (by omega)) b c
    calc
      _ ≤ (3 / 2 : ℝ) * epsilon * (g.tangentNorm x a *
          g.tangentNorm x (connectionDifference g h x b c) * g.tangentNorm x d) := hh
      _ = ((3 / 2 : ℝ) * epsilon * g.tangentNorm x a * g.tangentNorm x d) *
          g.tangentNorm x (connectionDifference g h x b c) := by ring
      _ ≤ ((3 / 2 : ℝ) * epsilon * g.tangentNorm x a * g.tangentNorm x d) *
          (2 * epsilon * (g.tangentNorm x b * g.tangentNorm x c)) :=
        mul_le_mul_of_nonneg_left hc
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hepsilon) (hp a)) (hp d))
      _ = _ := by ring
  have hzero := metricError_jet_evaluation_le D 0 x (herror 0 (by omega))
    ![D.curvature x u v z, w]
  simp! only [Nat.add_zero, LeviCivitaData.iteratedCovariantTensorDerivative, metricError,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hzero
  have hR := (D.tangentNorm_curvature_le x u v z).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcurv (hp u)) (hp v)) (hp z))
  have hbase : |h.inner x (D.curvature x u v z) w - g.inner x (D.curvature x u v z) w| ≤
      K * epsilon * P := by
    calc
      _ ≤ epsilon * (g.tangentNorm x (D.curvature x u v z) * g.tangentNorm x w) := hzero
      _ = (epsilon * g.tangentNorm x w) * g.tangentNorm x (D.curvature x u v z) := by ring
      _ ≤ (epsilon * g.tangentNorm x w) *
          (K * g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x z) :=
        mul_le_mul_of_nonneg_left hR (mul_nonneg hepsilon (hp w))
      _ = K * epsilon * P := by dsimp [P]; ring
  have h1 := abs_inner_covariantConnectionDifference_le D D' x hepsilon hsmall herror u v z w
  have h2 := abs_inner_covariantConnectionDifference_le D D' x hepsilon hsmall herror v u z w
  have h3 := hquad u v z w
  have h4 := hquad v u z w
  have hid : D'.curvatureTensor x u v w z - D.curvatureTensor x u v w z =
      (h.inner x (D.curvature x u v z) w - g.inner x (D.curvature x u v z) w) +
      h.inner x (covariantConnectionDifference g h x u v z) w -
      h.inner x (covariantConnectionDifference g h x v u z) w +
      h.inner x (connectionDifference g h x u (connectionDifference g h x v z)) w -
      h.inner x (connectionDifference g h x v (connectionDifference g h x u z)) w := by
    unfold LeviCivitaData.curvatureTensor
    rw [curvature_eq_add_connectionDifference D D']
    simp! only [map_add, map_sub, add_apply, sub_apply]
    ring!
  rw [hid]
  calc
    _ ≤ |h.inner x (D.curvature x u v z) w - g.inner x (D.curvature x u v z) w| +
        |h.inner x (covariantConnectionDifference g h x u v z) w| +
        |h.inner x (covariantConnectionDifference g h x v u z) w| +
        |h.inner x (connectionDifference g h x u (connectionDifference g h x v z)) w| +
        |h.inner x (connectionDifference g h x v (connectionDifference g h x u z)) w| := by
      exact (abs_sub _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add
          ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by
      dsimp [P] at hbase
      nlinarith! only [hbase, h1, h2, h3, h4]

end PoincareMT.M44
