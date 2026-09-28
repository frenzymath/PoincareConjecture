import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.RicciContraction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bilinear

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem ricci_reference_lower_bound (D : LeviCivitaData g)
    (x U X : EuclideanSpace ℝ (Fin n)) {K B r s : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hcurv : D.curvatureTensorNorm x ≤ K)
    (hX : g.tangentNorm x X ≤ B)
    (hscale : r ^ 2 * (n : ℝ) * K * B ≤ s) :
    let V := U - X
    let w := Real.sqrt (g.inner x V V + s ^ 2);
    -(((n : ℝ) * K + (r ^ 2)⁻¹) * w ^ 2) ≤ D.ricci x U V := by
  let V := U - X
  let w := Real.sqrt (g.inner x V V + s ^ 2)
  have hK : 0 ≤ K := (Real.sqrt_nonneg _).trans hcurv
  have hB : 0 ≤ B := (Real.sqrt_nonneg _).trans hX
  have hVV : 0 ≤ g.inner x V V := by
    by_cases hV : V = 0
    · simp [hV]
    · exact (g.pos x _ hV).le
  have hv : 0 ≤ g.tangentNorm x V := Real.sqrt_nonneg _
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  have hvw : g.tangentNorm x V ≤ w :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg s))
  have hsw : s ≤ w := by
    have h := Real.sqrt_le_sqrt (le_add_of_nonneg_left hVV :
      s ^ 2 ≤ g.inner x V V + s ^ 2)
    simpa only [Real.sqrt_sq hs.le] using h
  have hcoeff : (n : ℝ) * K * B ≤ s / r ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by nlinarith [hscale])
  have hric (u v : EuclideanSpace ℝ (Fin n)) :
      |D.ricci x u v| ≤ (n : ℝ) * K * g.tangentNorm x u * g.tangentNorm x v := by
    refine (D.abs_ricci_le_tangentNorm x u v).trans ?_
    gcongr <;> exact Real.sqrt_nonneg _
  have hdiag : |D.ricci x V V| ≤ (n : ℝ) * K * w ^ 2 := by
    calc
      _ ≤ (n : ℝ) * K * g.tangentNorm x V * g.tangentNorm x V := hric V V
      _ ≤ (n : ℝ) * K * w * w := by gcongr
      _ = _ := by ring
  have hsource : |D.ricci x X V| ≤ (r ^ 2)⁻¹ * w ^ 2 := by
    calc
      _ ≤ (n : ℝ) * K * g.tangentNorm x X * g.tangentNorm x V := hric X V
      _ ≤ ((n : ℝ) * K * B) * g.tangentNorm x V := by gcongr
      _ ≤ (s / r ^ 2) * w := by gcongr
      _ = (r ^ 2)⁻¹ * s * w := by rw [div_eq_mul_inv]; ring
      _ ≤ (r ^ 2)⁻¹ * w * w := by gcongr
      _ = _ := by ring
  have hsplit : D.ricci x U V = D.ricci x V V + D.ricci x X V := by
    have hU : U = V + X := by dsimp only [V]; abel
    conv_lhs => rw [hU]
    simp only [ricci, ← curvatureTensor_bilinear_first_third_apply,
      map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  have habs : |D.ricci x U V| ≤ ((n : ℝ) * K + (r ^ 2)⁻¹) * w ^ 2 := by
    rw [hsplit]
    calc
      _ ≤ |D.ricci x V V| + |D.ricci x X V| := abs_add_le _ _
      _ ≤ (n : ℝ) * K * w ^ 2 + (r ^ 2)⁻¹ * w ^ 2 := add_le_add hdiag hsource
      _ = _ := by ring
  exact (abs_le.mp habs).1

theorem reference_connection_energy_le (D : LeviCivitaData g)
    (X : (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x)
    (x V : EuclideanSpace ℝ (Fin n)) {r s : ℝ}
    (hconnection : (∑ i, g.inner x
      (D.connection X x (g.orthonormalBasis x i))
      (D.connection X x (g.orthonormalBasis x i))) ≤ (s / r) ^ 2) :
    (∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
      (D.connection X x (g.orthonormalBasis x i))) ≤
      (r ^ 2)⁻¹ * (Real.sqrt (g.inner x V V + s ^ 2)) ^ 2 := by
  have hVV : 0 ≤ g.inner x V V := by
    by_cases hV : V = 0
    · simp [hV]
    · exact (g.pos x _ hV).le
  rw [Real.sq_sqrt (add_nonneg hVV (sq_nonneg s))]
  calc
    _ ≤ (s / r) ^ 2 := hconnection
    _ = (r ^ 2)⁻¹ * s ^ 2 := by rw [div_pow, div_eq_mul_inv]; ring
    _ ≤ (r ^ 2)⁻¹ * (g.inner x V V + s ^ 2) := by
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hVV) (by positivity)

end PoincareConjecture.LeviCivitaData
