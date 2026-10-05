import PoincareLib.Geometry.RicciFlow.Area.MinimalSphere.ThreeDimensionalTrace
import PoincareLib.Geometry.RicciFlow.Area.FixedMap.RicciQuadratic

/-!
# Ricci trace on a conformal two-plane

Morgan-Tian Claim 18.12, printed pp. 426-427, and Hamilton (1999),
Section 11, printed p. 718. Normalizing the two vectors gives the
curvature contribution with exactly one conformal factor in the denominator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

omit [T2Space M] in
/-- Scaling the two vectors in a sectional-curvature numerator.
Source: MT Claim 18.12, pp. 426-427, curvature contraction. -/
theorem m60Curvature_plane_smul (D : LeviCivitaData g) (x : M)
    (c d : ℝ) (u v : TangentSpace (𝓡 3) x) :
    D.curvatureTensor x (c • u) (d • v) (c • u) (d • v) =
      c ^ 2 * d ^ 2 * D.curvatureTensor x u v u v := by
  have hfirst (a b : ℝ) (w y z t : TangentSpace (𝓡 3) x) :
      D.curvatureTensor x (a • w) y (b • z) t =
        a * b * D.curvatureTensor x w y z t := by
    change D.curvatureTensor_bilinear_first_third x y t (a • w) (b • z) =
      a * b * D.curvatureTensor_bilinear_first_third x y t w z
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hswap (w z : TangentSpace (𝓡 3) x) :
      D.curvatureTensor x w z w z = D.curvatureTensor x z w z w := by
    rw [M04.curvatureTensor_swap_first, M04.curvatureTensor_swap_last, neg_neg]
  rw [hfirst, hswap u (d • v), hfirst, hswap v u]
  ring

/-- The actual Ricci trace on equal-length orthogonal vectors in dimension
three. Source: MT Claim 18.12, pp. 426-427; Hamilton (1999), p. 718. -/
theorem m60Ricci_plane_trace_equal_length (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) (u v : TangentSpace (𝓡 3) x)
    {a : ℝ} (ha : 0 < a) (hu : g.inner x u u = a)
    (hv : g.inner x v v = a) (huv : g.inner x u v = 0) :
    D.ricci x u u + D.ricci x v v =
      (D.scalarCurvature x / 2) * a + D.curvatureTensor x u v u v / a := by
  let c : ℝ := (Real.sqrt a)⁻¹
  have hc : c * c = a⁻¹ := by
    dsimp [c]
    rw [← mul_inv_rev, ← pow_two, Real.sq_sqrt ha.le]
  have hunit (w : TangentSpace (𝓡 3) x) (hw : g.inner x w w = a) :
      g.inner x (c • w) (c • w) = 1 := by
    simp only [map_smul, smul_apply, smul_eq_mul, hw]
    rw [← mul_assoc, hc, inv_mul_cancel₀ ha.ne']
  have horth : g.inner x (c • u) (c • v) = 0 := by
    simp only [map_smul, smul_apply, smul_eq_mul, huv, mul_zero]
  have htrace := m60Ricci_plane_trace D hD x (c • u) (c • v)
    (hunit u hu) (hunit v hv) horth
  obtain ⟨B, hB⟩ := m60Ricci_exists_bilinear D hD x
  have hric (w : TangentSpace (𝓡 3) x) :
      D.ricci x (c • w) (c • w) = a⁻¹ * D.ricci x w w := by
    rw [← hB, ← hB]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, hc]
  rw [hric, hric, m60Curvature_plane_smul, pow_two, hc] at htrace
  field_simp at htrace ⊢
  nlinarith

end PoincareMT
