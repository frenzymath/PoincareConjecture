import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Geometry.SectionalNormalization

/-!
# Sectional curvature is independent of the basis of its plane

An alternating curvature form and the metric Gram determinant acquire
the same squared determinant under a change of two generators. Thus
a strict sectional bound holds on every nondegenerate basis of the
same plane. This is the linear algebra in Morgan--Tian, Claim 16.10,
pp. 374-375; see M44 derivation 46.
-/

set_option autoImplicit false

namespace PoincareMT.M44

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Changing two generators multiplies their Gram determinant by
the square of the coefficient determinant. Source: the tangent-plane
argument of Claim 16.10; M44 derivation 46. -/
theorem gram_linearCombination (u v : E) (a b c d : ℝ) :
    inner ℝ (a • u + b • v) (a • u + b • v) *
      inner ℝ (c • u + d • v) (c • u + d • v) -
        (inner ℝ (a • u + b • v) (c • u + d • v)) ^ 2 =
      (a * d - b * c) ^ 2 * (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2) := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm v u]
  ring

/-- Changing the two generators in both alternating pairs has the
same squared determinant as the Gram form. Source: Claim 16.10;
M44 derivation 46. -/
theorem curvature_linearCombination
    (R : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (u v : E) (a b c d : ℝ) :
    R (a • u + b • v) (c • u + d • v) (a • u + b • v) (c • u + d • v) =
      (a * d - b * c) ^ 2 * R u v u v := by
  have hzero1 (x y z : E) : R x x y z = 0 := by linarith only [hfirst x x y z]
  have hzero2 (x y z : E) : R x y z z = 0 := by linarith only [hlast x y z z]
  have hvu : R v u u v = -R u v u v := hfirst v u u v
  have huv : R u v v u = -R u v u v := hlast u v v u
  have hvu' : R v u v u = R u v u v := by rw [hfirst, huv, neg_neg]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hzero1, hzero2, hvu, huv, hvu']
  ring

/-- Every nondegenerate pair in a two-generator plane satisfies
the same strict lower sectional bound. Source: Claim 16.10;
M44 derivation 46. -/
theorem sectional_lower_of_mem_span_pair
    (R : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    {u v p q : E} {k : ℝ}
    (hlower : k * (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2) < R u v u v)
    (hp : p ∈ Submodule.span ℝ ({u, v} : Set E))
    (hq : q ∈ Submodule.span ℝ ({u, v} : Set E))
    (hgram : 0 < inner ℝ p p * inner ℝ q q - (inner ℝ p q) ^ 2) :
    k * (inner ℝ p p * inner ℝ q q - (inner ℝ p q) ^ 2) < R p q p q := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hq
  rw [gram_linearCombination] at hgram ⊢
  rw [curvature_linearCombination R hfirst hlast]
  have hdet : 0 < (a * d - b * c) ^ 2 := by
    apply lt_of_le_of_ne (sq_nonneg _)
    intro hz
    rw [← hz, zero_mul] at hgram
    exact (lt_irrefl _ hgram).elim
  have h := mul_lt_mul_of_pos_left hlower hdet
  nlinarith only [h]

end PoincareMT.M44
