import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Sectional








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma curvatureTensor_diagonal_of_constant_sectional (D : LeviCivitaData g)
    (x : M) (K : ℝ)
    (hsec : ∀ u v : TangentSpace (𝓡 n) x,
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        D.sectionalCurvature x u v = K)
    (u v : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v u v =
      K * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
  rw [D.curvatureTensor_diagonal_eq_sectional_mul_gram]
  by_cases hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 = 0
  · simp only [hgram, mul_zero]
  · rw [hsec u v hgram]

lemma curvatureTensor_radial_of_constant_sectional (D : LeviCivitaData g)
    (x : M) (K : ℝ)
    (hsec : ∀ u v : TangentSpace (𝓡 n) x,
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        D.sectionalCurvature x u v = K)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w v =
      K * (g.inner x u w * g.inner x v v - g.inner x u v * g.inner x w v) := by
  have h := D.curvatureTensor_diagonal_of_constant_sectional x K hsec (u + w) v
  have hu := D.curvatureTensor_diagonal_of_constant_sectional x K hsec u v
  have hw := D.curvatureTensor_diagonal_of_constant_sectional x K hsec w v
  have hsym := D.inner_radialCurvature_symm x v u w
  rw [g.symm x u] at hsym
  change D.curvatureTensor x u v w v = D.curvatureTensor x w v u v at hsym
  simp only [D.curvatureTensor_add_first, D.curvatureTensor_add_third,
    map_add, add_apply, g.symm x w u] at h
  nlinarith [hu, hw, hsym]



theorem curvatureTensor_of_constant_sectional (D : LeviCivitaData g)
    (x : M) (K : ℝ)
    (hsec : ∀ u v : TangentSpace (𝓡 n) x,
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        D.sectionalCurvature x u v = K)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z =
      K * (g.inner x u w * g.inner x v z - g.inner x v w * g.inner x u z) := by
  have h := D.three_curvatureTensor_eq_radial_polarization x u v z w
  simp only [D.curvatureTensor_radial_of_constant_sectional x K hsec,
    map_add, add_apply, g.symm x z v, g.symm x z u, g.symm x v u,
    g.symm x w u, g.symm x w v] at h
  nlinarith


theorem radialCurvature_of_constant_sectional (D : LeviCivitaData g)
    (x : M) (K : ℝ)
    (hsec : ∀ u v : TangentSpace (𝓡 n) x,
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        D.sectionalCurvature x u v = K)
    (v u : TangentSpace (𝓡 n) x) :
    D.radialCurvature x v u =
      K • (g.inner x v v • u - g.inner x u v • v) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro w
  change D.curvatureTensor x u v w v = g.inner x
    (K • (g.inner x v v • u - g.inner x u v • v)) w
  rw [D.curvatureTensor_radial_of_constant_sectional x K hsec]
  simp only [map_smul, smul_apply, map_sub, sub_apply, smul_eq_mul, g.symm x v w]
  ring

end PoincareConjecture.LeviCivitaData
