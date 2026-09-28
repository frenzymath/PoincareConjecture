import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bilinear
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Calculus

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {g : RiemannianMetric n M}

theorem ricci_eq_sum_frame (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    D.ricci x v w =
      ∑ i, ∑ j, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j) *
        g.inner x (g.orthonormalBasis x i) v *
        g.inner x (g.orthonormalBasis x j) w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let B := ∑ a, D.curvatureTensor_bilinear_first_third x (b a) (b a)
  have hB (u z : TangentSpace (𝓡 n) x) : B u z = D.ricci x u z := by
    simp [B, ricci, b, LinearMap.sum_apply]
  rw [← hB v w]
  conv_lhs => rw [← b.sum_repr' v, ← b.sum_repr' w]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hB]
  change inner ℝ (b j) w * (inner ℝ (b i) v * D.ricci x (b i) (b j)) =
    D.ricci x (b i) (b j) * inner ℝ (b i) v * inner ℝ (b j) w
  ring

theorem ricci_bounds_of_nonnegative_curvatureOperator
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hoperator : D.NonnegativeCurvatureOperator x)
    (v : TangentSpace (𝓡 n) x) :
    0 ≤ D.ricci x v v ∧ D.ricci x v v ≤ D.scalarCurvature x * g.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let R := fun i j k l ↦ D.curvatureTensor x (b i) (b j) (b k) (b l)
  let Ric := fun i j ↦ D.ricci x (b i) (b j)
  have hsym := hD.2.2.2.1
  have hlast : ∀ i j k l, R i j k l = -R i j l k :=
    fun i j k l ↦ (hsym x (b i) (b j) (b k) (b l)).1
  have hpair : ∀ i j k l, R i j k l = R k l i j :=
    fun i j k l ↦ (hsym x (b i) (b j) (b k) (b l)).2.1
  have hfirst : ∀ i j k l, R i j k l = -R j i k l := by
    intro i j k l
    rw [hpair i j k l, hlast k l i j, hpair k l j i]
  have hop : ∀ A : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ,
      (∀ i j, A i j = -A j i) →
      0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * A i j * A k l := by
    intro A hA
    simpa only [curvatureOperatorQuadratic, R, b, mul_comm, mul_left_comm,
      mul_assoc] using hoperator A hA
  have hb := Poincare.Geometry.Curvature.Operator.ricci_bounds_of_nonnegative_operator
    R Ric hfirst hlast (fun _ _ ↦ rfl) (fun i ↦ inner ℝ (b i) v) hop
  have hnorm : (∑ i, (inner ℝ (b i) v) ^ 2) = g.inner x v v := by
    rw [b.sum_sq_inner_right]
    exact (real_inner_self_eq_norm_sq v).symm
  have hcoord := D.ricci_eq_sum_frame x v v
  change D.ricci x v v = ∑ i, ∑ j, Ric i j * inner ℝ (b i) v *
    inner ℝ (b j) v at hcoord
  rw [← hcoord, hnorm] at hb
  exact hb

end PoincareConjecture.LeviCivitaData
