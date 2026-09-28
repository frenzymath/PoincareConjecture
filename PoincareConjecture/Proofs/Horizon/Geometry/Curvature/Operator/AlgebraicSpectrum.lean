import PoincareConjecture.Proofs.M05.Geometry.Curvature.Operator.AlgebraicSpectrum
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.Spectrum
import PoincareConjecture.Proofs.Horizon.LinearAlgebra.CrossProduct.Orthonormal

open scoped BigOperators Matrix

namespace Poincare.Geometry.Curvature.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem repr_dotProduct (b : OrthonormalBasis (Fin 3) ℝ E) (u v : E) :
    dotProduct (b.repr u) (b.repr v) = inner ℝ u v := by
  rw [← b.repr.inner_map_map u v, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, dotProduct_comm]

theorem crossProduct_repr_inner (b : OrthonormalBasis (Fin 3) ℝ E) (u v w z : E) :
    inner ℝ (WithLp.toLp 2 (crossProduct (b.repr u) (b.repr v)) :
        EuclideanSpace ℝ (Fin 3))
      (WithLp.toLp 2 (crossProduct (b.repr w) (b.repr z))) =
      inner ℝ u w * inner ℝ v z - inner ℝ u z * inner ℝ v w := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  exact (cross_dot_cross _ _ _ _).trans (by simp only [repr_dotProduct])

theorem exists_orthonormal_crossProduct_repr (b : OrthonormalBasis (Fin 3) ℝ E)
    (a : EuclideanSpace ℝ (Fin 3)) (ha : ‖a‖ = 1) :
    ∃ u v : E, inner ℝ u u = 1 ∧ inner ℝ v v = 1 ∧ inner ℝ u v = 0 ∧
      (WithLp.toLp 2 (crossProduct (b.repr u) (b.repr v)) :
        EuclideanSpace ℝ (Fin 3)) = a := by
  obtain ⟨u, v, hu, hv, huv, hcross⟩ :=
    Poincare.LinearAlgebra.exists_orthonormal_crossProduct_of_norm_eq_one a ha
  refine ⟨b.repr.symm u, b.repr.symm v, ?_, ?_, ?_, ?_⟩
  · rw [b.repr.symm.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact hu
  · rw [b.repr.symm.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact hv
  · rw [b.repr.symm.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, dotProduct_comm]
    exact huv
  · rw [b.repr.apply_symm_apply, b.repr.apply_symm_apply]
    exact congrArg (WithLp.toLp 2) hcross

theorem multilinear_eq_curvatureOperator_pairing
    (A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (b : OrthonormalBasis (Fin 3) ℝ E)
    (hfirst : ∀ u v w z, A ![u, v, w, z] = -A ![v, u, w, z])
    (hlast : ∀ u v w z, A ![u, v, w, z] = -A ![u, v, z, w]) (u v w z : E) :
    A ![u, v, w, z] =
      inner ℝ (WithLp.toLp 2 (crossProduct (b.repr u) (b.repr v)))
        (curvatureOperator (fun i j k l => A ![b i, b j, b k, b l])
          (WithLp.toLp 2 (crossProduct (b.repr w) (b.repr z)))) := by
  have hexp := multilinear_curvature_expansion A b (b.repr u) (b.repr v)
    (b.repr w) (b.repr z)
  rw [b.sum_repr u, b.sum_repr v, b.sum_repr w, b.sum_repr z] at hexp
  rw [hexp]
  have hcoords := curvature_contraction_eq_crossProduct_pairing
    (fun i j k l => A ![b i, b j, b k, b l])
    (fun i j k l => hfirst (b i) (b j) (b k) (b l))
    (fun i j k l => hlast (b i) (b j) (b k) (b l))
    (b.repr u) (b.repr v) (b.repr w) (b.repr z)
  rw [hcoords]
  simp only [curvatureOperator, Matrix.toLpLin_apply,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  exact dotProduct_comm _ _

theorem algebraic_three_operator_spectrum
    (A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (b : OrthonormalBasis (Fin 3) ℝ E)
    (hfirst : ∀ u v w z, A ![u, v, w, z] = -A ![v, u, w, z])
    (hlast : ∀ u v w z, A ![u, v, w, z] = -A ![u, v, z, w])
    (hpair : ∀ u v w z, A ![u, v, w, z] = A ![w, z, u, v]) :
    let T := curvatureOperator (fun i j k l => A ![b i, b j, b k, b l])
    ∃ k : Fin 3 → ℝ,
    ∃ e : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)),
      Antitone k ∧ (∀ i, T (e i) = k i • e i) ∧
      sInf {q : ℝ | ∃ u v : E,
        inner ℝ u u = 1 ∧ inner ℝ v v = 1 ∧ inner ℝ u v = 0 ∧
          q = A ![u, v, u, v]} = k 2 ∧
      (∑ i, ∑ j, A ![b i, b j, b i, b j]) = 2 * (k 0 + k 1 + k 2) ∧
      (∑ i, ∑ j, ∑ k, ∑ l, A ![b i, b j, b k, b l] ^ 2) =
        4 * (k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2) := by
  let R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
    fun i j k l => A ![b i, b j, b k, b l]
  have hRfirst : ∀ i j k l, R i j k l = -R j i k l :=
    fun i j k l => hfirst (b i) (b j) (b k) (b l)
  have hRlast : ∀ i j k l, R i j k l = -R i j l k :=
    fun i j k l => hlast (b i) (b j) (b k) (b l)
  have hRpair : ∀ i j k l, R i j k l = R k l i j :=
    fun i j k l => hpair (b i) (b j) (b k) (b l)
  let T := curvatureOperator R
  have hT : T.IsSymmetric := curvatureOperator_isSymmetric R hRpair
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  let e := hT.eigenvalues hn
  have hinf := sectional_inf_eq_least_eigenvalue A b hfirst hlast hpair
  refine ⟨e, hT.eigenvectorBasis hn, hT.eigenvalues_antitone hn,
    hT.apply_eigenvectorBasis hn, hinf, ?_, ?_⟩
  · change (∑ i, ∑ j, R i j i j) = _
    rw [curvatureOperator_scalar_identity R hRfirst hRlast]
    change 2 * LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3)) T = _
    rw [hT.trace_eq_sum_eigenvalues hn]
    simp [e, Fin.sum_univ_succ]
    ring
  · change (∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2) = _
    rw [curvatureOperator_normSq_identity R hRfirst hRlast hRpair
      (hT.eigenvectorBasis hn)]
    change 4 * (∑ i, ‖T (hT.eigenvectorBasis hn i)‖ ^ 2) = _
    rw [Poincare.symmetric_eigenbasis_energy hT hn]
    simp [e, Fin.sum_univ_succ]
    ring

end Poincare.Geometry.Curvature.Operator
