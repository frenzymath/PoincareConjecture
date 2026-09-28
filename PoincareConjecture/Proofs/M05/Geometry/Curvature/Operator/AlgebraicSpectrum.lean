import PoincareConjecture.Proofs.M05.Geometry.Curvature.Operator.Sectional
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Spectrum
import PoincareConjecture.Proofs.M05.LinearAlgebra.CrossProduct.Orthonormal

open scoped BigOperators Matrix

namespace Poincare.Geometry.Curvature.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem repr_dotProduct (b : OrthonormalBasis (Fin 3) ℝ E) (u v : E) :
    dotProduct (b.repr u) (b.repr v) = inner ℝ u v := by
  rw [← b.repr.inner_map_map u v, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, dotProduct_comm]

theorem multilinear_plane_eq_curvatureOperator_rayleigh
    (A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (b : OrthonormalBasis (Fin 3) ℝ E)
    (hfirst : ∀ u v w z, A ![u, v, w, z] = -A ![v, u, w, z])
    (hlast : ∀ u v w z, A ![u, v, w, z] = -A ![u, v, z, w]) (u v : E) :
    A ![u, v, u, v] =
      inner ℝ (WithLp.toLp 2 (crossProduct (b.repr u) (b.repr v)))
        (curvatureOperator (fun i j k l => A ![b i, b j, b k, b l])
          (WithLp.toLp 2 (crossProduct (b.repr u) (b.repr v)))) := by
  have hexp := multilinear_plane_expansion A b (b.repr u) (b.repr v)
  rw [b.sum_repr u, b.sum_repr v] at hexp
  rw [hexp, curvatureOperator_rayleigh]
  exact curvature_contraction_eq_crossProduct_rayleigh
    (fun i j k l => A ![b i, b j, b k, b l])
    (fun i j k l => hfirst (b i) (b j) (b k) (b l))
    (fun i j k l => hlast (b i) (b j) (b k) (b l)) (b.repr u) (b.repr v)

theorem sectional_inf_eq_least_eigenvalue
    (A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (b : OrthonormalBasis (Fin 3) ℝ E)
    (hfirst : ∀ u v w z, A ![u, v, w, z] = -A ![v, u, w, z])
    (hlast : ∀ u v w z, A ![u, v, w, z] = -A ![u, v, z, w])
    (hpair : ∀ u v w z, A ![u, v, w, z] = A ![w, z, u, v]) :
    sInf {q : ℝ | ∃ u v : E,
        inner ℝ u u = 1 ∧ inner ℝ v v = 1 ∧ inner ℝ u v = 0 ∧
          q = A ![u, v, u, v]} =
      (curvatureOperator_isSymmetric (fun i j k l => A ![b i, b j, b k, b l])
        (fun i j k l => hpair (b i) (b j) (b k) (b l))).eigenvalues
          (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) 2 := by
  let R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
    fun i j k l => A ![b i, b j, b k, b l]
  have hRpair : ∀ i j k l, R i j k l = R k l i j :=
    fun i j k l => hpair (b i) (b j) (b k) (b l)
  let T := curvatureOperator R
  have hT : T.IsSymmetric := curvatureOperator_isSymmetric R hRpair
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  let e := hT.eigenvalues hn
  let S : Set ℝ := {q | ∃ u v : E,
    inner ℝ u u = 1 ∧ inner ℝ v v = 1 ∧ inner ℝ u v = 0 ∧
      q = A ![u, v, u, v]}
  have hplane (u v : E) : A ![u, v, u, v] =
      inner ℝ (WithLp.toLp 2 (crossProduct (b.repr u) (b.repr v)))
        (T (WithLp.toLp 2 (crossProduct (b.repr u) (b.repr v)))) :=
    multilinear_plane_eq_curvatureOperator_rayleigh A b hfirst hlast u v
  have hlower : ∀ q ∈ S, e 2 ≤ q := by
    rintro q ⟨u, v, hu, hv, huv, rfl⟩
    rw [hplane]
    apply Poincare.symmetric_three_rayleigh_ge_least hT hn
    exact Poincare.LinearAlgebra.norm_crossProduct_of_orthonormal
      ((repr_dotProduct b u u).trans hu) ((repr_dotProduct b v v).trans hv)
      ((repr_dotProduct b u v).trans huv)
  have hattained : e 2 ∈ S := by
    obtain ⟨w, hw, hvalue⟩ := Poincare.symmetric_three_rayleigh_attains_least hT hn
    obtain ⟨u, v, hu, hv, huv, hcross⟩ :=
      Poincare.LinearAlgebra.exists_orthonormal_crossProduct_of_norm_eq_one w hw
    have hcross' : (WithLp.toLp 2 (crossProduct u v) : EuclideanSpace ℝ (Fin 3)) = w := by
      exact congrArg (WithLp.toLp 2) hcross
    refine ⟨b.repr.symm u, b.repr.symm v, ?_, ?_, ?_, ?_⟩
    · rw [b.repr.symm.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      exact hu
    · rw [b.repr.symm.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      exact hv
    · rw [b.repr.symm.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct,
        star_trivial, dotProduct_comm]
      exact huv
    · rw [hplane, b.repr.apply_symm_apply, b.repr.apply_symm_apply, hcross']
      exact hvalue.symm
  have hnonempty : S.Nonempty := ⟨e 2, hattained⟩
  have hbounded : BddBelow S := ⟨e 2, hlower⟩
  exact le_antisymm (csInf_le hbounded hattained) (le_csInf hnonempty hlower)

theorem algebraic_three_spectrum
    (A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (b : OrthonormalBasis (Fin 3) ℝ E)
    (hfirst : ∀ u v w z, A ![u, v, w, z] = -A ![v, u, w, z])
    (hlast : ∀ u v w z, A ![u, v, w, z] = -A ![u, v, z, w])
    (hpair : ∀ u v w z, A ![u, v, w, z] = A ![w, z, u, v]) :
    ∃ k₁ k₂ k₃ : ℝ,
      k₁ ≥ k₂ ∧ k₂ ≥ k₃ ∧
      sInf {q : ℝ | ∃ u v : E,
        inner ℝ u u = 1 ∧ inner ℝ v v = 1 ∧ inner ℝ u v = 0 ∧
          q = A ![u, v, u, v]} = k₃ ∧
      (∑ i, ∑ j, A ![b i, b j, b i, b j]) = 2 * (k₁ + k₂ + k₃) ∧
      (∑ i, ∑ j, ∑ k, ∑ l, A ![b i, b j, b k, b l] ^ 2) =
        4 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) := by
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
  refine ⟨e 0, e 1, e 2,
    hT.eigenvalues_antitone hn (by omega),
    hT.eigenvalues_antitone hn (by omega), hinf, ?_, ?_⟩
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
