import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ConformalVariation









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m65PlaneRicciTraceDensity_eq_sum_of_conformal
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (f : LoopPlane → M) (z : LoopPlane) (c : ℝ)
    (hconf : m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    m65PlaneRicciTraceDensity D f z = ∑ i : Fin 2, D.ricci (f z)
      (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  let e : Fin 2 → TangentSpace (𝓡 n) (f z) := fun i =>
    mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let R : Matrix (Fin 2) (Fin 2) ℝ := fun i j => D.ricci (f z) (e i) (e j)
  have hdet : (m60AreaGram g f z).det = c ^ 2 := by
    simp only [hconf, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hdensity := m65AreaDensity_eq_of_conformal g f z c hconf
  change (if (m60AreaGram g f z).det = 0 then 0
    else Matrix.trace ((m60AreaGram g f z)⁻¹ * R) * m60AreaDensity g f z) =
      ∑ i, D.ricci (f z) (e i) (e i)
  by_cases hc : c = 0
  · have he (i : Fin 2) : e i = 0 := by
      by_contra hne
      have hdiag := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G i i) hconf
      have hzero : g.inner (f z) (e i) (e i) = 0 := by
        simpa only [Matrix.smul_apply, hc, zero_smul, m60AreaGram, e] using hdiag
      exact (g.pos (f z) (e i) hne).ne' hzero
    simp only [hdet, hc, zero_pow two_ne_zero, if_true, he, LeviCivitaData.ricci,
      LeviCivitaData.curvatureTensor, map_zero, Finset.sum_const_zero]
  · let : Invertible c := invertibleOfNonzero hc
    have htrace : Matrix.trace R = ∑ i : Fin 2, D.ricci (f z) (e i) (e i) := rfl
    rw [if_neg (by rw [hdet]; exact pow_ne_zero 2 hc), hdensity, hconf,
      Matrix.inv_smul (1 : Matrix (Fin 2) (Fin 2) ℝ) c (by simp), inv_one,
      smul_mul_assoc, Matrix.one_mul, Matrix.trace_smul, htrace, invOf_eq_inv, smul_eq_mul]
    field_simp

end PoincareConjecture
