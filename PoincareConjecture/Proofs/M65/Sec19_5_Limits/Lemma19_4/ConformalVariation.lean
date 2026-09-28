import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.AmbientDensityVariation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m65AreaDensity_eq_of_conformal (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) (c : ℝ)
    (hconf : m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    m60AreaDensity g f z = c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdiag := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G 0 0) hconf
  have hc : 0 ≤ c := by
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hdiag
    rw [← hdiag]
    exact real_inner_self_nonneg (x :=
      mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
  have hdet : (m60AreaGram g f z).det = c ^ 2 := by
    simp only [hconf, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  simp only [m60AreaDensity, hdet, max_eq_right (sq_nonneg c), Real.sqrt_sq hc]

variable {a b : ℝ} (F : RicciFlow n M (Icc a b))

theorem m65PlaneMotionDensity_eq_sum_of_conformal
    (u : ℝ → LoopPlane → M) (t : ℝ) (z : LoopPlane) (c : ℝ)
    (hconf : m60AreaGram (F.metric t) (u t) z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    m65PlaneMotionDensity F u t z =
      ∑ i : Fin 2, (F.metric t).inner (u t z)
        (rampHorizontalCovariantDerivative (F.connection t) (fun s => u s z)
          (fun s => mfderiv (𝓡 2) (𝓡 n) (u s) z
            (EuclideanSpace.basisFun (Fin 2) ℝ i)) t)
        (mfderiv (𝓡 2) (𝓡 n) (u t) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let e : Fin 2 → TangentSpace (𝓡 n) (u t z) := fun i =>
    mfderiv (𝓡 2) (𝓡 n) (u t) z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let A : Fin 2 → TangentSpace (𝓡 n) (u t z) := fun i =>
    rampHorizontalCovariantDerivative (F.connection t) (fun s => u s z)
      (fun s => mfderiv (𝓡 2) (𝓡 n) (u s) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) t
  let B : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    (F.metric t).inner (u t z) (A i) (e j) + (F.metric t).inner (u t z) (e i) (A j)
  have hdet : (m60AreaGram (F.metric t) (u t) z).det = c ^ 2 := by
    simp only [hconf, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hdensity := m65AreaDensity_eq_of_conformal (F.metric t) (u t) z c hconf
  change (if (m60AreaGram (F.metric t) (u t) z).det = 0 then 0
    else (1 / 2 : ℝ) * Matrix.trace ((m60AreaGram (F.metric t) (u t) z)⁻¹ * B) *
      m60AreaDensity (F.metric t) (u t) z) = ∑ i, (F.metric t).inner (u t z) (A i) (e i)
  by_cases hc : c = 0
  · have he (i : Fin 2) : e i = 0 := by
      by_contra hne
      have hdiag := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G i i) hconf
      have hzero : (F.metric t).inner (u t z) (e i) (e i) = 0 := by
        simpa only [Matrix.smul_apply, hc, zero_smul, m60AreaGram, e] using hdiag
      exact ((F.metric t).pos (u t z) (e i) hne).ne' hzero
    simp only [hdet, hc, zero_pow two_ne_zero, if_true, he, map_zero,
      Finset.sum_const_zero]
  · let : Invertible c := invertibleOfNonzero hc
    have htrace : Matrix.trace B = 2 * ∑ i : Fin 2, (F.metric t).inner (u t z) (A i) (e i) := by
      have hsymm (i : Fin 2) :
          (F.metric t).inner (u t z) (e i) (A i) = (F.metric t).inner (u t z) (A i) (e i) :=
        real_inner_comm (A i) (e i)
      simp only [Matrix.trace, Fin.sum_univ_two]
      change B 0 0 + B 1 1 = 2 *
        ((F.metric t).inner (u t z) (A 0) (e 0) + (F.metric t).inner (u t z) (A 1) (e 1))
      dsimp only [B]
      rw [hsymm 0, hsymm 1]
      ring
    rw [if_neg (by rw [hdet]; exact pow_ne_zero 2 hc), hdensity, hconf,
      Matrix.inv_smul (1 : Matrix (Fin 2) (Fin 2) ℝ) c (by simp),
      inv_one, smul_mul_assoc, Matrix.one_mul,
      Matrix.trace_smul, htrace, invOf_eq_inv, smul_eq_mul]
    field_simp

end PoincareConjecture
