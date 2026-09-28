import PoincareConjecture.Proofs.M34.Standard.LocalHomothetyCurvature

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N] [T2Space N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

theorem ricci_eq_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) (u v : TangentSpace (𝓡 n) x) :
    D.ricci x u v = D'.ricci (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v) := by
  have hlocal := D.ricci_eq_of_local_isometry
    (M13.scaleLeviCivitaData D' Q hQ) hU hf hmetric hx u v
  have hs := M13.homothety_ricci_eq h (M13.scaleSmoothMetric h Q hQ)
    (Diffeomorph.refl (𝓡 n) N ∞) Q hQ (M13.identity_metricHomothety h Q hQ)
    D' (M13.scaleLeviCivitaData D' Q hQ) (f x)
    (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v)
  simp only [Diffeomorph.coe_refl, mfderiv_id, id_eq] at hs
  exact hlocal.trans hs

theorem ricciNormSq_eq_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) :
    D.ricciNormSq x = D'.ricciNormSq (f x) / Q ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let L : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
      (g.mfderiv_bijective_of_pullback_eq (M13.scaleSmoothMetric h Q hQ) x
        (fun a b => (hmetric x hx a b).symm))
  let e := L.trans (LinearEquiv.smulOfNeZero ℝ (TangentSpace (𝓡 n) (f x))
    (Real.sqrt Q) (Real.sqrt_pos.mpr hQ).ne')
  have he (u v : TangentSpace (𝓡 n) x) : inner ℝ (e u) (e v) = inner ℝ u v := by
    change h.inner (f x) (Real.sqrt Q • mfderiv (𝓡 n) (𝓡 n) f x u)
      (Real.sqrt Q • mfderiv (𝓡 n) (𝓡 n) f x v) = g.inner x u v
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, Real.mul_self_sqrt hQ.le, ← hmetric x hx]
  let e' := e.isometryOfInner he
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f x)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) (f x)
  have hricci (u v : TangentSpace (𝓡 n) x) :
      D'.ricci (f x) (e' u) (e' v) = Q * D.ricci x u v := by
    change M13.ricciLinear D' (f x)
      (Real.sqrt Q • mfderiv (𝓡 n) (𝓡 n) f x u)
      (Real.sqrt Q • mfderiv (𝓡 n) (𝓡 n) f x v) = _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, M13.ricciLinear_apply]
    rw [← mul_assoc, Real.mul_self_sqrt hQ.le,
      ← D.ricci_eq_of_local_homothety D' hQ hU hf hmetric hx]
  have ht := M13.sum_sq_bilinear_basis_eq (M13.ricciLinear D' (f x))
    ((g.orthonormalBasis x).map e') (h.orthonormalBasis (f x))
  change (∑ i, ∑ j, (D'.ricci (f x) (e' (g.orthonormalBasis x i))
    (e' (g.orthonormalBasis x j))) ^ 2) = D'.ricciNormSq (f x) at ht
  simp only [hricci, mul_pow, ← Finset.mul_sum] at ht
  change Q ^ 2 * D.ricciNormSq x = D'.ricciNormSq (f x) at ht
  apply (eq_div_iff (pow_ne_zero 2 hQ.ne')).mpr
  exact (mul_comm _ _).trans ht

end PoincareConjecture.LeviCivitaData
