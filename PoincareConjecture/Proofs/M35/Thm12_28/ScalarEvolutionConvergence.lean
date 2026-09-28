import PoincareConjecture.Proofs.M35.Thm12_28.ScalarLaplacianConvergence









set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Filter
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix.Norms.Elementwise

namespace PoincareConjecture.M35

local notation:max "E" n:max => EuclideanSpace ℝ (Fin n)



theorem ricciNormSq_eq_inverse_gram {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    D.ricciNormSq x = ∑ i, ∑ j, ∑ a, ∑ c,
      (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j *
        ((Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ a c *
          (D.ricci x (b i) (b a) * D.ricci x (b j) (b c))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B := M13.ricciLinear D x
  let e := g.orthonormalBasis x
  let C : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ :=
    ∑ a, (B.flip (e a)).smulRight (B.flip (e a))
  have hC (u v : TangentSpace (𝓡 n) x) : C u v = ∑ a, B u (e a) * B v (e a) := by
    simp only [C, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      smul_eq_mul, LinearMap.flip_apply]
  have hinner (i j : Fin n) : C (b i) (b j) = ∑ a, ∑ c,
      (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ a c *
        (D.ricci x (b i) (b a) * D.ricci x (b j) (b c)) := by
    rw [hC]
    exact bilinear_sum_basis_eq_inverse_gram ((B (b i)).smulRight (B (b j))) b e
  calc
    D.ricciNormSq x = ∑ a, C (e a) (e a) := by
      simp only [hC, pow_two, LeviCivitaData.ricciNormSq, B, e, M13.ricciLinear_apply]
    _ = ∑ i, ∑ j,
        (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j * C (b i) (b j) :=
      bilinear_sum_basis_eq_inverse_gram C b e
    _ = _ := by simp only [hinner, Finset.mul_sum]



theorem ricciNormSq_tendsto_of_metric_jets {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E n) (p : E n)
    (hjet : ∀ m ≤ 2, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => (Dseq k).ricciNormSq (pseq k)) atTop (𝓝 (D.ricciNormSq p)) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hI (i j : Fin n) :
      Tendsto (fun k => (Matrix.of (fun a c => (gseq k).inner (pseq k) (b a) (b c)))⁻¹ i j)
        atTop (𝓝 ((Matrix.of (fun a c => g.inner p (b a) (b c)))⁻¹ i j)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ (E n) ℝ).continuous.tendsto _).comp
      (inverseGram_jets_tendsto_of_metric_jets pseq p b i j 0
        (fun m hm => hjet m (by omega)))
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  have hR (u v : E n) : Tendsto (fun k => (Dseq k).ricci (pseq k) u v) atTop
      (𝓝 (D.ricci p u v)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ (E n) ℝ).continuous.tendsto _).comp
      (ricci_jets_tendsto_of_metric_jets Dseq D pseq p u v 0 hjet)
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  simp_rw [ricciNormSq_eq_inverse_gram _ _ b]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro a _
  apply tendsto_finsetSum
  intro c _
  exact (hI i j).mul ((hI a c).mul ((hR (b i) (b a)).mul (hR (b j) (b c))))



theorem scalar_evolution_tendsto_of_metric_jets {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E n) (p : E n)
    (hjet : ∀ m ≤ 4, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => (Dseq k).laplacian (Dseq k).scalarCurvature (pseq k) +
      2 * (Dseq k).ricciNormSq (pseq k)) atTop
      (𝓝 (D.laplacian D.scalarCurvature p + 2 * D.ricciNormSq p)) :=
  (scalar_laplacian_tendsto_of_metric_jets Dseq D pseq p hjet).add
    (tendsto_const_nhds.mul (ricciNormSq_tendsto_of_metric_jets Dseq D pseq p
      (fun m hm => hjet m (by omega))))

end PoincareConjecture.M35
