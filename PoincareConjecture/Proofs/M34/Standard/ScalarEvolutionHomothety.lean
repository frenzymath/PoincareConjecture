import PoincareConjecture.Proofs.M34.Standard.ScalarEvolutionHomothetyScaling
import PoincareConjecture.Proofs.M34.Standard.ScalarEvolutionHomothetyRicci
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.ScalarOperators.Locality
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.ScalarOperators.Scaling











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}



theorem laplacian_comp_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) {u : N → ℝ}
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u (f x)) :
    D.laplacian (u ∘ f) x = D'.laplacian u (f x) / Q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hb := g.mfderiv_bijective_of_pullback_eq (M13.scaleSmoothMetric h Q hQ) y
      (fun a b => (hmetric y hy a b).symm)
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) y) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) y
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f y)) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : N → Type _) (f y)
    exact ⟨(LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f y).toLinearMap
      hb).toContinuousLinearEquiv, rfl⟩
  have hm : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = (M13.scaleSmoothMetric h Q hQ).inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hmetric y hy
  have hlap := D.laplacian_comp_of_metric_pullback (M13.scaleLeviCivitaData D' Q hQ)
    ((hf x hx).contMDiffAt (hU.mem_nhds hx)) hinv hm hu
  exact hlap.trans (M13.scaleLeviCivitaData_laplacian D' hQ hu)

variable [T2Space N]



theorem laplacian_scalarCurvature_eq_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) :
    D.laplacian D.scalarCurvature x = D'.laplacian D'.scalarCurvature (f x) / Q ^ 2 := by
  have heq : D.scalarCurvature =ᶠ[𝓝 x]
      (fun y => Q⁻¹ * D'.scalarCurvature (f y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simpa only [div_eq_mul_inv, mul_comm] using
      D.scalarCurvature_eq_of_local_homothety D' hQ hU hf hmetric hy
  rw [D.laplacian_eq_of_eventuallyEq heq, D.laplacian_const_mul]
  have hlap := D.laplacian_comp_of_local_homothety D' hQ hU hf hmetric hx
    (M34.contMDiff_scalarCurvature D' (f x))
  change Q⁻¹ * D.laplacian (D'.scalarCurvature ∘ f) x = _
  rw [hlap]
  field_simp [hQ.ne']



theorem scalarEvolutionNumerator_eq_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) :
    D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x =
      (D'.laplacian D'.scalarCurvature (f x) + 2 * D'.ricciNormSq (f x)) / Q ^ 2 := by
  rw [D.laplacian_scalarCurvature_eq_of_local_homothety D' hQ hU hf hmetric hx,
    D.ricciNormSq_eq_of_local_homothety D' hQ hU hf hmetric hx]
  ring

end PoincareConjecture.LeviCivitaData
