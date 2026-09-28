import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarPullback
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarScaling
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Locality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T2Space N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

theorem scalar_ricciNormSq_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 n) y, g.inner y v w =
      h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w))
    {x : M} (hx : x ∈ U) :
    D'.scalarCurvature (f x) = D.scalarCurvature x ∧
      D'.ricciNormSq (f x) = D.ricciNormSq x := by
  obtain ⟨L, hL⟩ := hinv x hx
  apply (curvatureContractions_eq_of_metric_linearEquiv D D' x (f x) L.toLinearEquiv
    (fun v w => ?_) (fun v w a b => ?_)).2
  · rw [hmetric x hx, ← hL]
    rfl
  · rw [D.curvatureTensor_eq_of_local_isometry D' hU hf hmetric hx, ← hL]
    rfl

theorem scalar_evolution_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 n) y, g.inner y v w =
      h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w))
    {x : M} (hx : x ∈ U)
    (hscalar : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ D'.scalarCurvature (f x)) :
    D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x =
      D'.laplacian D'.scalarCurvature (f x) + 2 * D'.ricciNormSq (f x) := by
  have hid := fun y hy => scalar_ricciNormSq_eq_of_local_isometry D D' hU hf hinv hmetric
    (x := y) hy
  have heq : D.scalarCurvature =ᶠ[𝓝 x] D'.scalarCurvature ∘ f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hid y hy).1.symm
  rw [D.laplacian_eq_of_eventuallyEq heq,
    D.laplacian_comp_of_metric_pullback D' (hf.contMDiffAt (hU.mem_nhds hx))
      (eventually_of_mem (hU.mem_nhds hx) (fun y hy => hinv y hy))
      (eventually_of_mem (hU.mem_nhds hx) (fun y hy => hmetric y hy)) hscalar,
    (hid x hx).2]

theorem scalar_eq_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    {Q : ℝ} (hQ : 0 < Q)
    (hmetric : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 n) y,
      h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w) =
        Q * g.inner y v w) {x : M} (hx : x ∈ U) :
    D'.scalarCurvature (f x) = D.scalarCurvature x / Q := by
  let DQ := m01RescaledMetric_connection g D Q hQ
  have hm (y : M) (hy : y ∈ U) (v w : TangentSpace (𝓡 n) y) :
      (m01RescaledMetric g Q hQ).inner y v w =
        h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w) :=
    (m01RescaledMetric_inner g Q hQ y v w).trans (hmetric y hy v w).symm
  rw [(scalar_ricciNormSq_eq_of_local_isometry DQ D' hU hf hinv hm hx).1]
  exact M13.homothety_scalarCurvature_eq g (m01RescaledMetric g Q hQ)
    (Diffeomorph.refl (𝓡 n) M ∞) Q hQ (rescaledMetric_identity_homothety hQ) D DQ x

theorem scalar_evolution_eq_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    {Q : ℝ} (hQ : 0 < Q)
    (hmetric : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 n) y,
      h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w) =
        Q * g.inner y v w) {x : M} (hx : x ∈ U)
    (hscalar : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature)
    (hscalar' : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ D'.scalarCurvature (f x)) :
    D'.laplacian D'.scalarCurvature (f x) + 2 * D'.ricciNormSq (f x) =
      (D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x) / Q ^ 2 := by
  let DQ := m01RescaledMetric_connection g D Q hQ
  have hm (y : M) (hy : y ∈ U) (v w : TangentSpace (𝓡 n) y) :
      (m01RescaledMetric g Q hQ).inner y v w =
        h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w) :=
    (m01RescaledMetric_inner g Q hQ y v w).trans (hmetric y hy v w).symm
  rw [← scalar_evolution_eq_of_local_isometry DQ D' hU hf hinv hm hx hscalar']
  exact rescaled_scalar_evolution D hQ x hscalar

end PoincareConjecture.M44
