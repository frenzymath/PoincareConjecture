import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarJet
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.TraceRegularity
import PoincareConjecture.Statements.M44Providers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M44

theorem scalar_smooth_of_predecessors
    (P : M44CapPersistencePredecessors.{u}) {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M} (D : LeviCivitaData g) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  have hD := P.curvature.tensor_calculus n M g D
  have hs := (hD.2.1.tensorTrace (g := g)).2 univ isOpen_univ
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  change ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞
    (fun x => ∑ i, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x i))
  simpa [contMDiffOn_univ, RiemannianMetric.tensorTrace, LeviCivitaData.scalarCurvature,
    LeviCivitaData.ricciEvaluation] using hs

section Contractions

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T2Space N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

theorem curvatureContractions_eq_of_metric_linearEquiv
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) (y : N)
    (L : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) y)
    (hmetric : ∀ v w, h.inner y (L v) (L w) = g.inner x v w)
    (hcurv : ∀ v w a b, D'.curvatureTensor y (L v) (L w) (L a) (L b) =
      D.curvatureTensor x v w a b) :
    (∀ v w, D'.ricci y (L v) (L w) = D.ricci x v w) ∧
      D'.scalarCurvature y = D.scalarCurvature x ∧ D'.ricciNormSq y = D.ricciNormSq x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) y) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    infer_instance
  let e := L.isometryOfInner hmetric
  let b := g.orthonormalBasis x
  have hRicci (v w : TangentSpace (𝓡 n) x) :
      D'.ricci y (L v) (L w) = D.ricci x v w := by
    rw [M13.ricci_eq_sum_basis D' y (b.map e)]
    change (∑ i, D'.curvatureTensor y (L v) (L (b i)) (L w) (L (b i))) = _
    simp only [hcurv]
    rfl
  refine ⟨hRicci, ?_, ?_⟩
  · rw [M13.scalarCurvature_eq_sum_basis D' y (b.map e)]
    change (∑ i, D'.ricci y (L (b i)) (L (b i))) = _
    simp only [hRicci]
    rfl
  · have hn := M13.sum_sq_bilinear_basis_eq (M13.ricciLinear D' y)
      (h.orthonormalBasis y) (b.map e)
    have hn0 := M13.sum_sq_bilinear_basis_eq (M13.ricciLinear D x)
      (g.orthonormalBasis x) b
    change D'.ricciNormSq y = ∑ i, ∑ j, D'.ricci y (L (b i)) (L (b j)) ^ 2 at hn
    change D.ricciNormSq x = ∑ i, ∑ j, D.ricci x (b i) (b j) ^ 2 at hn0
    calc
      D'.ricciNormSq y = ∑ i, ∑ j, D'.ricci y (L (b i)) (L (b j)) ^ 2 := hn
      _ = ∑ i, ∑ j, D.ricci x (b i) (b j) ^ 2 := by simp only [hRicci]
      _ = D.ricciNormSq x := hn0.symm

end Contractions

section EuclideanSource

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

variable {n : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (E n) N]
  [IsManifold (𝓡 n) ∞ N] [T2Space N]
  {g : RiemannianMetric n (E n)} {h : RiemannianMetric n N}

theorem scalar_ricciNormSq_eq_of_metric_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : E n → N} {x : E n}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : E n, g.inner y v w = h.inner (f y)
      (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w)) :
    D'.scalarCurvature (f x) = D.scalarCurvature x ∧
      D'.ricciNormSq (f x) = D.ricciNormSq x := by
  obtain ⟨e, he⟩ := hinv.self_of_nhds
  apply (curvatureContractions_eq_of_metric_linearEquiv D D' x (f x) e.toLinearEquiv
    (fun v w => ?_) (fun v w a b => ?_)).2
  · rw [hmetric.self_of_nhds, ← he]
    rfl
  · rw [D.curvatureTensor_eq_pullback_euclidean D' hf hinv hmetric, ← he]
    rfl

theorem scalar_evolution_eq_of_metric_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : E n → N} {U : Set (E n)}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = h.inner (f y)
      (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w))
    {x : E n} (hx : x ∈ U)
    (hscalar : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ D'.scalarCurvature (f x)) :
    D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x =
      D'.laplacian D'.scalarCurvature (f x) + 2 * D'.ricciNormSq (f x) := by
  have hid (y : E n) (hy : y ∈ U) :=
    scalar_ricciNormSq_eq_of_metric_pullback D D' (hf.contMDiffAt (hU.mem_nhds hy))
      (Filter.eventually_of_mem (hU.mem_nhds hy) (fun z hz => hinv z hz))
      (Filter.eventually_of_mem (hU.mem_nhds hy) (fun z hz => hmetric z hz))
  have heq : D.scalarCurvature =ᶠ[𝓝 x] D'.scalarCurvature ∘ f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hid y hy).1.symm
  have hcomp : ContDiffAt ℝ ∞ (D'.scalarCurvature ∘ f) x :=
    contMDiffAt_iff_contDiffAt.mp (hscalar.comp x (hf.contMDiffAt (hU.mem_nhds hx)))
  have hlap : D.laplacian D.scalarCurvature x =
      D.laplacian (D'.scalarCurvature ∘ f) x := by
    rw [D.laplacian_eq_sum_fderiv_sub_christoffel (contDiff_scalarCurvature D).contDiffAt,
      D.laplacian_eq_sum_fderiv_sub_christoffel hcomp, heq.fderiv_eq,
      (heq.fderiv (𝕜 := ℝ)).fderiv_eq]
  rw [hlap, D.laplacian_comp_of_metric_pullback D'
    (hf.contMDiffAt (hU.mem_nhds hx))
    (Filter.eventually_of_mem (hU.mem_nhds hx) (fun z hz => hinv z hz))
    (Filter.eventually_of_mem (hU.mem_nhds hx) (fun z hz => hmetric z hz)) hscalar,
    (hid x hx).2]

end EuclideanSource

end PoincareConjecture.M44
