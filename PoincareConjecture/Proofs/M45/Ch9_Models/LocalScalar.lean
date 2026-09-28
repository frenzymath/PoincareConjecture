import PoincareConjecture.Definitions.M45ModelAnalytics
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M13.BasisContractions
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Locality
import PoincareConjecture.Proofs.M04.RicciRegularity
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.TraceRegularity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M45

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}



theorem model_scalar_smooth (D : LeviCivitaData g) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  have hs := ((M04.isSmoothCovariantTensor_ricciEvaluation D).tensorTrace
    (g := g)).2 univ isOpen_univ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  change ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞
    (fun x => ∑ i, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x i))
  simpa [contMDiffOn_univ, RiemannianMetric.tensorTrace,
    LeviCivitaData.scalarCurvature, LeviCivitaData.ricciEvaluation] using hs



noncomputable def modelRicciBilinear (D : LeviCivitaData g) (x : M) :
    TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ :=
  ∑ i, D.curvatureTensor_bilinear_first_third x
    (g.orthonormalBasis x i) (g.orthonormalBasis x i)



theorem modelRicciBilinear_apply (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) : modelRicciBilinear D x v w = D.ricci x v w := by
  simp only [modelRicciBilinear, LinearMap.sum_apply,
    LeviCivitaData.curvatureTensor_bilinear_first_third_apply, LeviCivitaData.ricci]



theorem model_ricciNormSq_eq_sum_basis (D : LeviCivitaData g) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) x)),
      D.ricciNormSq x = ∑ i, ∑ j, D.ricci x (b i) (b j) ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    infer_instance
  intro ι _ b
  simpa only [modelRicciBilinear_apply, LeviCivitaData.ricciNormSq] using
    M13.sum_sq_bilinear_basis_eq (modelRicciBilinear D x) (g.orthonormalBasis x) b



theorem model_ricciNormSq_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) : D.ricciNormSq x = D'.ricciNormSq (f x) := by
  let e : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
      (g.mfderiv_bijective_of_pullback_eq h x (fun a b => (hmetric x hx a b).symm))
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let e' := e.isometryOfInner (fun a b => (hmetric x hx a b).symm)
  rw [model_ricciNormSq_eq_sum_basis D' (f x) ((g.orthonormalBasis x).map e')]
  change (∑ i, ∑ j, D.ricci x (g.orthonormalBasis x i)
    (g.orthonormalBasis x j) ^ 2) = ∑ i, ∑ j, D'.ricci (f x)
      (e (g.orthonormalBasis x i)) (e (g.orthonormalBasis x j)) ^ 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [D.ricci_eq_of_local_isometry D' hU hf hmetric hx]
  rfl



theorem model_scalar_differential_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) D.scalarCurvature x v =
      mvfderiv (𝓡 n) D'.scalarCurvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) := by
  have heq : D.scalarCurvature =ᶠ[𝓝 x] D'.scalarCurvature ∘ f :=
    eventually_of_mem (hU.mem_nhds hx) fun y hy =>
      D.scalarCurvature_eq_of_local_isometry D' hU hf hmetric hy
  rw [show mvfderiv (𝓡 n) D.scalarCurvature x =
    mvfderiv (𝓡 n) (D'.scalarCurvature ∘ f) x from heq.mfderiv_eq]
  rw [mvfderiv_comp x ((model_scalar_smooth D' (f x)).mdifferentiableAt (by simp))
    ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
  rfl



theorem model_scalar_evolution_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) :
    D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x =
      D'.laplacian D'.scalarCurvature (f x) + 2 * D'.ricciNormSq (f x) := by
  have heq : D.scalarCurvature =ᶠ[𝓝 x] D'.scalarCurvature ∘ f :=
    eventually_of_mem (hU.mem_nhds hx) fun y hy =>
      D.scalarCurvature_eq_of_local_isometry D' hU hf hmetric hy
  rw [D.laplacian_eq_of_eventuallyEq heq,
    D.laplacian_comp_of_metric_pullback D' (hf.contMDiffAt (hU.mem_nhds hx))
      (eventually_of_mem (hU.mem_nhds hx) hinv)
      (eventually_of_mem (hU.mem_nhds hx) hmetric) (model_scalar_smooth D' (f x)),
    model_ricciNormSq_eq_of_local_isometry D D' hU hf hmetric hx]




theorem model_scalarGradientNorm_le {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g) (x : X) {B : ℝ}
    (hB : ∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 →
      |mvfderiv (𝓡 3) D.scalarCurvature x v| ≤ B) :
    scalarGradientNorm g D x ≤ B := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)) := ⟨0, by
    unfold TangentSpace
    simp⟩
  have hunit : g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1 :=
    (g.orthonormalBasis x).inner_eq_one i
  apply csSup_le
  · exact ⟨_, ⟨⟨g.orthonormalBasis x i, hunit⟩, rfl⟩⟩
  · rintro _ ⟨v, rfl⟩
    exact hB v.1 v.2

end PoincareConjecture.M45
