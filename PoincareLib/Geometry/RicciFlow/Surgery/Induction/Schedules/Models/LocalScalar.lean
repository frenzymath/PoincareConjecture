import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Homothety
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Curvature
import PoincareLib.Geometry.RicciFlow.Surgery.Control.ModelBounds
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareLib.Geometry.Riemannian.Homothety.Curvature.BasisContractions
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareLib.Geometry.Riemannian.ScalarOperators.Locality
import PoincareLib.Geometry.RicciFlow.Curvature.Calculus.Tensors.RicciRegularity
import PoincareLib.Geometry.Riemannian.Tensor.TraceRegularity

/-!
# Local scalar operators for the canonical models

The normalized model charts transport scalar curvature, its differential,
and its spatial evolution expression without a global separation hypothesis.
Morgan--Tian Definition 2.16, equation (2.1), p. 30, and Definition 9.76,
p. 231; see `derivations/ModelAnalyticsLocal.md` in the M45 task records.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

local notation "M04.isSmoothCovariantTensor_ricciEvaluation" => PoincareMT.RicciFlowAnalysis.isSmoothCovariantTensor_ricciEvaluation

namespace PoincareMT.M45

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

/-- The scalar contraction is smooth on every supplied smooth metric.
Source: the scalar differential in equation (2.1), p. 30. -/
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

/-- The actual Ricci evaluation is a bilinear form, with no separation
assumption on the carrier. Source: the contractions in equation (3.7), p. 41. -/
noncomputable def modelRicciBilinear (D : LeviCivitaData g) (x : M) :
    TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ :=
  ∑ i, D.curvatureTensor_bilinear_first_third x
    (g.orthonormalBasis x i) (g.orthonormalBasis x i)

/-- The bilinear form retains the actual connection's Ricci tensor.
Source: equation (3.7), p. 41. -/
theorem modelRicciBilinear_apply (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) : modelRicciBilinear D x v w = D.ricci x v w := by
  simp only [modelRicciBilinear, LinearMap.sum_apply,
    LeviCivitaData.curvatureTensor_bilinear_first_third_apply, LeviCivitaData.ricci]

/-- The squared Ricci contraction can be computed in a transported
orthonormal basis. Source: equation (3.7), p. 41. -/
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

/-- Local metric isometries preserve the full squared Ricci norm.
Source: the model normalization in Definition 2.16, p. 30. -/
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

/-- The scalar differential is transported through the actual local
metric isometry. Source: Definition 2.16, equation (2.1), p. 30. -/
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

/-- The spatial expression in scalar evolution is local-isometry invariant.
Source: equation (3.7), p. 41, as used in Corollary 9.71, pp. 229-230. -/
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

/-- A bound on every unit directional derivative bounds the retained
supremum definition of the scalar-gradient norm. The unit sphere is nonempty
in dimension three. Source: Definition 2.16, equation (2.1), p. 30. -/
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

end PoincareMT.M45
