import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.SmoothFlow
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.LevelSet
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.FlowProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

noncomputable section

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M}

theorem exists_parallelGradient_productDiffeomorph
    {D : LeviCivitaData g} {f : M → ℝ} (hc : MetricComplete g)
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : HasUnitGradient D f) (hzero : HasZeroHessian D f) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hunit x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hunit x) n 0
    ∃ Φ : ℝ → M → M,
      ∃ e : (zeroLevelSet f × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M,
        (∀ x, Φ 0 x = x) ∧
        (∀ x, IsMIntegralCurve (fun t => Φ t x) (D.gradient f)) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 (n + 1))) (𝓡 (n + 1)) ∞
          (fun z : ℝ × M => Φ z.1 z.2) ∧
        (∀ z, e z = Φ z.2 (zeroLevelIncl f z.1)) ∧
        (∀ x, (e.symm x).2 = f x) ∧
        (∀ x, zeroLevelIncl f (e.symm x).1 = Φ (-f x) x) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hunit x
  letI := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  letI := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  obtain ⟨Φ, h0, hΦ, hgeo, _, hadd, hscalar⟩ := exists_complete_gradientFlow hc hf hunit hzero
  have hs := contMDiff_gradientFlow hf h0 hΦ hgeo
  let e := productDiffeomorphOfFlow hf (fun x => regular_of_hasUnitGradient hunit x)
    Φ hs h0 hadd hscalar
  refine ⟨Φ, e, h0, hΦ, hs, ?_, ?_, ?_⟩
  · intro z; rfl
  · intro x; rfl
  · intro x; rfl

theorem zeroLevelSet_connectedSpace [ConnectedSpace M]
    {D : LeviCivitaData g} {f : M → ℝ} (hc : MetricComplete g)
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : HasUnitGradient D f) (hzero : HasZeroHessian D f) :
    ConnectedSpace (zeroLevelSet f) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openLevelSetChartedSpace hf (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hunit x) n 0
  letI := isManifold_openLevelSet hf (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hunit x) n 0
  obtain ⟨Φ, e, _⟩ := exists_parallelGradient_productDiffeomorph hc hf hunit hzero
  have hsurj : Function.Surjective (fun x => (e.symm x).1) := by
    intro y
    exact ⟨e (y, 0), congrArg Prod.fst (e.symm_apply_apply (y, 0))⟩
  exact hsurj.connectedSpace e.symm.contMDiff.continuous.fst

end PoincareConjecture.RiemannianMetric
