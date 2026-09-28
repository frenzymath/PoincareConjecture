import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.ProductDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.ProductMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.LevelComplete










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] {g : RiemannianMetric (n + 1) M}




theorem exists_parallelGradient_productIsometry
    {D : LeviCivitaData g} {f : M → ℝ} (hc : MetricComplete g)
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (hz : HasZeroHessian D f) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    let h := regularLevelMetric hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 0 g
    Nonempty (zeroLevelSet f) ∧ ConnectedSpace (zeroLevelSet f) ∧ MetricComplete h ∧
    ∃ Φ : ℝ → M → M,
      ∃ e : (zeroLevelSet f × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M,
        (∀ x, Φ 0 x = x) ∧
        (∀ x, IsMIntegralCurve (fun t => Φ t x) (D.gradient f)) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 (n + 1))) (𝓡 (n + 1)) ∞
          (fun z : ℝ × M => Φ z.1 z.2) ∧
        (∀ z, e z = Φ z.2 (zeroLevelIncl f z.1)) ∧
        (∀ z, f (e z) = z.2) ∧
        (∀ (z : zeroLevelSet f × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
          g.inner (e z) (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z v)
            (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z w) =
              h.inner z.1 v.1 w.1 + v.2 * w.2) ∧
        (∀ x, (e.symm x).2 = f x) ∧
        (∀ x, zeroLevelIncl f (e.symm x).1 = Φ (-f x) x) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  letI := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  letI := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  refine ⟨zeroLevelSet_nonempty hc hf hu hz, zeroLevelSet_connectedSpace hc hf hu hz,
    zeroLevelMetric_complete g hf (regular_of_hasUnitGradient hu) hc, ?_⟩
  obtain ⟨Φ, e, h0, hΦ, hs, he, htime, hlevel⟩ :=
    exists_parallelGradient_productDiffeomorph hc hf hu hz
  refine ⟨Φ, e, h0, hΦ, hs, he, ?_, ?_, htime, hlevel⟩
  · intro z
    have hh := htime (e z)
    rw [e.symm_apply_apply] at hh
    exact hh.symm
  · have heq : (e : zeroLevelSet f × ℝ → M) =
        (fun z => Φ z.2 (zeroLevelIncl f z.1)) := funext he
    rw [heq]
    exact gradientFlow_product_metric hf hu hz hs hΦ h0

end PoincareConjecture.RiemannianMetric
