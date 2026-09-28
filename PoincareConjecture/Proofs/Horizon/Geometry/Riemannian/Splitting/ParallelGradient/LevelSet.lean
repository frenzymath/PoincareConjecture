import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.CompleteFlow
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevel








set_option autoImplicit false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]

abbrev zeroLevelSet (f : M → ℝ) :=
  openLevelSet f (⊤ : Opens M) 0

abbrev zeroLevelIncl (f : M → ℝ) : zeroLevelSet f → M :=
  openLevelIncl f (⊤ : Opens M) 0

theorem zeroLevelSet_nonempty_of_integralCurve
    {g : RiemannianMetric (n + 1) M} {D : LeviCivitaData g}
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : HasUnitGradient D f) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (D.gradient f))
    {x : M} (hγ0 : γ 0 = x) :
    Nonempty (zeroLevelSet f) := by
  refine ⟨⟨⟨γ (-f x), Set.mem_univ _⟩, ?_⟩⟩
  simpa using integralCurve_hits_zero hf hunit hγ hγ0


theorem zeroLevelSet_nonempty [T3Space M] [Nonempty M]
    {g : RiemannianMetric (n + 1) M} {D : LeviCivitaData g}
    {f : M → ℝ} (hc : MetricComplete g)
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : HasUnitGradient D f) (hzero : HasZeroHessian D f) :
    Nonempty (zeroLevelSet f) := by
  obtain ⟨x⟩ := ‹Nonempty M›
  obtain ⟨γ, hγ0, hγ, _, _⟩ := exists_global_gradientIntegralCurve hc hf hunit hzero x
  exact zeroLevelSet_nonempty_of_integralCurve hf hunit hγ hγ0

theorem zeroLevelRange (f : M → ℝ) :
    Set.range (zeroLevelIncl f) = f ⁻¹' {0} := by
  simpa [zeroLevelIncl] using
    (range_openLevelIncl f (⊤ : Opens M) 0)

theorem zeroLevelGeometry
    (g : RiemannianMetric (n + 1) M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => hreg x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => hreg x) n 0
    ∃ gL : RiemannianMetric n (zeroLevelSet f),
      Topology.IsEmbedding (zeroLevelIncl f) ∧
      Set.range (zeroLevelIncl f) = f ⁻¹' {0} ∧
      ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (zeroLevelIncl f) ∧
      (∀ x : zeroLevelSet f,
        Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl f) x)) ∧
      (∀ x : zeroLevelSet f,
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl f) x :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).range =
        (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f (zeroLevelIncl f x) :
          EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).ker) ∧
      (∀ (x : zeroLevelSet f) (v w : EuclideanSpace ℝ (Fin n)),
        gL.inner x v w = g.inner (zeroLevelIncl f x)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl f) x v)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl f) x w)) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openLevelSetChartedSpace hf (⊤ : Opens M)
    (fun x _ => hreg x) n 0
  letI := isManifold_openLevelSet hf (⊤ : Opens M)
    (fun x _ => hreg x) n 0
  simpa [zeroLevelSet, zeroLevelIncl] using
    (regularLevelGeometry g hf (⊤ : Opens M) (fun x _ => hreg x) 0)

end PoincareConjecture.RiemannianMetric
