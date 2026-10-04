import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.FactorMetric
import PoincareLib.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature

/-!
# Ricci flow on a fixed parallel-gradient factor

The induced metrics on one fixed zero level form a Ricci flow when the
same function has unit gradient and zero Hessian throughout the time interval.
The factor connection is constructed from its induced metric, and the
evolution equation follows from the proved intrinsic Ricci restriction.

Reference: Kleiner--Lott (corrected 2013), Proposition 41.13, p. 2678.
Backward persistence of the parallel gradient is a separate geometric step.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

namespace PoincareMT.RicciFlow

open RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] {J : Set ℝ}
  (F : RicciFlow (n + 1) M J)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  {t₀ : ℝ} (ht₀ : t₀ ∈ J)
  (hu : ∀ t ∈ J, RiemannianMetric.HasUnitGradient (F.connection t) f)
  (hz : ∀ t ∈ J, RiemannianMetric.HasZeroHessian (F.connection t) f)

/-- The actual fixed regular-level metric family, equipped with its intrinsic
Levi-Civita connections, satisfies the Ricci-flow equation. -/
def parallelGradientFactor :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => RiemannianMetric.regular_of_hasUnitGradient (hu t₀ ht₀) x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => RiemannianMetric.regular_of_hasUnitGradient (hu t₀ ht₀) x) n 0
    RicciFlow n (zeroLevelSet f) J := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) =>
    RiemannianMetric.regular_of_hasUnitGradient (hu t₀ ht₀) x
  letI := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  letI := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  let g := fun t => RiemannianMetric.regularLevelMetric hf (⊤ : Opens M) hreg 0 (F.metric t)
  refine
    { metric := g
      connection := fun t => (g t).leviCivitaData
      interval := F.interval
      nontrivial := F.nontrivial
      smooth := F.smooth.regularLevelMetric hf (⊤ : Opens M) hreg 0
      equation := ?_ }
  intro t ht y u v
  have hRic := (RiemannianMetric.parallelGradient_factor_curvature hf (hu t ht) (hz t ht) y).2.2.1 u v
  rw [hRic]
  exact F.regularLevelMetric_equation hf (⊤ : Opens M) hreg 0 t ht y u v

/-- Completeness and the curvature hypotheses hold for this same fixed
factor flow at every time. Nonflatness at any ambient point descends to a
point of the factor by the actual gradient-flow product isometry. -/
theorem parallelGradientFactor_geometry [T3Space M] [ConnectedSpace M]
    (hc : ∀ t ∈ J, MetricComplete (F.metric t))
    (hop : ∀ t ∈ J, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hbound : ∀ t ∈ J, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient (hu t₀ ht₀) x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient (hu t₀ ht₀) x) n 0
    let H := F.parallelGradientFactor hf ht₀ hu hz
    Nonempty (zeroLevelSet f) ∧ ConnectedSpace (zeroLevelSet f) ∧
      (∀ t ∈ J, MetricComplete (H.metric t)) ∧
      (∀ t ∈ J, ∀ y, (H.connection t).NonnegativeCurvatureOperator y) ∧
      (∀ t ∈ J, ∀ y, (H.connection t).curvatureTensorNorm y ≤ K) ∧
      (∀ t ∈ J, ∀ p, 0 < (F.connection t).scalarCurvature p →
        ∃ y, 0 < (H.connection t).scalarCurvature y) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient (hu t₀ ht₀) x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  have hs (t : ℝ) (ht : t ∈ J) :=
    exists_parallelGradient_productIsometry_curvature (hc t ht) hf (hu t ht) (hz t ht)
  refine ⟨(hs t₀ ht₀).1, (hs t₀ ht₀).2.1, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (hs t ht).2.2.1
  · intro t ht y
    exact (parallelGradient_factor_curvature hf (hu t ht) (hz t ht) y).2.2.2.2.2
      (hop t ht _)
  · intro t ht y
    exact (parallelGradient_factor_curvature hf (hu t ht) (hz t ht) y).2.2.2.2.1 ▸
      hbound t ht (zeroLevelIncl f y)
  · intro t ht p hp
    obtain ⟨_, _, _, Φ, e, _, _, _, _, _, hscalar, _⟩ := hs t ht
    exact ⟨(e.symm p).1, (hscalar p).symm ▸ hp⟩

end PoincareMT.RicciFlow
