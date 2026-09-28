import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


def PoincareConjecture.NormalizedCornerScalarBound
    (n m k : ℕ) (hdim : n = m + k) (M : Type*)
    [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (δ H η C : ℝ) : Prop :=
  ∀ (g : PoincareConjecture.RiemannianMetric n M) (D : PoincareConjecture.LeviCivitaData g),
    PoincareConjecture.MetricComplete g →
    (∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w) →
    ∀ (f h : Fin k → M → ℝ)
      (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
      (_hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i)) (U : Opens M),
    (∀ x ∈ U, ∀ i,
      g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (D.gradient (h i) x) ≤ 1) →
    (∀ x ∈ U, ∀ i,
      g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * δ) →
    (∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (f i) x) (D.gradient (f j) x)| ≤ δ ∧
      |g.inner x (D.gradient (f i) x) (D.gradient (h j) x)| ≤ δ ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ δ ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (h j) x)| ≤ δ) →
    (∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (D.gradient (f i) x) (D.gradient (f j) x) ≤ 0) →
    (∀ x ∈ U, ∀ i z,
      D.hessian (f i) x z z ≤ H * g.inner x z z ∧
      D.hessian (h i) x z z ≤ H * g.inner x z z) →
    let F := fun x i => f i x
    let hF : ContMDiff (𝓡 n) 𝓘(ℝ, Fin k → ℝ) ∞ F := contMDiff_pi_space.mpr hf
    ∀ (hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 n) 𝓘(ℝ, Fin k → ℝ) F x))
      (c : Fin k → ℝ),
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = m + k) :=
        ⟨by rw [finrank_euclideanSpace_fin]; exact hdim⟩
      letI := openFiberChartedSpace (m := m) hF U hreg c
      letI := isManifold_openFiber (m := m) hF U hreg c
      let L := openFiber F U c
      let incl := openFiberIncl F U c
      let gL : PoincareConjecture.RiemannianMetric m L :=
        PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g incl
          (contMDiff_openFiberIncl (m := m) hF U hreg c)
          (injective_mfderiv_openFiberIncl (m := m) hF U hreg c)
      CompactSpace L → ConnectedSpace L → PoincareConjecture.MetricComplete gL →
      (∀ x y : L, gL.edist x y ≤ 1) →
      (∀ x : L, ∀ y : M, g.edist (incl x) y ≤ ENNReal.ofReal η → y ∈ U) →
      ∀ K : L → ℝ, Continuous K → (∀ x, 0 ≤ K x) →
      (∀ x (v w : TangentSpace (𝓡 m) x),
        -K x ≤ gL.leviCivitaData.sectionalCurvature x v w) →
      (∫ x, max 0 (gL.leviCivitaData.scalarCurvature x) ∂gL.volumeMeasure) ≤
        C * (1 + ∫ x, K x ∂gL.volumeMeasure)
