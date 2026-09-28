import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Jets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.BilinearJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

noncomputable def pulledChartCoefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier) (k : ℕ) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  ((S.flow (G.subsequence k)).metricAt t).pullbackCoefficients
    (fun y ↦ ((G.embedding k).toFun (t, (extChartAt (𝓡 n) q).symm y)).2)

theorem contDiffAt_pulledChartCoefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier) (k : ℕ) (t : ℝ)
    (ht : t ∈ Ioo a b) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt (𝓡 n) q).target)
    (hys : (extChartAt (𝓡 n) q).symm y ∈ G.exhaustion k) :
    ContDiffAt ℝ ∞ (G.pulledChartCoefficients q k t) y := by
  exact ((S.flow (G.subsequence k)).metricAt t).contDiffAt_pullbackCoefficients
    (((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) ht hys).comp y
      ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hy)))

theorem pulledChartCoefficients_eq
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier) (k : ℕ) (t : ℝ)
    (ht : t ∈ Ioo a b) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt (𝓡 n) q).target)
    (hys : (extChartAt (𝓡 n) q).symm y ∈ G.exhaustion k)
    (v w : EuclideanSpace ℝ (Fin n)) :
    G.pulledChartCoefficients q k t y v w =
      pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)
        t ((extChartAt (𝓡 n) q).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm y v)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm y w) := by
  let ψ := fun x ↦ ((G.embedding k).toFun (t, x)).2
  let c := (extChartAt (𝓡 n) q).symm
  have hψ := ((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) ht hys).mdifferentiableAt
    (by simp)
  have hc := ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hy)).mdifferentiableAt (by simp)
  have hd : mfderiv (𝓡 n) (𝓡 n) (ψ ∘ c) y =
      (mfderiv (𝓡 n) (𝓡 n) ψ (c y)).comp (mfderiv (𝓡 n) (𝓡 n) c y) :=
    mfderiv_comp y hψ hc
  change ((S.flow (G.subsequence k)).metricAt t).inner (ψ (c y))
      (mfderiv (𝓡 n) (𝓡 n) (ψ ∘ c) y v)
      (mfderiv (𝓡 n) (𝓡 n) (ψ ∘ c) y w) = _
  rw [hd]
  rfl

theorem pulledChartCoefficients_basis_eq
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier) (k : ℕ) (t : ℝ)
    (ht : t ∈ Ioo a b) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt (𝓡 n) q).target)
    (hys : (extChartAt (𝓡 n) q).symm y ∈ G.exhaustion k)
    (i j : Fin n) :
    G.pulledChartCoefficients q k t y (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j) =
      G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) i j (t, y) :=
  G.pulledChartCoefficients_eq q k t ht hy hys _ _

theorem eventually_contDiffAt_pulledChartCoefficients_on_compact
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier) (t : ℝ)
    (ht : t ∈ Ioo a b) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 n) q).target) :
    ∀ᶠ k in atTop, ∀ y ∈ K, ContDiffAt ℝ ∞ (G.pulledChartCoefficients q k t) y := by
  have hc : ContinuousOn (extChartAt (𝓡 n) q).symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨s, hs⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hc)
  filter_upwards [eventually_ge_atTop s] with k hk y hy
  exact G.contDiffAt_pulledChartCoefficients q k t ht (hKc hy)
    (G.exhaustion_monotone hk (hs (mem_image_of_mem _ hy)))

end PoincareConjecture.PointedGeometricConvergence
