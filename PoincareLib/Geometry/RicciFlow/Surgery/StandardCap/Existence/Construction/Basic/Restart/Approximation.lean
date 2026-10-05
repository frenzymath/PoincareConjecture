import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Coordinates.ClosedPullbackCoefficients
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.ParameterSpatialDerivatives
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareLib.Geometry.Riemannian.Connection.Euclidean
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Geometry

/-!
# Fixed-coordinate approximations of an arbitrary smooth cap metric

The analytic extraction only needs actual flows, growing open chart
sources, exact initial pullbacks, and uniform intrinsic curvature jets.
The initial metric need not be a standard initial metric. This is the
restart interface for Morgan-Tian Theorem 12.5, pp. 296-297; see
terminal-restart-approximation.md.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

/-- Actual flow approximations in fixed original coordinates, with all
initial coefficients and all curvature bounds retained
(Theorem 12.5, pp. 296-297). -/
structure MetricFlowApproximation (h : RiemannianMetric 3 StandardCapSpace)
    (M : ℕ → Type) [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace StandardCapSpace (M k)] [∀ k, IsManifold (𝓡 3) ∞ (M k)] where
  /-- Common included terminal time. -/
  time : ℝ
  /-- The time slab has positive length. -/
  time_pos : 0 < time
  /-- Actual Ricci flows on the carrier sequence. -/
  flow (k : ℕ) : RicciFlow 3 (M k) (Icc 0 time)
  /-- Original-coordinate domains with exact initial coefficients. -/
  source : ℕ → Set StandardCapSpace
  /-- Every source is open. -/
  source_isOpen (k : ℕ) : IsOpen (source k)
  /-- Fixed total parametrizations of the approximations. -/
  chart (k : ℕ) : StandardCapSpace → M k
  /-- Smoothness is required on the actual source. -/
  chart_smooth (k : ℕ) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (chart k) (source k)
  /-- Chart derivatives are genuinely invertible. -/
  chart_invertible (k : ℕ) (x : StandardCapSpace) (hx : x ∈ source k) :
    (mfderiv (𝓡 3) (𝓡 3) (chart k) x).IsInvertible
  /-- Initial pullback coefficients are exactly the supplied smooth metric. -/
  initial_pullback (k : ℕ) (x : StandardCapSpace) (hx : x ∈ source k) :
    ((flow k).metric 0).pullbackCoefficients (chart k) x = h.euclideanCoefficients x
  /-- Every original compact set is eventually retained. -/
  compact_sources (K : Set StandardCapSpace) (hK : IsCompact K) :
    ∀ᶠ k : ℕ in atTop, K ⊆ source k
  /-- The bounds are chosen after the flows and before index/time/point. -/
  curvature_bound : ℕ → ℝ
  /-- Bounds are positive. -/
  bound_pos (m : ℕ) : 0 < curvature_bound m
  /-- The actual full covariant curvature jets are uniformly controlled. -/
  curvature_le (m k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 time) (q : M k) :
    ((flow k).connection t).curvatureDerivativeNorm m q ≤ curvature_bound m

namespace MetricFlowApproximation

variable {h : RiemannianMetric 3 StandardCapSpace} {M : ℕ → Type}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace StandardCapSpace (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] (A : MetricFlowApproximation h M)

/-- The zeroth intrinsic derivative is the actual full curvature norm
(Theorem 12.5, pp. 296-297). -/
theorem full_curvature_le (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 A.time) (q : M k) :
    ((A.flow k).connection t).curvatureTensorNorm q ≤ A.curvature_bound 0 := by
  simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using A.curvature_le 0 k t ht q

/-- Evolving metric coefficients in the same original coordinates at
every approximation index (Theorem 12.5, pp. 296-297). -/
noncomputable def coefficients (k : ℕ) (t : ℝ) (x : StandardCapSpace) :
    StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
  ((A.flow k).metric t).pullbackCoefficients (A.chart k) x

/-- Joint smoothness includes both endpoints of the actual closed slab
(Theorem 12.5, pp. 296-297). -/
theorem contDiffOn_coefficients (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × StandardCapSpace => A.coefficients k p.1 p.2)
      (Icc 0 A.time ×ˢ A.source k) :=
  (A.flow k).smooth.contDiffOn_spacetime_pullbackCoefficients
    (A.source_isOpen k) (A.chart_smooth k)

/-- Spatial jets preserve joint smoothness at the initial boundary
(Theorem 12.5, pp. 296-297). -/
theorem contDiffOn_spatialJet (k m : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × StandardCapSpace => iteratedFDeriv ℝ m (A.coefficients k p.1) p.2)
      (Icc 0 A.time ×ˢ A.source k) :=
  (A.contDiffOn_coefficients k).iteratedFDeriv_snd_of_isOpen (A.source_isOpen k) m

/-- Spatial jets are continuous in time through the initial slice
(Theorem 12.5, pp. 296-297). -/
theorem continuousOn_spatialJet_time (k m : ℕ) {x : StandardCapSpace}
    (hx : x ∈ A.source k) :
    ContinuousOn (fun t => iteratedFDeriv ℝ m (A.coefficients k t) x) (Icc 0 A.time) := by
  apply (A.contDiffOn_spatialJet k m).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn
  exact fun _ ht => ⟨ht, hx⟩

/-- Interior spatial jets have ordinary time derivatives
(Theorem 12.5, pp. 296-297). -/
theorem differentiableAt_spatialJet_time (k m : ℕ) {x : StandardCapSpace}
    (hx : x ∈ A.source k) {t : ℝ} (ht : t ∈ Ioo 0 A.time) :
    DifferentiableAt ℝ (fun s => iteratedFDeriv ℝ m (A.coefficients k s) x) t := by
  have hjoint := (A.contDiffOn_spatialJet k m).mono
    (prod_mono Ioo_subset_Icc_self (Subset.refl _))
  exact ((hjoint.contDiffAt
    ((isOpen_Ioo.prod (A.source_isOpen k)).mem_nhds ⟨ht, hx⟩)).comp t
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

/-- The initial coefficient equality holds on the exact retained source
(Theorem 12.5, pp. 296-297). -/
theorem coefficients_zero (k : ℕ) {x : StandardCapSpace} (hx : x ∈ A.source k) :
    A.coefficients k 0 x = h.euclideanCoefficients x := A.initial_pullback k x hx

/-- The initial equality is a germ, hence identifies every spatial jet
(Theorem 12.5, pp. 296-297). -/
theorem spatialJet_zero (k m : ℕ) {x : StandardCapSpace} (hx : x ∈ A.source k) :
    iteratedFDeriv ℝ m (A.coefficients k 0) x =
      iteratedFDeriv ℝ m h.euclideanCoefficients x := by
  have heq : A.coefficients k 0 =ᶠ[𝓝 x] h.euclideanCoefficients := by
    filter_upwards [(A.source_isOpen k).mem_nhds hx] with y hy
    exact A.coefficients_zero k hy
  exact (heq.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds

end MetricFlowApproximation
end PoincareMT.M34
