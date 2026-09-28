import PoincareConjecture.Proofs.M34.Standard.ClosedPullbackCoefficients
import PoincareConjecture.Proofs.M34.Mathlib.ParameterSpatialDerivatives
import PoincareConjecture.Proofs.M04.TensorNorm
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean
import PoincareConjecture.Definitions.Ch12.StandardCap

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

structure MetricFlowApproximation (h : RiemannianMetric 3 StandardCapSpace)
    (M : ℕ → Type) [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace StandardCapSpace (M k)] [∀ k, IsManifold (𝓡 3) ∞ (M k)] where

  time : ℝ

  time_pos : 0 < time

  flow (k : ℕ) : RicciFlow 3 (M k) (Icc 0 time)

  source : ℕ → Set StandardCapSpace

  source_isOpen (k : ℕ) : IsOpen (source k)

  chart (k : ℕ) : StandardCapSpace → M k

  chart_smooth (k : ℕ) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (chart k) (source k)

  chart_invertible (k : ℕ) (x : StandardCapSpace) (hx : x ∈ source k) :
    (mfderiv (𝓡 3) (𝓡 3) (chart k) x).IsInvertible

  initial_pullback (k : ℕ) (x : StandardCapSpace) (hx : x ∈ source k) :
    ((flow k).metric 0).pullbackCoefficients (chart k) x = h.euclideanCoefficients x

  compact_sources (K : Set StandardCapSpace) (hK : IsCompact K) :
    ∀ᶠ k : ℕ in atTop, K ⊆ source k

  curvature_bound : ℕ → ℝ

  bound_pos (m : ℕ) : 0 < curvature_bound m

  curvature_le (m k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 time) (q : M k) :
    ((flow k).connection t).curvatureDerivativeNorm m q ≤ curvature_bound m

namespace MetricFlowApproximation

variable {h : RiemannianMetric 3 StandardCapSpace} {M : ℕ → Type}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace StandardCapSpace (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] (A : MetricFlowApproximation h M)

theorem full_curvature_le (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 A.time) (q : M k) :
    ((A.flow k).connection t).curvatureTensorNorm q ≤ A.curvature_bound 0 := by
  simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using A.curvature_le 0 k t ht q

noncomputable def coefficients (k : ℕ) (t : ℝ) (x : StandardCapSpace) :
    StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
  ((A.flow k).metric t).pullbackCoefficients (A.chart k) x

theorem contDiffOn_coefficients (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × StandardCapSpace => A.coefficients k p.1 p.2)
      (Icc 0 A.time ×ˢ A.source k) :=
  (A.flow k).smooth.contDiffOn_spacetime_pullbackCoefficients
    (A.source_isOpen k) (A.chart_smooth k)

theorem contDiffOn_spatialJet (k m : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × StandardCapSpace => iteratedFDeriv ℝ m (A.coefficients k p.1) p.2)
      (Icc 0 A.time ×ˢ A.source k) :=
  (A.contDiffOn_coefficients k).iteratedFDeriv_snd_of_isOpen (A.source_isOpen k) m

theorem continuousOn_spatialJet_time (k m : ℕ) {x : StandardCapSpace}
    (hx : x ∈ A.source k) :
    ContinuousOn (fun t => iteratedFDeriv ℝ m (A.coefficients k t) x) (Icc 0 A.time) := by
  apply (A.contDiffOn_spatialJet k m).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn
  exact fun _ ht => ⟨ht, hx⟩

theorem differentiableAt_spatialJet_time (k m : ℕ) {x : StandardCapSpace}
    (hx : x ∈ A.source k) {t : ℝ} (ht : t ∈ Ioo 0 A.time) :
    DifferentiableAt ℝ (fun s => iteratedFDeriv ℝ m (A.coefficients k s) x) t := by
  have hjoint := (A.contDiffOn_spatialJet k m).mono
    (prod_mono Ioo_subset_Icc_self (Subset.refl _))
  exact ((hjoint.contDiffAt
    ((isOpen_Ioo.prod (A.source_isOpen k)).mem_nhds ⟨ht, hx⟩)).comp t
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

theorem coefficients_zero (k : ℕ) {x : StandardCapSpace} (hx : x ∈ A.source k) :
    A.coefficients k 0 x = h.euclideanCoefficients x := A.initial_pullback k x hx

theorem spatialJet_zero (k m : ℕ) {x : StandardCapSpace} (hx : x ∈ A.source k) :
    iteratedFDeriv ℝ m (A.coefficients k 0) x =
      iteratedFDeriv ℝ m h.euclideanCoefficients x := by
  have heq : A.coefficients k 0 =ᶠ[𝓝 x] h.euclideanCoefficients := by
    filter_upwards [(A.source_isOpen k).mem_nhds hx] with y hy
    exact A.coefficients_zero k hy
  exact (heq.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds

end MetricFlowApproximation
end PoincareConjecture.M34
