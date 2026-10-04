import PoincareLib.Geometry.Riemannian.Measure.Calibrated
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Reduced-volume and weak reduced-length infrastructure

The density follows Morgan--Tian's unnormalized convention, so its Euclidean
integral is `(4 * pi) ^ (n / 2)`. The measure is calibrated Hausdorff measure
for the explicitly selected Riemannian metric. Weak inequalities use complete
test-function integrands; the statement file separately requires their
integrability and supplies a full-measure regular locus.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- The reduced-volume density at a positive backward time. -/
noncomputable def reducedVolumeDensity {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p : M) (τ : ℝ) (q : M) : ℝ :=
  if 0 < τ then
    Real.rpow τ (-(n : ℝ) / 2) * Real.exp (-reducedLength F T p q τ)
  else 0

/-- The reduced volume of a spatial subset in the selected time slice. -/
noncomputable def reducedVolumeOn [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (p : M) (τ : ℝ)
    (A : Set M) : ℝ :=
  ∫ q in A, reducedVolumeDensity F T p τ q
    ∂calibratedMetricVolume (F.metric (T - τ))

/-- The whole-space reduced volume. -/
noncomputable def reducedVolume [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (p : M) (τ : ℝ) : ℝ :=
  ∫ q, reducedVolumeDensity F T p τ q
    ∂calibratedMetricVolume (F.metric (T - τ))

/-- The unnormalized Euclidean value of reduced volume. -/
noncomputable def euclideanReducedVolume (n : ℕ) : ℝ :=
  Real.rpow (4 * Real.pi) ((n : ℝ) / 2)

/-- Local spacetime Lipschitz regularity measured using the terminal metric. -/
def reducedLengthLocallyLipschitz [T3Space M] {J : Set ℝ}
    (F : RicciFlow n M J) (T τmax : ℝ) (p : M) : Prop :=
  let g := F.metric T
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  LocallyLipschitzOn (Set.univ ×ˢ Set.Ioo 0 τmax)
    (fun z : M × ℝ ↦ reducedLength F T p z.1 z.2)

/-- The first weak reduced-length integrand, with the Laplacian on the test function. -/
noncomputable def reducedLengthFirstWeakIntegrand {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (p : M) (τ : ℝ)
    (φ : M → ℝ) (q : M) : ℝ :=
  φ q * (deriv (fun s ↦ reducedLength F T p q s) τ +
      reducedLengthGradientNormSq F T (fun z ↦ reducedLength F T p z.1 z.2) τ q -
      (F.connection (T - τ)).scalarCurvature q + (n : ℝ) / (2 * τ)) -
    reducedLength F T p q τ * (F.connection (T - τ)).laplacian φ q

/-- The second weak reduced-length integrand, including the full `n / τ` term. -/
noncomputable def reducedLengthSecondWeakIntegrand {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (p : M) (τ : ℝ)
    (φ : M → ℝ) (q : M) : ℝ :=
  φ q * (-reducedLengthGradientNormSq F T
      (fun z ↦ reducedLength F T p z.1 z.2) τ q +
      (F.connection (T - τ)).scalarCurvature q +
      (reducedLength F T p q τ - (n : ℝ)) / τ) +
    2 * reducedLength F T p q τ * (F.connection (T - τ)).laplacian φ q

/-- The regular locus and local bounds needed to interpret weak slice inequalities. -/
structure ReducedLengthMeasureData [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {J : Set ℝ} (F : RicciFlow n M J) (T τmax : ℝ) (p : M) where
  regularDomain : Set (M × ℝ)
  regularDomain_open : IsOpen regularDomain
  regularDomain_time : regularDomain ⊆ Set.univ ×ˢ Set.Ioo 0 τmax
  regular_points : ∀ z ∈ regularDomain,
    Nonempty (ReducedLengthRegularPoint F T τmax p z.1 z.2)
  slice_complement_null : ∀ τ : ℝ, 0 < τ → τ < τmax →
    calibratedMetricVolume (F.metric (T - τ)) {q | (q, τ) ∉ regularDomain} = 0
  continuous : ContinuousOn (fun z : M × ℝ ↦ reducedLength F T p z.1 z.2)
    (Set.univ ×ˢ Set.Ioo 0 τmax)
  locally_lipschitz : reducedLengthLocallyLipschitz F T τmax p
  local_derivative_bounds : ∀ z : M × ℝ, z ∈ Set.univ ×ˢ Set.Ioo 0 τmax →
    ∃ U : Set (M × ℝ), IsOpen U ∧ z ∈ U ∧
      U ⊆ Set.univ ×ˢ Set.Ioo 0 τmax ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ U ∩ regularDomain,
        |deriv (fun s ↦ reducedLength F T p w.1 s) w.2| ≤ C ∧
        reducedLengthGradientNormSq F T
          (fun z ↦ reducedLength F T p z.1 z.2) w.2 w.1 ≤ C

/-- An open regular domain closed under following minimizing L-paths toward the base. -/
def IsBackwardLStarShaped {J : Set ℝ} (F : RicciFlow n M J)
    (T τmax : ℝ) (p : M) (A : Set (M × ℝ)) : Prop :=
  IsOpen A ∧ A ⊆ Set.univ ×ˢ Set.Ioo 0 τmax ∧
    ∀ z ∈ A, ∃ r : ReducedLengthRegularPoint F T τmax p z.1 z.2,
      ∀ σ ∈ Set.Ioc 0 z.2, (r.path.curve σ, σ) ∈ A

/-- A single Euclidean isometry identifies every metric on the stated time interval. -/
def IsStaticEuclideanFlowOn {J : Set ℝ} (F : RicciFlow n M J) (I : Set ℝ) : Prop :=
  ∃ e : Diffeomorph (𝓡 n) (𝓡 n) M (EuclideanSpace ℝ (Fin n)) ∞,
    ∀ t ∈ I, ∀ q : M, ∀ v w : TangentSpace (𝓡 n) q,
      (F.metric t).inner q v w =
        inner ℝ ((mfderiv (𝓡 n) (𝓡 n) e q) v) ((mfderiv (𝓡 n) (𝓡 n) e q) w)

end PoincareMT
