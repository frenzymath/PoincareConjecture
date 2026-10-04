import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Compactness.Target
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.AlphaEnergy.Critical.Interface
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.AlphaEnergy.Variation.Energy
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Harmonic.Conformality

/-!
# Exact maximum-gradient output for the least-sphere assembly

Sacks-Uhlenbeck Theorems 4.4-4.7 and Morgan-Tian Lemma 18.10.
These are interfaces, not assertions of compactness or existence.
The final producer `m60PerturbedMinimizers_maxGradientLimit` will prove
`SUMaxGradientCompactnessProducer g` from the quantitative local gradient
estimate and the actual weak-coordinate smoothness theorem. The checked
puncture-removal and small-energy theorems are used directly.
-/

set_option autoImplicit false

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareMT.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The genuine all-chart weighted Euler equation on the round sphere,
with the source factor retained and unscaled rho equal to one. -/
def SUSphereWeightedEuler (g : RiemannianMetric n M) (alpha : ℝ)
    (f : UnitTwoSphere → M) : Prop :=
  ∀ (p : UnitTwoSphere) (b : M) (z : LoopPlane),
    f ((chartAt LoopPlane p).symm z) ∈ (extChartAt (𝓡 n) b).source →
    let v := f ∘ (chartAt LoopPlane p).symm
    let u := extChartAt (𝓡 n) b ∘ v
    let Gamma := CoordinateExponential.christoffelBilinear
      (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
    let w := fun y => (1 + 2 * m60EnergyDensity g v y / suAlphaRoundFactor y) ^ (alpha - 1)
    ∑ i : Fin 2, ConnectionVariation.covDerivAlong Gamma u
      (fun y => w y • fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (EuclideanSpace.basisFun (Fin 2) ℝ i) z = 0

/-- Compactness retains the original sequence for the null-bubble
replacement. The other case already has a non-null global sphere limit. -/
structure SUMaxGradientLimit (g : RiemannianMetric n M)
    (f : ℕ → UnitTwoSphere → M) where
  dimension : ℕ
  observation : M → EuclideanSpace ℝ (Fin dimension)
  observation_smooth : ContMDiff (𝓡 n) (𝓡 dimension) ∞ observation
  observation_embedding : IsClosedEmbedding observation
  observation_readable : SUChartReadable (n := n) observation
  sphere : UnitTwoSphere → M
  smooth : ContMDiff (𝓡 2) (𝓡 n) ∞ sphere
  nonconstant : ∃ p q : UnitTwoSphere, sphere p ≠ sphere q
  harmonic : M60SphereChartHarmonic g sphere
  energy_bound : m60SphereEnergy g sphere ≤
    sInf (m60SphereArea g ''
      {h | ContMDiff (𝓡 2) (𝓡 n) 1 h ∧ ¬ IsNullHomotopicSphere h})
  retained : ¬ IsNullHomotopicSphere sphere ∨
    ∃ (k : ℕ → ℕ) (center : ℕ → UnitTwoSphere) (scale : ℕ → ℝ),
      StrictMono k ∧ (∀ j, 0 < scale j) ∧ Tendsto scale atTop (𝓝 0) ∧
      let v := fun j z => f (k j) ((chartAt LoopPlane (center j)).symm (scale j • z))
      TendstoLocallyUniformly (fun j => observation ∘ v j)
        (observation ∘ sphere ∘ m60SphereParameter) atTop ∧
      TendstoLocallyUniformly (fun j => fderiv ℝ (observation ∘ v j))
        (fderiv ℝ (observation ∘ sphere ∘ m60SphereParameter)) atTop ∧
      ∀ R : ℝ, 0 < R →
        Tendsto (fun j => ∫ z in Metric.ball (0 : LoopPlane) R, m60AreaDensity g (v j) z)
          atTop (𝓝 (∫ z in Metric.ball (0 : LoopPlane) R, m60SphereAreaDensity g sphere z))

/-- Exact reserved theorem type, without any generic harmonic-map
compactness hypothesis. The source sequence consists of actual smooth
non-null alpha minima, and the weighted equation is literal. -/
def SUMaxGradientCompactnessProducer (g : RiemannianMetric n M) : Prop :=
  ∀ (alpha : ℕ → ℝ) (f : ℕ → UnitTwoSphere → M),
    Tendsto alpha atTop (𝓝 1) →
    (∀ j, 1 ≤ alpha j ∧ alpha j ≤ 33 / 32) →
    (∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j)) →
    (∀ j, ¬ IsNullHomotopicSphere (f j)) →
    (∀ j (h : UnitTwoSphere → M), ContMDiff (𝓡 2) (𝓡 n) ∞ h →
      ¬ IsNullHomotopicSphere h →
      m60SphereAlphaEnergy g (alpha j) (f j) ≤ m60SphereAlphaEnergy g (alpha j) h) →
    (∀ j, SUSphereWeightedEuler g (alpha j) (f j)) →
    Nonempty (SUMaxGradientLimit g f)

end PoincareMT.M60
