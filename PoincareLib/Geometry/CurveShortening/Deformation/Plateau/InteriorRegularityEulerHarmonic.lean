import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.InteriorRegularityEulerChart
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.InteriorRegularityEulerEquation

/-!
# Actual weak harmonic charts of the local energy minimum

The actual local minimum and its continuous representative construct
the chart weak graph, the true coordinate metric and connection, and
the literal weak harmonic equation. All target variations and their
stationarity are discharged internally.
Morrey ICM 1950, pp. 183-185; MT Lemma 19.2, pp. 437-438;
M65 derivations 44 and 47.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

universe u

namespace PoincareMT.M65Euler

/-- Every actual local weak minimum has genuine canonical weak
harmonic coordinates near each interior point. The true derivative
fields still reconstruct the original embedding, and the actual
metric agrees with the original pullback on the captured target.
No variation, stationarity or weak PDE is an input.
Morrey ICM pp. 183-185; MT Lemma 19.2, pp. 437-438; derivation 44. -/
theorem exists_weak_harmonic_chart {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e) (heinj : Function.Injective e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    {U : Set LoopPlane} (hU : IsOpen U) (F : M65LocalWeakMap e U)
    (hmin : M65LocallyMinimizesEnergy g F) (q : LoopPlane → M)
    (hqcont : ContinuousOn q U) (hq : q =ᵐ[volume.restrict U] F.value)
    {x : LoopPlane} (hx : x ∈ U) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧ closedBall x (8 * R) ⊆ U ∧
      ∃ (gE : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (DE : LeviCivitaData gE)
        (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin 3) => y) (ball x (8 * R))),
        (∀ z, X.value z = extChartAt (𝓡 3) (q x) (q z)) ∧
        ContinuousOn X.value (ball x (8 * R)) ∧
        (∀ z ∈ ball x (8 * R), q z ∈ (extChartAt (𝓡 3) (q x)).source) ∧
        MapsTo X.value (ball x (8 * R))
          (ball (extChartAt (𝓡 3) (q x) (q x)) (ε / 2)) ∧
        (∀ y ∈ ball (extChartAt (𝓡 3) (q x) (q x)) ε,
          y ∈ (extChartAt (𝓡 3) (q x)).target ∧
            ∀ v w : EuclideanSpace ℝ (Fin 3), gE.inner y v w =
              g.inner ((extChartAt (𝓡 3) (q x)).symm y)
                (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q x)).symm y v)
                (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q x)).symm y w)) ∧
        (∀ i, F.derivative i =ᵐ[volume.restrict (ball x (8 * R))] fun z =>
          fderiv ℝ (e ∘ (extChartAt (𝓡 3) (q x)).symm)
            (extChartAt (𝓡 3) (q x) (q z)) (X.derivative i z)) ∧
        ∀ (k : Fin 3) (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ →
          tsupport φ ⊆ ball x R →
          IntegrableOn (fun z => ∑ i : Fin 2,
            (M65Gauss.connectionCoefficient DE (X.value z)
              (X.derivative i z) (X.derivative i z)) k) (closedBall x (2 * R)) ∧
          (∫ z in closedBall x (2 * R), ∑ i : Fin 2,
            fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * (X.derivative i z) k) =
            ∫ z in closedBall x (2 * R), φ z * ∑ i : Fin 2,
              (M65Gauss.connectionCoefficient DE (X.value z)
                (X.derivative i z) (X.derivative i z)) k := by
  obtain ⟨R, ε, hR, hε, hRU, gE, DE, X, hX, hsource, hcap, hmetric, hfield, hcmp⟩ :=
    exists_variational_chart g e he heinj hinj hU F hmin q hqcont hq hx
  have hXc : ContinuousOn X.value (ball x (8 * R)) := by
    have hsub : ball x (8 * R) ⊆ U := ball_subset_closedBall.trans hRU
    apply ((continuousOn_extChartAt (I := 𝓡 3) (q x)).comp
      (hqcont.mono hsub) hsource).congr
    intro z _
    exact hX z
  exact ⟨R, ε, hR, hε, hRU, gE, DE, X, hX, hXc, hsource, hcap, hmetric, hfield,
    variational_weak_equation DE x hR X _ hε hcap hcmp⟩

end PoincareMT.M65Euler
