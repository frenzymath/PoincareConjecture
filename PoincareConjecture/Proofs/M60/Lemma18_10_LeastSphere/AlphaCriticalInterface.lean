import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Derivatives











set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open Poincare.Analysis.Sobolev.Weak

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


def suAlphaRoundFactor (z : LoopPlane) : ℝ := 16 / (‖z‖ ^ 2 + 4) ^ 2


def suAlphaChartCoordinate (f : C(UnitTwoSphere, M)) (p : UnitTwoSphere) :
    LoopPlane → EuclideanSpace ℝ (Fin n) :=
  (chartAt (EuclideanSpace ℝ (Fin n)) (f p)) ∘ f ∘ (chartAt LoopPlane p).symm



def suAlphaChartVariation (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (u : LoopPlane → EuclideanSpace ℝ (Fin n))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n))
    (phi : LoopPlane → EuclideanSpace ℝ (Fin n)) (z : LoopPlane) : ℝ :=
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  let Q := ∑ i : Fin 2, G (u z) (V i z) (V i z)
  alpha * (1 + Q / suAlphaRoundFactor z) ^ (alpha - 1) *
    ((∑ i : Fin 2, fderiv ℝ G (u z) (phi z) (V i z) (V i z)) +
      2 * ∑ i : Fin 2, G (u z) (V i z)
        (fderiv ℝ phi z (EuclideanSpace.single i 1)))



structure SUWeakAlphaChart (g : RiemannianMetric n M) (alpha : ℝ)
    (f : C(UnitTwoSphere, M)) (p : UnitTwoSphere) where
  radius : ℝ
  radius_pos : 0 < radius
  chart_range : MapsTo (f ∘ (chartAt LoopPlane p).symm)
    (Metric.closedBall ((chartAt LoopPlane p) p) radius)
    (chartAt (EuclideanSpace ℝ (Fin n)) (f p)).source
  coordinate_continuous : ContinuousOn (suAlphaChartCoordinate (n := n) f p)
    (Metric.closedBall ((chartAt LoopPlane p) p) radius)
  coordinate_memLp : MemLp (suAlphaChartCoordinate (n := n) f p) (ENNReal.ofReal (2 * alpha))
    (volume.restrict (Metric.ball ((chartAt LoopPlane p) p) radius))
  column : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)
  column_memLp : ∀ i, MemLp (column i) (ENNReal.ofReal (2 * alpha))
    (volume.restrict (Metric.ball ((chartAt LoopPlane p) p) radius))
  weak_derivative : ∀ (i : Fin 2) (a : Fin n),
    HasWeakPartialDeriv i (fun z => column i z a)
      (fun z => suAlphaChartCoordinate (n := n) f p z a)
      (Metric.ball ((chartAt LoopPlane p) p) radius)
  variation_integrable : ∀ phi : LoopPlane → EuclideanSpace ℝ (Fin n),
    ContDiff ℝ ∞ phi → HasCompactSupport phi →
    tsupport phi ⊆ Metric.ball ((chartAt LoopPlane p) p) radius →
    IntegrableOn
      (suAlphaChartVariation g (f p) alpha (suAlphaChartCoordinate (n := n) f p) column phi)
      (Metric.ball ((chartAt LoopPlane p) p) radius)
  variation_zero : ∀ phi : LoopPlane → EuclideanSpace ℝ (Fin n),
    ContDiff ℝ ∞ phi → HasCompactSupport phi →
    tsupport phi ⊆ Metric.ball ((chartAt LoopPlane p) p) radius →
    (∫ z in Metric.ball ((chartAt LoopPlane p) p) radius,
      suAlphaChartVariation g (f p) alpha (suAlphaChartCoordinate (n := n) f p) column phi z) = 0




structure SUWeakAlphaSphere (g : RiemannianMetric n M) (eps0 alpha : ℝ) where
  alpha_mem : alpha ∈ Ioo 1 (1 + eps0)
  map : C(UnitTwoSphere, M)
  chart : ∀ p : UnitTwoSphere, SUWeakAlphaChart g alpha map p




structure SUWeakAlphaCoordinate (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (u : LoopPlane → EuclideanSpace ℝ (Fin n))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n))
    (center : LoopPlane) (radius : ℝ) where
  radius_pos : 0 < radius
  coordinate_range : MapsTo u (Metric.closedBall center radius) (extChartAt (𝓡 n) b).target
  coordinate_continuous : ContinuousOn u (Metric.closedBall center radius)
  coordinate_memLp : MemLp u (ENNReal.ofReal (2 * alpha))
    (volume.restrict (Metric.ball center radius))
  column_memLp : ∀ i, MemLp (V i) (ENNReal.ofReal (2 * alpha))
    (volume.restrict (Metric.ball center radius))
  weak_derivative : ∀ (i : Fin 2) (a : Fin n),
    HasWeakPartialDeriv i (fun z => V i z a) (fun z => u z a)
      (Metric.ball center radius)
  variation_integrable : ∀ phi : LoopPlane → EuclideanSpace ℝ (Fin n),
    ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ Metric.ball center radius →
    IntegrableOn (suAlphaChartVariation g b alpha u V phi) (Metric.ball center radius)
  variation_zero : ∀ phi : LoopPlane → EuclideanSpace ℝ (Fin n),
    ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ Metric.ball center radius →
    (∫ z in Metric.ball center radius, suAlphaChartVariation g b alpha u V phi z) = 0






def SUAlphaOneSmoothness (g : RiemannianMetric n M) : Prop :=
  ∀ (b : M) (u : LoopPlane → EuclideanSpace ℝ (Fin n))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)) (center : LoopPlane) (radius : ℝ),
    SUWeakAlphaCoordinate g b 1 u V center radius → ContDiffAt ℝ ∞ u center



theorem SUWeakAlphaChart.coordinateData {g : RiemannianMetric n M} {alpha : ℝ}
    {f : C(UnitTwoSphere, M)} {p : UnitTwoSphere} (S : SUWeakAlphaChart g alpha f p) :
    SUWeakAlphaCoordinate g (f p) alpha (suAlphaChartCoordinate (n := n) f p) S.column
      ((chartAt LoopPlane p) p) S.radius where
  radius_pos := S.radius_pos
  coordinate_range := by
    intro z hz
    simpa only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id_eq,
      modelWithCornersSelf_coe, Set.range_id, Set.inter_univ, id_eq,
      suAlphaChartCoordinate, Function.comp_apply] using
      (chartAt (EuclideanSpace ℝ (Fin n)) (f p)).map_source (S.chart_range hz)
  coordinate_continuous := S.coordinate_continuous
  coordinate_memLp := S.coordinate_memLp
  column_memLp := S.column_memLp
  weak_derivative := S.weak_derivative
  variation_integrable := S.variation_integrable
  variation_zero := S.variation_zero



structure SUInitialGain {m : ℕ}
    (u : LoopPlane → EuclideanSpace ℝ (Fin m))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
    (center : LoopPlane) (outerRadius : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt : radius < outerRadius
  coordinate_continuous : ContinuousOn u (Metric.closedBall center radius)
  coordinate_memLp : MemLp u 2 (volume.restrict (Metric.ball center radius))
  column_memLp : ∀ q : ℝ, 1 ≤ q → ∀ i : Fin 2,
    MemLp (V i) (ENNReal.ofReal q) (volume.restrict (Metric.ball center radius))
  weak_derivative : ∀ (i : Fin 2) (a : Fin m),
    HasWeakPartialDeriv i (fun z => V i z a) (fun z => u z a)
      (Metric.ball center radius)
  hessian : Fin 2 → Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)
  hessian_memLp : ∀ i j, MemLp (hessian i j) 2
    (volume.restrict (Metric.ball center radius))
  second_weak_derivative : ∀ (i j : Fin 2) (a : Fin m),
    HasWeakPartialDeriv j (fun z => hessian i j z a) (fun z => V i z a)
      (Metric.ball center radius)




structure SUQuadraticWeakSystem {m : ℕ}
    (u : LoopPlane → EuclideanSpace ℝ (Fin m))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
    (center : LoopPlane) (radius : ℝ) where
  radius_pos : 0 < radius
  coordinate_continuous : ContinuousOn u (Metric.closedBall center radius)
  coordinate_memLp : MemLp u 2 (volume.restrict (Metric.ball center radius))
  column_memLp : ∀ i, MemLp (V i) 2 (volume.restrict (Metric.ball center radius))
  weak_derivative : ∀ (i : Fin 2) (a : Fin m),
    HasWeakPartialDeriv i (fun z => V i z a) (fun z => u z a)
      (Metric.ball center radius)
  targetRadius : ℝ
  targetRadius_pos : 0 < targetRadius
  coordinate_range : MapsTo u (Metric.closedBall center radius)
    (Metric.ball (u center) (targetRadius / 2))
  flux : (LoopPlane × EuclideanSpace ℝ (Fin m)) →
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ
  source : (LoopPlane × EuclideanSpace ℝ (Fin m)) →
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →
    EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ
  nu : ℝ
  constant : ℝ
  nu_pos : 0 < nu
  constant_pos : 0 < constant
  flux_continuous : ContinuousOn (fun z => flux z.1 z.2)
    ((Metric.closedBall center radius ×ˢ Metric.closedBall (u center) targetRadius) ×ˢ univ)
  source_continuous : ContinuousOn (fun z => source z.1 z.2)
    ((Metric.closedBall center radius ×ˢ Metric.closedBall (u center) targetRadius) ×ˢ univ)
  flux_bound : ∀ x ∈ Metric.closedBall center radius ×ˢ
      Metric.closedBall (u center) targetRadius, ∀ q,
    ‖flux x q‖ ≤ constant * (1 + ‖q‖)
  source_bound : ∀ x ∈ Metric.closedBall center radius ×ˢ
      Metric.closedBall (u center) targetRadius, ∀ q,
    ‖source x q‖ ≤ constant * (1 + ‖q‖ ^ 2)
  flux_monotone : ∀ x ∈ Metric.closedBall center radius ×ˢ
      Metric.closedBall (u center) targetRadius, ∀ q r,
    nu * ‖q - r‖ ^ 2 ≤ (flux x q - flux x r) (q - r)
  flux_gradient_bound : ∀ x ∈ Metric.closedBall center radius ×ˢ
      Metric.closedBall (u center) targetRadius, ∀ q r,
    ‖flux x q - flux x r‖ ≤ constant * ‖q - r‖
  flux_base_bound : ∀ x ∈ Metric.closedBall center radius ×ˢ
      Metric.closedBall (u center) targetRadius,
    ∀ y ∈ Metric.closedBall center radius ×ˢ Metric.closedBall (u center) targetRadius, ∀ q,
      ‖flux y q - flux x q‖ ≤ constant * (1 + ‖q‖) * ‖y - x‖
  source_gradient_bound : ∀ x ∈ Metric.closedBall center radius ×ˢ
      Metric.closedBall (u center) targetRadius, ∀ q r,
    ‖source x q - source x r‖ ≤ constant * (1 + ‖q‖ + ‖r‖) * ‖q - r‖
  source_base_bound : ∀ x ∈ Metric.closedBall center radius ×ˢ
      Metric.closedBall (u center) targetRadius,
    ∀ y ∈ Metric.closedBall center radius ×ˢ Metric.closedBall (u center) targetRadius, ∀ q,
      ‖source y q - source x q‖ ≤ constant * (1 + ‖q‖ ^ 2) * ‖y - x‖
  flux_integrable : ∀ phi : LoopPlane → EuclideanSpace ℝ (Fin m),
    ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ Metric.ball center radius →
    IntegrableOn (fun z => flux (z, u z) (V 0 z, V 1 z)
      (fderiv ℝ phi z (EuclideanSpace.single 0 1),
        fderiv ℝ phi z (EuclideanSpace.single 1 1))) (Metric.ball center radius)
  source_integrable : ∀ phi : LoopPlane → EuclideanSpace ℝ (Fin m),
    ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ Metric.ball center radius →
    IntegrableOn (fun z => source (z, u z) (V 0 z, V 1 z) (phi z))
      (Metric.ball center radius)
  equation : ∀ phi : LoopPlane → EuclideanSpace ℝ (Fin m),
    ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ Metric.ball center radius →
    (∫ z in Metric.ball center radius, flux (z, u z) (V 0 z, V 1 z)
      (fderiv ℝ phi z (EuclideanSpace.single 0 1),
        fderiv ℝ phi z (EuclideanSpace.single 1 1))) =
      ∫ z in Metric.ball center radius, source (z, u z) (V 0 z, V 1 z) (phi z)

end PoincareConjecture.M60
