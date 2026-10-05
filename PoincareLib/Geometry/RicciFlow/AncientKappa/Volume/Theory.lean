import PoincareLib.Geometry.RicciFlow.AncientKappa.Volume.Basic
import PoincareLib.Geometry.Riemannian.Curvature.Calculus

/-!
# Slice-wise asymptotic volume theory

Declaration bodies from `PoincareMT/Definitions/M21AsymptoticVolume.lean`
and `PoincareMT/Statements/M21AsymptoticVolume.lean` at Mapher commit
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.
Morgan--Tian, Theorem 1.34, pp. 19--20, and Section 9.6, pp. 221--222.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- Bishop--Gromov and asymptotic-ratio data for one ancient-flow slice. -/
structure AsymptoticVolumeRatioSliceData
    (K : AncientKappaSolution n M) (t : ℝ) where
  time_mem : t ≤ 0
  ratio_antitone : ∀ p : M,
    AntitoneMetricBallVolumeRatio (K.flow.metric t) p
  ratio_limit : ∀ p : M,
    HasAsymptoticVolumeRatio (K.flow.metric t) p
  basepoint_independent :
    AsymptoticVolumeRatioBasepointIndependent (K.flow.metric t)

/-- M04's static tensor calculus on the actual metric and connection.
This is the only earlier theorem service used by the M21 slice argument. -/
def AsymptoticVolumeRatioPredecessors (n : ℕ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus

/-- The M21 slice-by-slice asymptotic volume ratio theory. The numbered
theorem supplies its predecessors once, before any slice is selected. -/
structure AsymptoticVolumeRatioTheory (n : ℕ) : Prop where
  slice : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (t : ℝ), t ≤ 0 →
    Nonempty (AsymptoticVolumeRatioSliceData K t)

end PoincareMT
