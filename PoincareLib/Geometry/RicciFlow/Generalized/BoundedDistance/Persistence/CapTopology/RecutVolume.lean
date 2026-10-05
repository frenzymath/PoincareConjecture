import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Persistence.CapTopology.QuantitativeRecut

/-!
# Normalized volume bounds on actual cap recuts

Morgan--Tian Proposition 9.79, pp. 232-234. The scalar-ratio field of an
actual cap bounds its scalar range. On any nonempty subset, the scalar
supremum decreases, so the allowance with exponent `-3/2` increases while
the calibrated volume decreases. See the task derivation
`cap-topology/2026-09-23-recut-quantitative-producers.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}

/-- On every nonempty subset of an actual cap, the scalar supremum is
positive and no larger than the old scalar supremum. The old scalar-ratio
witness supplies boundedness, without assuming supremum attainment. -/
theorem scalar_sup_pos_and_le_of_subset (N : CapCertificate g)
    {V : Set M} (hne : V.Nonempty) (hV : V ⊆ N.carrier) :
    0 < scalarCurvatureSupOn g N.connection V ∧
      scalarCurvatureSupOn g N.connection V ≤
        scalarCurvatureSupOn g N.connection N.carrier := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨b, _, hb⟩ := N.scalar_ratio
  have hbounded : BddAbove (range (fun z : N.carrier =>
      N.connection.scalarCurvature z.1)) := by
    refine ⟨b * N.connection.scalarCurvature x, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hb x (hV hx) y.1 y.2
  have hsubset : range (fun z : V => N.connection.scalarCurvature z.1) ⊆
      range (fun z : N.carrier => N.connection.scalarCurvature z.1) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨y.1, hV y.2⟩, rfl⟩
  have hmem : N.connection.scalarCurvature x ∈
      range (fun z : V => N.connection.scalarCurvature z.1) :=
    ⟨⟨x, hx⟩, rfl⟩
  exact ⟨(N.scalar_pos x (hV hx)).trans_le
      (le_csSup (hbounded.mono hsubset) hmem),
    csSup_le_csSup hbounded ⟨_, hmem⟩ hsubset⟩

/-- Every nonempty subset of the old cap inherits its strict normalized
calibrated-volume bound with the unchanged old cap constant. -/
theorem normalized_volume_bound_of_subset (N : CapCertificate g)
    {V : Set M} (hne : V.Nonempty) (hV : V ⊆ N.carrier) :
    calibratedMetricVolume g V < ENNReal.ofReal N.cap_constant *
      ENNReal.ofReal (scalarCurvatureSupOn g N.connection V ^ (-3 / 2 : ℝ)) := by
  obtain ⟨hpos, hsup⟩ := N.scalar_sup_pos_and_le_of_subset hne hV
  have hpower := Real.rpow_le_rpow_of_nonpos hpos hsup
    (show (-3 / 2 : ℝ) ≤ 0 by norm_num)
  exact ((MeasureTheory.measure_mono hV).trans_lt N.volume_bound).trans_le
    (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hpower))

/-- Construct the old-metric quantitative recut margins from actual
diameter and core-ball confinement. The volume field is now produced
from the old cap, rather than supplied as a target conclusion. -/
theorem exists_quantitative_cap_recut_margins_of_diameter_and_core_balls
    (N : CapCertificate g) {V : Set M}
    (hne : V.Nonempty) (hV : V ⊆ N.carrier)
    (hdiam : intrinsicDiameter g V <
      ENNReal.ofReal ((N.cap_constant + 1) *
        scalarCurvatureSupOn g N.connection V ^ (-1 / 2 : ℝ)))
    (hball : ∀ y ∈ N.core,
      closure (g.ball y (N.core_radius y)) ⊆ V) :
    Nonempty (QuantitativeCapRecutMargins N V) := by
  apply N.exists_quantitative_cap_recut_margins_of_old_cap hV hdiam _ hball
  exact (N.normalized_volume_bound_of_subset hne hV).trans_le
    (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (show N.cap_constant ≤ N.cap_constant + 1 by linarith)) le_rfl)

end PoincareMT.CapCertificate
