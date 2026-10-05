import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsSourceInitialAxialPath
import PoincareLib.Geometry.Riemannian.Distance.CompactConfinement

/-!
# Actual tip distance controls the old axial position

The path-length infimum preserves the retained collar barrier in the
ambient output, including paths which leave that collar.
Morgan--Tian Lemma 17.7, pp. 405-406; blowup-source-old-axial.md, I6B.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {g0 : StandardInitialMetric}
  {K : MetricSurgeryConstants} {I : MetricSurgeryInput K g}

/-- Ambient shortcuts cannot avoid the actual central-sphere crossing
between a retained negative old point and the surgery tip. -/
theorem source_initial_old_height_le_tip_distance
    (R : MetricSurgeryResult g0 I) {y : M}
    (hy : y ∈ I.neck.region (-I.neck.epsilon⁻¹) 0) :
    ENNReal.ofReal (I.neck.scale / 2 * |(I.neck.coordinate_inverse y).2|) ≤
      R.metric.edist R.tip (R.collapse y) := by
  by_contra hnot
  have hd := lt_of_not_ge hnot
  have hball : R.tip ∈ R.metric.ball (R.collapse y)
      (I.neck.scale / 2 * |(I.neck.coordinate_inverse y).2|) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : R.output.carrier → Type _) :=
      ⟨R.metric.toRiemannianMetric⟩
    change R.metric.edist (R.collapse y) R.tip < _
    change Manifold.riemannianEDist (𝓡 3) (R.collapse y) R.tip < _
    rw [Manifold.riemannianEDist_comm]
    exact hd
  obtain ⟨p, hp0, hp1, hp, hlength, _⟩ :=
    R.metric.exists_short_path_in_ball (R.collapse y) R.tip hball
  exact not_lt_of_ge (source_initial_old_height_le_path_length R hy p hp hp0 hp1) hlength

end PoincareMT.M47
