import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareLib.Geometry.Riemannian.Connection.Uniqueness
import PoincareLib.Geometry.Riemannian.Surface.Regularity

/-!
# Compact lower bounds for neck scales

The compact branch of Morgan--Tian Proposition 2.19 is independent of the
neck separation argument.  The scalar curvature of the actual metric is
continuous, and the retained connection stored in a neck computes the same
curvature as any other Levi--Civita data for that metric.

Reference: Morgan--Tian, Proposition 2.19, p. 31 and proof pp. 31--32.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

private theorem scalarCurvature_eq_of_metric
    (g : RiemannianMetric 3 M) (D D' : LeviCivitaData g) (x : M) :
    D.scalarCurvature x = D'.scalarCurvature x := by
  unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
  simp_rw [D.curvatureTensor_eq D' x]

/-- On a compact manifold, every actual epsilon-neck has scale bounded below.

The bound depends only on the fixed metric and connection, while the necks
retain their original scalar-normalized scale definition. -/
theorem exists_neck_scale_lower_bound_of_compact
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcompact : IsCompact (Set.univ : Set M)) (hM : Nonempty M)
    (hpositive : ∀ x : M, 0 < D.scalarCurvature x) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ N : EpsilonNeck g, rho ≤ N.scale := by
  letI : Nonempty M := hM
  obtain ⟨p, hp, hpmax⟩ := hcompact.exists_isMaxOn
    (show (Set.univ : Set M).Nonempty from Set.univ_nonempty)
    D.continuous_scalarCurvature.continuousOn
  have hpR : 0 < D.scalarCurvature p := hpositive p
  let rho : ℝ := D.scalarCurvature p ^ (-1 / 2 : ℝ)
  have hrho : 0 < rho := Real.rpow_pos_of_pos hpR _
  refine ⟨rho, hrho, ?_⟩
  intro N
  have hmax : D.scalarCurvature N.center ≤ D.scalarCurvature p :=
    hpmax (Set.mem_univ _)
  have hscalar : N.connection.scalarCurvature N.center =
      D.scalarCurvature N.center :=
    scalarCurvature_eq_of_metric g N.connection D N.center
  rw [N.scale_eq_scalar, hscalar]
  exact Real.rpow_le_rpow_of_nonpos (hpositive _) hmax (by norm_num)

end PoincareMT
