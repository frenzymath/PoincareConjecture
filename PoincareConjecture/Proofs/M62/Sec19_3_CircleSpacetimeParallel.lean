import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductIdentities
import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeIdentities

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem CircleProductData.spacetime_parallel
    {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : CircleProductData F circumference) (G : SpacetimeData P.flow) :
    CircleUnitSpacetimeParallel P G := by
  let := P.charts.chartedSpace
  let := G.charts.chartedSpace
  let B : ℝ → (p : P.charts.Point) → TangentSpace (𝓡 (n + 1)) p :=
    fun _ => P.charts.circleUnit
  have hP := circleProduct_identities P
  have hB : G.charts.IsSmoothField (G.charts.liftSpatialField B) :=
    (G.charts.liftSpatialField_smooth_iff B).mpr
      (hP.circle_unit_smooth.comp contMDiff_fst)
  have hfixed (p : P.charts.Point) (t : ℝ) : fixedPointTimeDerivative B p t = 0 := by
    simp only [fixedPointTimeDerivative, B, deriv_const, map_zero]
  have hspace (q : G.charts.Point) (V : TangentSpace (𝓡 (n + 1)) q.1) :
      G.connection.connection (G.charts.liftSpatialField B) q
        (G.charts.horizontal q V) = 0 := by
    apply (G.charts.split q).injective
    rw [G.spatial_connection B hB, map_zero]
    exact Prod.ext (hP.circle_parallel q.2 q.1 V) (hP.circle_ricci q.2 q.1 V)
  have htime (q : G.charts.Point) :
      G.connection.connection (G.charts.liftSpatialField B) q (G.charts.timeVector q) = 0 := by
    let N := G.connection.connection (G.charts.liftSpatialField B) q (G.charts.timeVector q)
    have hv : (G.charts.split q N).2 = 0 := G.time_spatial_vertical B hB q
    have hh : G.charts.horizontal q (G.charts.split q N).1 = N := by
      simpa only [hv, zero_smul, add_zero] using G.charts.horizontal_time_decomposition q N
    have hp := G.time_spatial_pairing B hB q (G.charts.split q N).1
    rw [hfixed, map_zero, zero_apply, zero_sub] at hp
    have hr : (P.flow.connection q.2).ricci q.1 (B q.2 q.1) (G.charts.split q N).1 = 0 := by
      rw [M04.ricci_symm]
      exact hP.circle_ricci q.2 q.1 _
    rw [hr, neg_zero, hh] at hp
    change G.metric.inner q N N = 0 at hp
    change N = 0
    by_contra hne
    exact (ne_of_gt (G.metric.pos q N hne)) hp
  intro q V
  change G.connection.connection (G.charts.liftSpatialField B) q V = 0
  rw [← G.charts.horizontal_time_decomposition q V, map_add, map_smul,
    hspace, htime, smul_zero, add_zero]

end PoincareConjecture.M62
