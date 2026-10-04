import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.CurvatureRadius

/-!
# A strict outer margin around each actual cap curvature ball

Morgan-Tian Definition 9.72, pp. 230-231, in Theorem 12.28,
pp. 323-324. Compact containment and short-path radial projection give
an enlarged ball still inside the open cap. The exact original radius
then gives a strict scalar-supremum crossing on every enlarged ball.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M35

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [ConnectedSpace M]

/-- Definition 9.72 in Theorem 12.28: a compact Riemannian ball
strictly inside an open set has an enlarged closed ball in the same set. -/
theorem exists_larger_ball_closure_subset (g : RiemannianMetric 3 M)
    (x : M) {r : ℝ} (hr : 0 < r) {U : Set M} (hU : IsOpen U)
    (hcompact : IsCompact (closure (g.ball x r)))
    (hsub : closure (g.ball x r) ⊆ U) :
    ∃ b : ℝ, r < b ∧ closure (g.ball x b) ⊆ U := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  obtain ⟨d, hd, hthick⟩ := hcompact.exists_thickening_subset_open hU hsub
  refine ⟨r + d / 3, by linarith, ?_⟩
  rw [riemannian_closure_ball g x (by linarith : 0 < r + d / 3)]
  have hproj := Proofs.M09.selectedMetricSpace_radial_projection g x
    (r + d / 3) r (d / 3) hr.le (by linarith) (by positivity)
  intro y hy
  apply hthick
  rw [riemannian_closure_ball g x hr]
  exact (thickening_mono (show r + d / 3 - r + d / 3 ≤ d by linarith)
    (closedBall x r)) (hproj hy)

/-- Definition 9.72 in Theorem 12.28: enlarging an exact positive
curvature radius produces a strict scalar-supremum crossing, witnessed
already by a point of the original open ball. -/
theorem exists_scalar_witness_in_curvature_ball (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (x : M) {r a : ℝ} (hr : 0 < r) (hra : r < a)
    (hscale : scalarCurvatureSupOn g D (g.ball x r) = r⁻¹ ^ 2) :
    ∃ z ∈ g.ball x r, 1 < a ^ 2 * D.scalarCurvature z := by
  have ha : 0 < a := hr.trans hra
  have hinv : a⁻¹ < r⁻¹ := inv_lt_inv₀ ha hr |>.mpr hra
  have hinvsq : a⁻¹ ^ 2 < r⁻¹ ^ 2 :=
    pow_lt_pow_left₀ hinv (inv_nonneg.mpr ha.le) (by omega)
  have hnonempty : (range fun z : g.ball x r => D.scalarCurvature z.1).Nonempty := by
    have hx : x ∈ g.ball x r := by
      let : MetricSpace M := Proofs.M09.selectedMetricSpace g
      change g.edist x x < ENNReal.ofReal r
      rw [← Proofs.M09.selectedMetricSpace_edist g, edist_self]
      exact ENNReal.ofReal_pos.mpr hr
    exact ⟨D.scalarCurvature x, ⟨⟨x, hx⟩, rfl⟩⟩
  change sSup (range fun z : g.ball x r => D.scalarCurvature z.1) = r⁻¹ ^ 2 at hscale
  obtain ⟨v, hv, hvalue⟩ := exists_lt_of_lt_csSup hnonempty (hscale ▸ hinvsq)
  obtain ⟨z, rfl⟩ := hv
  refine ⟨z, z.property, ?_⟩
  have hmul := mul_lt_mul_of_pos_left hvalue (sq_pos_of_pos ha)
  rw [← mul_pow, mul_inv_cancel₀ ha.ne', one_pow] at hmul
  exact hmul

end PoincareMT.M35

namespace PoincareMT.CapCertificate

/-- Definition 9.72 in Theorem 12.28: each actual cap core point
has a buffered outer ball and a strict scalar crossing before that buffer.
The witness remains inside its original exact curvature ball. -/
theorem exists_buffered_core_scalar_witness
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g) {y : M} (hy : y ∈ N.core) :
    ∃ a b : ℝ, N.core_radius y < a ∧ a < b ∧
      closure (g.ball y b) ⊆ N.carrier ∧
        ∃ z ∈ g.ball y (N.core_radius y), 1 < a ^ 2 * N.connection.scalarCurvature z := by
  obtain ⟨b, hb, hsub⟩ := M35.exists_larger_ball_closure_subset g y
    (N.core_radius_pos y hy) N.carrier_open (N.core_ball_compact y hy)
    (N.core_ball_subset y hy)
  obtain ⟨a, hra, hab⟩ := exists_between hb
  exact ⟨a, b, hra, hab, hsub, M35.exists_scalar_witness_in_curvature_ball
    g N.connection y (N.core_radius_pos y hy) hra (N.core_radius_eq y hy)⟩

end PoincareMT.CapCertificate
