import PoincareLib.Topology.Connected.FiniteCoverDiameter
import PoincareLib.Geometry.Curvature.Integral.Concentration.BallCover

/-!
# Intrinsic diameter bounds from local control in an ambient ball

The Bishop--Gromov cover and a local distance comparison bound the diameter
of a preconnected metric space mapped into an ambient unit ball.

Reference: Petrunin (2009), Section 4.5, manuscript p. 9.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.RiemannianMetric

/-- A local distance bound becomes global with a factor depending only on the
ambient dimension and the local comparison radius. -/
theorem dist_le_of_unitBall_cover_and_local_distance_bound
    {n : ℕ} {M X : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [PseudoMetricSpace X] [PreconnectedSpace X]
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n)
    {r d : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 ≤ d)
    (hcomplete : MetricComplete g) (D : LeviCivitaData g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    (f : X → M) (hf : ∀ x, f x ∈ g.ball p 1)
    (hlocal : ∀ x y : X, (g.edist (f x) (f y)).toReal < 2 * r → dist x y ≤ d)
    (x y : X) :
    dist x y ≤ (⌈modelVolume n 1 3 / modelVolume n 1 (r / 2)⌉₊ : ℝ) * d := by
  classical
  let : MetricSpace M := g.toMetricSpace
  obtain ⟨S, _, _, hcard, hcover⟩ :=
    g.exists_finset_unitBall_cover p hn hr hr1 hcomplete D hsec
  have hcover' (z : X) : ∃ i : S, dist (f z) i.val < r := by
    obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp (hcover (hf z))
    refine ⟨⟨q, hq⟩, ?_⟩
    rw [← g.toMetricSpace_ball] at hzq
    exact hzq
  have hbound := Poincare.Topology.dist_le_card_mul_of_image_ball_cover f
    (fun q : S => q.val) hd hcover' hlocal x y
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ hd
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    (show (S.card : ℝ) ≤ ⌈modelVolume n 1 3 / modelVolume n 1 (r / 2)⌉₊ by
      exact_mod_cast hcard)

end PoincareMT.RiemannianMetric

