import PoincareConjecture.Proofs.Horizon.Topology.Connected.MetricCover
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.BallCover









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric



theorem connectedComponents_card_le_of_unitBall_local_connectivity
    {n : ℕ} {M X : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [TopologicalSpace X]
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hcomplete : MetricComplete g) (D : LeviCivitaData g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    (f : X → M) (hf : ∀ x, f x ∈ g.ball p 1)
    (hlocal : ∀ x y : X, (g.edist (f x) (f y)).toReal < 2 * r →
      x ∈ connectedComponent y) :
    Finite (ConnectedComponents X) ∧
      Nat.card (ConnectedComponents X) ≤
        ⌈modelVolume n 1 3 / modelVolume n 1 (r / 2)⌉₊ := by
  classical
  let : MetricSpace M := g.toMetricSpace
  obtain ⟨S, _, _, hcard, hcover⟩ :=
    g.exists_finset_unitBall_cover p hn hr hr1 hcomplete D hsec
  have hcover' (x : X) : ∃ i : S, dist (f x) i.val < r := by
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hcover (hf x))
    refine ⟨⟨q, hq⟩, ?_⟩
    rw [← g.toMetricSpace_ball] at hxq
    exact hxq
  obtain ⟨hfinite, hbound⟩ := Poincare.Topology.components_card_le_of_image_ball_cover f
    (fun q : S => q.val) hcover' hlocal
  refine ⟨hfinite, hbound.trans ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard

end PoincareConjecture.RiemannianMetric
