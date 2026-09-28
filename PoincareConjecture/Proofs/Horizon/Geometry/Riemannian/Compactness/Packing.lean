import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Covering
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Packing.Bounds










noncomputable section
set_option autoImplicit false

open Set Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]


def toBasedMetricSpace (g : RiemannianMetric n M) (p : M) : BasedMetricSpaceBundle :=
  ⟨M, g.toMetricSpace, p⟩


theorem packing_card_le_of_ricci_lower_bound
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n)
    {δ R κ : ℝ} (hδ : 0 < δ) (hκ : 0 ≤ κ)
    (hcomplete : MetricComplete g) (D : LeviCivitaData g)
    (hRic : ∀ x, ∀ v : TangentSpace (𝓡 n) x,
      -(((n : ℝ) - 1) * κ) * g.inner x v v ≤ D.ricci x v v)
    {m : ℕ} (hm : m ∈ packingAdmissible (g.toBasedMetricSpace p).base δ R) :
    m ≤ ⌈modelVolume n κ (3 * max R 1) /
      modelVolume n κ (min (δ / 2) (max R 1) / 2)⌉₊ := by
  classical
  let : MetricSpace M := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hcomplete
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let : SecondCountableTopology M := g.secondCountableTopology
  let R' := max R 1
  let δ' := min (δ / 2) R'
  have hR' : 0 < R' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hδ' : 0 < δ' := lt_min (by positivity) hR'
  have hcompact : IsCompact (closure (g.ball p (5 * R'))) := by
    rw [← g.toMetricSpace_ball]
    exact (isCompact_closedBall p (5 * R')).of_isClosed_subset
      isClosed_closure Metric.closure_ball_subset_closedBall
  obtain ⟨S, _, hcard, _, hcover⟩ :=
    g.exists_finset_cover_of_precompact_ball p hn hR' hδ' (min_le_right _ _)
      hκ hcompact D (fun x _ => hRic x)
  change Nonempty (PackingWitness p δ R m) at hm
  obtain ⟨w⟩ := hm
  have hnear (i : Fin m) : ∃ z : S, dist (w.center i) z < δ' := by
    have hi : w.center i ∈ g.ball p R' := by
      rw [← g.toMetricSpace_ball]
      exact Metric.ball_subset_ball (le_max_left _ _) (w.center_mem i)
    obtain ⟨z, hzS, hz⟩ := mem_iUnion₂.mp (hcover hi)
    refine ⟨⟨z, hzS⟩, ?_⟩
    rw [← g.toMetricSpace_ball] at hz
    exact hz
  choose f hf using hnear
  have hfinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hsep := w.center_separated hδ hne
    have hi := hf i
    have hj := hf j
    rw [← hij] at hj
    have ht := dist_triangle (w.center i) (f i) (w.center j)
    rw [dist_comm (f i : M) (w.center j)] at ht
    have hsmall : δ' ≤ δ / 2 := min_le_left _ _
    linarith
  have hmS : m ≤ S.card := by
    simpa using Fintype.card_le_of_injective f hfinj
  exact hmS.trans hcard

end PoincareConjecture.RiemannianMetric
