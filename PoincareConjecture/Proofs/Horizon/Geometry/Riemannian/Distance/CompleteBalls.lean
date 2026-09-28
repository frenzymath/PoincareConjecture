import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.ApproximateSplit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Basic
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.LengthProper











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M]



theorem isCompact_closedBall_of_metricComplete (g : RiemannianMetric n M)
    (hcomplete : MetricComplete g) (p : M) (r : ℝ) :
    IsCompact {q | g.edist p q ≤ ENNReal.ofReal r} := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : CompleteSpace M := hcomplete
  let C := Metric.eball p ⊤
  have hC : IsClosed C := Metric.isClosed_eball_top
  let : LocallyCompactSpace C := hC.locallyCompactSpace
  let : CompleteSpace C := hC.isComplete.completeSpace_coe
  have hfinite (a b : C) : EDist.edist a b ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (edist_triangle a.val p b.val)
    refine ENNReal.add_ne_top.mpr ⟨a.property.ne, ?_⟩
    rw [edist_comm]
    exact b.property.ne
  let : MetricSpace C := EMetricSpace.toMetricSpace hfinite
  let : ProperSpace C := Poincare.properSpace_of_approximate_split (fun a b s ε hs hε hsb => by
    obtain ⟨z, hz, hzy, hrest⟩ :=
      g.exists_approximate_distance_split a.val b.val (hfinite a b) hs hε hsb
    have hzC : z ∈ C := by
      apply lt_of_le_of_lt (edist_triangle z a.val p)
      apply ENNReal.add_lt_top.mpr
      refine ⟨?_, a.property⟩
      change g.edist z a.val < ⊤
      rw [show g.edist z a.val = g.edist a.val z from edist_comm z a.val, hz]
      exact ENNReal.ofReal_lt_top
    refine ⟨⟨z, hzC⟩, ?_, hrest⟩
    change (g.edist a.val z).toReal ≤ s
    rw [hz, ENNReal.toReal_ofReal hs.le])
  let pC : C := ⟨p, Metric.mem_eball_self (by simp)⟩
  have himage : (Subtype.val : C → M) '' Metric.closedBall pC (max r 0) =
      {q | g.edist p q ≤ ENNReal.ofReal r} := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : (g.edist p z.val).toReal ≤ max r 0 := by
        change dist pC z ≤ max r 0
        rw [dist_comm]
        exact hz
      have hfin : g.edist p z.val ≠ ⊤ := by
        change EDist.edist p z.val ≠ ⊤
        rw [edist_comm]
        exact z.property.ne
      calc
        g.edist p z.val = ENNReal.ofReal (g.edist p z.val).toReal :=
          (ENNReal.ofReal_toReal hfin).symm
        _ ≤ ENNReal.ofReal (max r 0) := ENNReal.ofReal_le_ofReal hz'
        _ = ENNReal.ofReal r := by simp
    · intro hq
      have hqC : q ∈ C := by
        change EDist.edist q p < ⊤
        rw [edist_comm]
        exact lt_of_le_of_lt hq ENNReal.ofReal_lt_top
      refine ⟨⟨q, hqC⟩, ?_, rfl⟩
      change (g.edist q p).toReal ≤ max r 0
      rw [show g.edist q p = g.edist p q from edist_comm q p]
      simpa only [ENNReal.toReal_ofReal'] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hq
  rw [← himage]
  exact (isCompact_closedBall pC (max r 0)).image continuous_subtype_val

end PoincareConjecture.RiemannianMetric
