import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.ApproximateSplit









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M]



theorem closure_ball_eq_edist_le (g : RiemannianMetric n M) (p : M)
    {r : ℝ} (hr : 0 < r) :
    closure (g.ball p r) = {q | g.edist p q ≤ ENNReal.ofReal r} := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  apply Subset.antisymm
  · apply closure_minimal ?_
      (isClosed_le (continuous_const.edist continuous_id) continuous_const)
    intro q hq
    change g.edist p q < ENNReal.ofReal r at hq
    exact hq.le
  · intro q hq
    change g.edist p q ≤ ENNReal.ofReal r at hq
    rcases lt_or_eq_of_le hq with hlt | heq
    · exact subset_closure hlt
    · apply EMetric.mem_closure_iff.mpr
      intro ε hε
      obtain ⟨δ, _, hδ, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
      have hδpos : 0 < δ := ENNReal.ofReal_pos.mp hδ
      obtain ⟨a, ha, har⟩ := exists_between
        (max_lt (half_lt_self hr) (sub_lt_self r (half_pos hδpos)))
      have ha0 : 0 < a := (half_pos hr).trans ((le_max_left _ _).trans_lt ha)
      have hnear : r - a + δ / 2 < δ := by
        have := (le_max_right (r / 2) (r - δ / 2)).trans_lt ha
        linarith
      have hfinite : g.edist p q ≠ ⊤ := by rw [heq]; exact ENNReal.ofReal_ne_top
      obtain ⟨z, hz, hzfinite, hzq⟩ := g.exists_approximate_distance_split p q hfinite
        ha0 (half_pos hδpos) (by rw [heq, ENNReal.toReal_ofReal hr.le]; exact har)
      have hzball : z ∈ g.ball p r := by
        change g.edist p z < ENNReal.ofReal r
        rw [hz]
        exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr har
      have hzδ : g.edist z q < ENNReal.ofReal δ := by
        rw [heq, ENNReal.toReal_ofReal hr.le] at hzq
        rw [← ENNReal.ofReal_toReal hzfinite]
        exact (ENNReal.ofReal_lt_ofReal_iff hδpos).mpr (hzq.trans hnear)
      refine ⟨z, hzball, ?_⟩
      change g.edist q z < ε
      have hcomm : g.edist q z = g.edist z q := Manifold.riemannianEDist_comm
      exact hcomm ▸ hzδ.trans hδε

end PoincareConjecture.RiemannianMetric
