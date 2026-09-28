import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M]



theorem exists_approximate_distance_split (g : RiemannianMetric n M)
    (x y : M) (hxy : g.edist x y ≠ ⊤) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hry : r < (g.edist x y).toReal) :
    ∃ z : M, g.edist x z = ENNReal.ofReal r ∧ g.edist z y ≠ ⊤ ∧
      (g.edist z y).toReal < (g.edist x y).toReal - r + ε := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hshort : g.edist x y < ENNReal.ofReal ((g.edist x y).toReal + ε) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hxy]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg |>.mpr
      (lt_add_of_pos_right _ hε)
  obtain ⟨γ, h0, h1, hγ, hlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hshort
  have hcont : ContinuousOn (fun t => g.edist x (γ t)) (Icc (0 : ℝ) 1) :=
    (continuous_const.edist continuous_id).comp_continuousOn hγ.continuousOn
  have hrange : ENNReal.ofReal r ∈
      Icc (g.edist x (γ 0)) (g.edist x (γ 1)) := by
    rw [h0, h1]
    refine ⟨by simp only [edist, Manifold.riemannianEDist_self]; positivity, ?_⟩
    conv_rhs => rw [← ENNReal.ofReal_toReal hxy]
    exact ENNReal.ofReal_le_ofReal hry.le
  obtain ⟨t, ht, hdist⟩ := intermediate_value_Icc zero_le_one hcont hrange
  have hleft : g.edist x (γ t) ≤ Manifold.pathELength (𝓡 n) γ 0 t :=
    Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc_right ht.2)) h0 rfl ht.1
  have hright : g.edist (γ t) y ≤ Manifold.pathELength (𝓡 n) γ t 1 :=
    Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc_left ht.1)) rfl h1 ht.2
  have hsum : ENNReal.ofReal r + g.edist (γ t) y <
      ENNReal.ofReal ((g.edist x y).toReal + ε) := by
    rw [← hdist]
    exact (add_le_add hleft hright).trans_lt
      ((Manifold.pathELength_add ht.1 ht.2).trans_lt hlen)
  have hfinite : g.edist (γ t) y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((le_add_self).trans hsum.le)
  refine ⟨γ t, hdist, hfinite, ?_⟩
  have hreal := (ENNReal.toReal_lt_toReal
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hfinite⟩)
    ENNReal.ofReal_ne_top).mpr hsum
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hfinite,
    ENNReal.toReal_ofReal hr.le,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  linarith

end PoincareConjecture.RiemannianMetric
