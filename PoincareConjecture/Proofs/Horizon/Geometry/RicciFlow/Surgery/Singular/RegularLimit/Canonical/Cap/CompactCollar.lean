import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.BallClosure
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.Compactness.LocallyCompact









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M]



theorem exists_compact_ball_neighborhood (g : RiemannianMetric n M)
    {A : Set M} (hA : IsCompact A) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : Set M, IsCompact K ∧
      ∀ p ∈ A, g.ball p δ ⊆ K := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  obtain ⟨K, hK, hAK⟩ := exists_compact_superset hA
  obtain ⟨ε, hε, hεK⟩ :=
    (hA.nhdsSet_basis_uniformity uniformity_basis_edist).mem_iff.mp
      (isOpen_interior.mem_nhdsSet.mpr hAK)
  obtain ⟨δ, _, hδ, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  refine ⟨δ, ENNReal.ofReal_pos.mp hδ, K, hK, ?_⟩
  intro p hp q hq
  apply interior_subset (hεK ?_)
  exact mem_iUnion₂_of_mem hp (hq.trans hδε)



theorem ball_add_subset_of_ball_subset (g : RiemannianMetric n M)
    (p : M) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    {A B : Set M} (hball : g.ball p r ⊆ A)
    (hcollar : ∀ z ∈ A, g.ball z δ ⊆ B) :
    g.ball p (r + δ) ⊆ B := by
  intro q hq
  by_cases hqr : q ∈ g.ball p r
  · apply hcollar q (hball hqr)
    change g.edist q q < ENNReal.ofReal δ
    simpa only [edist, Manifold.riemannianEDist_self] using ENNReal.ofReal_pos.mpr hδ
  · have hfinite : g.edist p q ≠ ⊤ := ne_top_of_lt ((show
        g.edist p q < ENNReal.ofReal (r + δ) from hq).trans_le le_top)
    have hd : (g.edist p q).toReal < r + δ := ENNReal.toReal_lt_of_lt_ofReal hq
    have hrd : r ≤ (g.edist p q).toReal := by
      have hh : ENNReal.ofReal r ≤ g.edist p q := le_of_not_gt hqr
      exact (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hh
    obtain ⟨a, ha, har⟩ := exists_between
      (max_lt hr (show (g.edist p q).toReal - δ < r by linarith))
    have ha0 : 0 < a := (le_max_left _ _).trans_lt ha
    have hgap : 0 < δ - ((g.edist p q).toReal - a) := by
      have := (le_max_right (0 : ℝ) ((g.edist p q).toReal - δ)).trans_lt ha
      linarith
    obtain ⟨z, hzp, hzfinite, hzq⟩ := g.exists_approximate_distance_split p q hfinite
      ha0 (half_pos hgap) (har.trans_le hrd)
    have hz : z ∈ g.ball p r := by
      change g.edist p z < ENNReal.ofReal r
      rw [hzp]
      exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr har
    apply hcollar z (hball hz)
    change g.edist z q < ENNReal.ofReal δ
    rw [← ENNReal.ofReal_toReal hzfinite]
    apply (ENNReal.ofReal_lt_ofReal_iff hδ).mpr
    linarith



theorem exists_uniform_precompact_ball_enlargement (g : RiemannianMetric n M)
    {A : Set M} (hA : IsCompact A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : M, ∀ r : ℝ, 0 < r → g.ball p r ⊆ A →
      IsCompact (closure (g.ball p (r + δ))) := by
  obtain ⟨δ, hδ, K, hK, hcollar⟩ := g.exists_compact_ball_neighborhood hA
  refine ⟨δ, hδ, ?_⟩
  intro p r hr hball
  exact hK.of_isClosed_subset isClosed_closure
    (closure_minimal (g.ball_add_subset_of_ball_subset p hr hδ hball hcollar) hK.isClosed)

end PoincareConjecture.RiemannianMetric
