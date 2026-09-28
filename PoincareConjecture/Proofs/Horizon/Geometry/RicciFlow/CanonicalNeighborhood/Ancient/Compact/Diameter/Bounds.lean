import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.UniformScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

section Diameter

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [ConnectedSpace M]


theorem compact_metricDiameter_bddAbove (g : RiemannianMetric 3 M)
    (hcompact : IsCompact (Set.univ : Set M)) :
    BddAbove (Set.range (fun p : (↥(Set.univ : Set M) × ↥(Set.univ : Set M)) ↦
      (g.edist p.1 p.2).toReal)) := by
  obtain ⟨p⟩ := (inferInstance : Nonempty M)
  obtain ⟨q, _, hq⟩ := hcompact.exists_isMaxOn Set.univ_nonempty
    (g.continuous_toReal_edist p).continuousOn
  refine ⟨2 * (g.edist p q).toReal, ?_⟩
  rintro _ ⟨⟨x, y⟩, rfl⟩
  have hx := hq (Set.mem_univ (x : M))
  have hy := hq (Set.mem_univ (y : M))
  have htriangle := g.toReal_edist_triangle (x : M) p (y : M)
  have hcomm : g.edist (x : M) p = g.edist p x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact Manifold.riemannianEDist_comm
  rw [hcomm] at htriangle
  dsimp at hx hy ⊢
  linarith


theorem compact_toReal_edist_le_metricDiameter (g : RiemannianMetric 3 M)
    (hcompact : IsCompact (Set.univ : Set M)) (p q : M) :
    (g.edist p q).toReal ≤ metricDiameter g Set.univ :=
  le_csSup (compact_metricDiameter_bddAbove g hcompact)
    ⟨(⟨p, Set.mem_univ p⟩, ⟨q, Set.mem_univ q⟩), rfl⟩


theorem compact_mem_ball_of_metricDiameter_lt (g : RiemannianMetric 3 M)
    (hcompact : IsCompact (Set.univ : Set M)) {r : ℝ}
    (hdiam : metricDiameter g Set.univ < r) (p q : M) : q ∈ g.ball p r :=
  (ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top p q)).mpr
    ((compact_toReal_edist_le_metricDiameter g hcompact p q).trans_lt hdiam)

end Diameter



theorem compact_uniform_scalar_bound_of_normalized_diameter
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {kappa D : ℝ} (hkappa : 0 < kappa) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        AncientKappaNoncollapsed K.flow kappa →
        (K.flow.connection 0).scalarCurvature p = 1 →
        IsCompact (Set.univ : Set M) →
        metricDiameter (K.flow.metric 0) Set.univ ≤ D →
        ∀ x : M, (K.flow.connection 0).scalarCurvature x ≤ C := by
  obtain ⟨C, hC, hbound⟩ := compact_uniform_scalar_bound_of_normalized P hkappa
    (show 0 < D + 1 by linarith)
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnoncollapsed hnormalized hcompact hdiam x
  exact hbound K p hnoncollapsed hnormalized x
    (compact_mem_ball_of_metricDiameter_lt (K.flow.metric 0) hcompact
      (hdiam.trans_lt (by linarith)) p x)

end PoincareConjecture
