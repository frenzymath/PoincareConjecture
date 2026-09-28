import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Asymptotic.ScalarDiameter












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]




theorem compact_nonround_exists_earlier_large_scalarDiameter
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : AncientKappaSolution 3 M) (hcompact : IsCompact (univ : Set M))
    (hnonround : ¬ IsRoundAncientKappaSolution K) (C b : ℝ) :
    ∃ t : ℝ, t < min b 0 ∧ ∃ p : M,
      C < metricDiameter (K.flow.metric t) univ *
        Real.sqrt ((K.flow.connection t).scalarCurvature p) := by
  obtain ⟨reference, _⟩ := K.nonflat 0 le_rfl
  let tau : ℕ → ℝ := fun k => (k : ℝ) + 1
  have htau : ∀ k, 0 < tau k := fun k => by dsimp [tau]; positivity
  have htauLimit : Tendsto tau atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  obtain ⟨B⟩ := P.blowup_setup K reference tau htau htauLimit
  obtain ⟨L, _⟩ := P.classified_limit K B.sequence
  have hdiam := compact_nonround_eventually_large_past_scalarDiameter
    P hcompact hnonround B.sequence L C
  have hscale := B.sequence.scale_tendsto.comp
    L.convergence.subsequence_strictMono.tendsto_atTop
  obtain ⟨k, ⟨p, hp⟩, hk⟩ :=
    (hdiam.and (hscale.eventually (eventually_gt_atTop (-min b 0)))).exists
  refine ⟨-B.sequence.scale (L.convergence.subsequence k), ?_, p, hp⟩
  simpa only [Function.comp_apply, neg_neg] using neg_lt_neg hk



theorem compact_nonround_exists_large_past_scalarDiameter
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : AncientKappaSolution 3 M) (hcompact : IsCompact (univ : Set M))
    (hnonround : ¬ IsRoundAncientKappaSolution K) (C : ℝ) :
    ∃ t : ℝ, t ≤ 0 ∧ ∃ p : M,
      C < metricDiameter (K.flow.metric t) univ *
        Real.sqrt ((K.flow.connection t).scalarCurvature p) := by
  obtain ⟨t, ht, p, hp⟩ :=
    compact_nonround_exists_earlier_large_scalarDiameter P K hcompact hnonround C 0
  exact ⟨t, ht.le.trans (min_le_right _ _), p, hp⟩

end PoincareConjecture
