import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.EscapeCarrier









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem exists_scale_lower_bound_of_meets_compact (D : LeviCivitaData g)
    (epsilon : ℝ) {K : Set M} (hK : IsCompact K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : EpsilonNeck g, N.epsilon = epsilon →
      (N.carrier ∩ K).Nonempty → ρ ≤ N.scale := by
  classical
  by_contra h
  have hchoice (i : ℕ) : ∃ N : EpsilonNeck g, N.epsilon = epsilon ∧
      (N.carrier ∩ K).Nonempty ∧ N.scale < 1 / ((i : ℝ) + 1) := by
    by_contra hn
    push Not at hn
    exact h ⟨1 / ((i : ℝ) + 1), by positivity, hn⟩
  choose N hε hmeet hscale using hchoice
  have htendsto : Tendsto (fun i => (N i).scale) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
      (fun i => (N i).scale_pos.le) (fun i => (hscale i).le)
  obtain ⟨i, hi⟩ :=
    (eventually_disjoint_carrier_compact_of_scale_tendsto_zero D N hε htendsto hK).exists
  exact (hmeet i).ne_empty hi.inter_eq



theorem eventually_scale_lower_bound_of_tendsto (D : LeviCivitaData g)
    {ι : Type*} {l : Filter ι} (N : ι → EpsilonNeck g) {epsilon : ℝ}
    (hε : ∀ i, (N i).epsilon = epsilon) {p : ι → M} {x : M}
    (hp : Tendsto p l (𝓝 x)) (hmem : ∀ᶠ i in l, p i ∈ (N i).carrier) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ i in l, ρ ≤ (N i).scale := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  obtain ⟨ρ, hρ, hbound⟩ := exists_scale_lower_bound_of_meets_compact D epsilon hK
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hp.eventually hxK, hmem] with i hiK hiN
  exact hbound (N i) (hε i) ⟨p i, hiN, hiK⟩

end PoincareConjecture.EpsilonNeck
