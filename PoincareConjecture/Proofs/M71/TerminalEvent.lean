import PoincareConjecture.Definitions.M52GlobalFlow
import PoincareConjecture.Definitions.Ch18.FiniteExtinction
import Mathlib.Data.Finset.Max













set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M]
  {N : NormalizedInitialMetric (M := M)}






theorem m71FirstEmptySurgery
    (G : GlobalSurgeryFlowCertificate N)
    (T : ℝ) (hT : T ∈ G.flow.time_domain)
    (hempty : IsEmpty (G.flow.slice T).carrier) :
    ∃ E : FiniteExtinctionConclusion G.flow,
      E.extinction_time ≤ T ∧
        ∀ s ∈ G.flow.time_domain, s < E.extinction_time →
          Nonempty (G.flow.slice s).carrier := by
  classical
  have hTnonnegative : 0 ≤ T := G.flow.time_domain_nonnegative hT
  let bounded := (G.local_finite (Set.Icc 0 T) isCompact_Icc).toFinset
  have mem_bounded : ∀ s : ℝ, s ∈ bounded ↔
      s ∈ G.flow.surgery_times ∧ 0 ≤ s ∧ s ≤ T := by
    intro s
    simp only [bounded, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_Icc]
  let anchors := insert 0 bounded
  have hzero : 0 ∈ anchors := Finset.mem_insert_self _ _
  let S := anchors.max' ⟨0, hzero⟩
  have hSanchor : S ∈ anchors := anchors.max'_mem _
  have hSnonnegative : 0 ≤ S := anchors.le_max' 0 hzero
  have hST : S ≤ T := by
    rcases Finset.mem_insert.mp hSanchor with hSzero | hS
    · simpa only [hSzero] using hTnonnegative
    · exact ((mem_bounded S).mp hS).2.2
  have hSdomain : S ∈ G.flow.time_domain := by
    rw [G.time_domain_eq]
    exact hSnonnegative
  have hregular : Disjoint G.flow.surgery_times (Set.Ioc S T) := by
    apply Set.disjoint_left.mpr
    intro t ht hinterval
    have htanchor : t ∈ anchors := Finset.mem_insert_of_mem
      ((mem_bounded t).mpr ⟨ht,
        G.flow.time_domain_nonnegative (G.flow.surgery_times_subset ht), hinterval.2⟩)
    exact (not_lt_of_ge (anchors.le_max' t htanchor)) hinterval.1
  have hSempty : IsEmpty (G.flow.slice S).carrier := by
    rcases hST.eq_or_lt with hSTeq | hSTlt
    · simpa only [hSTeq] using hempty
    · have hdomain : Set.Icc S T ⊆ G.flow.time_domain := by
        intro t ht
        rw [G.time_domain_eq]
        exact hSnonnegative.trans ht.1
      let slab := G.flow.regular_slabs S T hSTlt hdomain hregular
      exact ⟨fun x => hempty.false (slab.identify ⟨T, ⟨hSTlt.le, le_rfl⟩⟩ x)⟩
  have hSne : S ≠ 0 := by
    intro hSzero
    have hzempty : IsEmpty (G.flow.slice 0).carrier := by
      simpa only [hSzero] using hSempty
    exact hzempty.false (Classical.choice G.flow.initial_nonempty)
  have hSsurgery : S ∈ G.flow.surgery_times := by
    rcases Finset.mem_insert.mp hSanchor with hSzero | hS
    · exact (hSne hSzero).elim
    · exact ((mem_bounded S).mp hS).1
  let E : FiniteExtinctionConclusion G.flow :=
    { extinction_time := S
      extinction_mem := hSdomain
      extinct := hSempty
      extinction_surgery_mem := hSsurgery
      permanent_empty := fun t ht hSt => G.permanent_empty S t hSdomain ht hSt hSempty }
  refine ⟨E, hST, ?_⟩
  intro s hs hsS
  by_contra hnonempty
  have hsempty : IsEmpty (G.flow.slice s).carrier := not_nonempty_iff.mp hnonempty
  exact G.no_surgery_after_empty s hs hsempty S hSdomain hsS hSsurgery

end PoincareConjecture
