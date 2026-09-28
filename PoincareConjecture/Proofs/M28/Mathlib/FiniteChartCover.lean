import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.Compactness.LocallyCompact










set_option autoImplicit false

open Set Filter
open scoped Manifold Topology

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [LocallyCompactSpace M]





theorem IsCompact.exists_finite_extChart_cover {K W : Set M} (hK : IsCompact K)
    (I : ModelWithCorners 𝕜 E H) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ s : Finset M, ∃ C : M → Set M,
      (∀ q ∈ s, q ∈ K ∧ IsCompact (C q) ∧ q ∈ interior (C q) ∧
        C q ⊆ (extChartAt I q).source ∩ W ∧
        IsCompact ((extChartAt I q) '' C q) ∧
        (extChartAt I q) '' C q ⊆ (extChartAt I q).target) ∧
      K ⊆ ⋃ q ∈ s, interior (C q) := by
  classical
  have hchoose : ∀ q : M, ∃ C : Set M, IsCompact C ∧
      (q ∈ K → q ∈ interior C ∧ C ⊆ (extChartAt I q).source ∩ W) := by
    intro q
    by_cases hq : q ∈ K
    · obtain ⟨C, hC, hqC, hCW⟩ := exists_compact_subset
        ((isOpen_extChartAt_source (I := I) q).inter hW)
        ⟨mem_extChartAt_source q, hKW hq⟩
      exact ⟨C, hC, fun _ => ⟨hqC, hCW⟩⟩
    · exact ⟨∅, isCompact_empty, fun h => (hq h).elim⟩
  choose C hC hinside using hchoose
  obtain ⟨s, hsK, hcover⟩ := hK.elim_nhds_subcover (fun q => interior (C q))
    (fun q hq => isOpen_interior.mem_nhds (hinside q hq).1)
  refine ⟨s, C, ?_, hcover⟩
  intro q hq
  have hqK := hsK q hq
  have hsource : C q ⊆ (extChartAt I q).source :=
    fun x hx => ((hinside q hqK).2 hx).1
  refine ⟨hqK, hC q, (hinside q hqK).1, (hinside q hqK).2, ?_, ?_⟩
  · exact (hC q).image_of_continuousOn ((continuousOn_extChartAt q).mono hsource)
  · rintro _ ⟨x, hx, rfl⟩
    exact (extChartAt I q).map_source (hsource hx)
