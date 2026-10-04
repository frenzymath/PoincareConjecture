import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Finite compact chart regions inside a prescribed open set

Local compactness and the actual extended charts give a finite cover by
interiors of compact chart regions. This supplies the fixed atlas for
Morgan--Tian Proposition 9.79, pp. 232-234, and Proposition 10.7, p. 253;
M28 derivation 101. No completeness or connectedness is used.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold Topology

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [LocallyCompactSpace M]

/-- A compact set has finitely many compact actual chart regions whose
interiors cover it and which lie in any prescribed open neighborhood.
The coordinate images are compact and remain in the actual chart targets.
Source: the fixed-atlas step of Proposition 9.79; M28 derivation 101. -/
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
