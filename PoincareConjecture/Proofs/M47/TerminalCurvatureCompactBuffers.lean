import PoincareConjecture.Proofs.M47.TerminalCurvatureOriginalCharts
import Mathlib.Topology.Separation.Regular









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_exists_finite_original_chart_buffers
    {ι : Type u} {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T3Space X]
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    {V : Set X} (hV : IsCompact V) (hVne : V.Nonempty)
    (hcover : ∀ x ∈ V, ∃ i, x ∈ (c i).source) :
    ∃ s : Finset V, s.Nonempty ∧
      ∃ index : s → ι, ∃ K : s → Set E,
        (∀ j, IsCompact (K j)) ∧ (∀ j, K j ⊆ (c (index j)).target) ∧
        ∀ x ∈ V, ∃ j, x ∈ (c (index j)).source ∧ c (index j) x ∈ K j := by
  classical
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
  choose index hindex using fun x : V => hcover x x.property
  have hlocal (x : V) : ∃ W : Set X, IsOpen W ∧ x.val ∈ W ∧
      closure W ⊆ (c (index x)).source ∧ IsCompact (closure W) := by
    obtain ⟨W, hW, hxW, hWsource, hWcompact⟩ :=
      exists_open_between_and_isCompact_closure isCompact_singleton
        (c (index x)).open_source (singleton_subset_iff.mpr (hindex x))
    exact ⟨W, hW, hxW (mem_singleton x.val), hWsource, hWcompact⟩
  choose W hW hxW hWsource hWcompact using hlocal
  obtain ⟨s, hs⟩ := hV.elim_finite_subcover W hW (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hVne
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hjs, _⟩ := mem_iUnion.mp hj
    exact ⟨j, hjs⟩
  refine ⟨s, hsne, fun j => index j.val,
    fun j => c (index j.val) '' closure (W j.val), ?_, ?_, ?_⟩
  · intro j
    exact (hWcompact j.val).image_of_continuousOn
      ((c (index j.val)).contMDiffOn_toFun.continuousOn.mono (hWsource j.val))
  · intro j
    rintro _ ⟨x, hx, rfl⟩
    exact (c (index j.val)).map_source (hWsource j.val hx)
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hjs, hxWj⟩ := mem_iUnion.mp hj
    exact ⟨⟨j, hjs⟩, hWsource j (subset_closure hxWj), ⟨x, subset_closure hxWj, rfl⟩⟩

end PoincareConjecture.M47
