import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.LoopNeighborhoods
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.SmallParametrizedCollars
import PoincareConjecture.Proofs.M60.Filling










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]




theorem m60_exists_parametrized_collar_neighborhood (g : RiemannianMetric 3 M)
    (hcompact : IsCompact (univ : Set M)) (γ₀ : C1FreeLoopSpace (M := M))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ U : Set (C1FreeLoopSpace (M := M)), IsOpen U ∧ γ₀ ∈ U ∧
      ∀ γ ∈ U,
        (∀ D : LipschitzSpanningDisk g γ₀, (∀ z : LoopCircle, D.map z = γ₀ z) →
          ∃ E : LipschitzSpanningDisk g γ,
            (∀ z : LoopCircle, E.map z = γ z) ∧ E.area < D.area + epsilon) ∧
        (∀ D : LipschitzSpanningDisk g γ, (∀ z : LoopCircle, D.map z = γ z) →
          ∃ E : LipschitzSpanningDisk g γ₀,
            (∀ z : LoopCircle, E.map z = γ₀ z) ∧ E.area < D.area + epsilon) := by
  obtain ⟨V, L, hV, hγ₀, hL, hlength⟩ := m60_exists_loop_length_neighborhood g γ₀
  obtain ⟨delta, hdelta, hcollar⟩ :=
    m60_exists_small_parametrized_collar g hcompact (add_nonneg hL hL) hepsilon
  obtain ⟨W, hW, hγ₀W, hclose⟩ := m60_exists_loop_close_neighborhood g γ₀ hdelta
  refine ⟨V ∩ W, hV.inter hW, ⟨hγ₀, hγ₀W⟩, ?_⟩
  intro γ hγ
  constructor
  · exact hcollar γ₀ γ (hclose γ hγ.2) (add_le_add (hlength γ hγ.1) (hlength γ₀ hγ₀))
  · apply hcollar γ γ₀ _ (add_le_add (hlength γ₀ hγ₀) (hlength γ hγ.1))
    intro z
    have hsymm : g.edist (γ₀ z) (γ z) = g.edist (γ z) (γ₀ z) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_comm
    rw [hsymm]
    exact hclose γ hγ.2 z




theorem m60FillingArea_continuousOn_of_parametrized_near_minimizers
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M))
    (hnear : ∀ γ : C1FreeLoopSpace (M := M), IsNullHomotopicLoop γ →
      ∀ epsilon : ℝ, 0 < epsilon → ∃ D : LipschitzSpanningDisk g γ,
        (∀ z : LoopCircle, D.map z = γ z) ∧ D.area < fillingArea g γ + epsilon) :
    ContinuousOn (fun γ : C1FreeLoopSpace (M := M) => fillingArea g γ)
      {γ | IsNullHomotopicLoop γ} := by
  intro γ₀ hγ₀
  apply Metric.continuousWithinAt_iff'.mpr
  intro epsilon hepsilon
  have hh : 0 < epsilon / 2 := half_pos hepsilon
  obtain ⟨U, hU, hγ₀U, hcollar⟩ := m60_exists_parametrized_collar_neighborhood
    g hcompact γ₀ hh
  obtain ⟨D₀, hD₀, hD₀area⟩ := hnear γ₀ hγ₀ (epsilon / 2) hh
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hγ₀U), self_mem_nhdsWithin]
    with γ hγU hγ
  obtain ⟨D, hD, hDarea⟩ := hnear γ hγ (epsilon / 2) hh
  obtain ⟨E, _, hE⟩ := (hcollar γ hγU).1 D₀ hD₀
  obtain ⟨E₀, _, hE₀⟩ := (hcollar γ hγU).2 D hD
  have hupper := m60FillingArea_le_disk g γ E
  have hlower := m60FillingArea_le_disk g γ₀ E₀
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end PoincareConjecture
