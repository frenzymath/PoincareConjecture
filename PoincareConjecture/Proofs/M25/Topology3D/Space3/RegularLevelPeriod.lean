import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarLevelCurveChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularCurveFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactFlowPeriod

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_regular_collar_component_period
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪u, ψ (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪u, ψ (p, 0)⟫_ℝ) q ≠ 0)
    (x : collarHeightLevel ψ u t) :
    ∃ (T : ℝ), 0 < T ∧ ∃ e : AddCircle T ≃ₜ connectedComponent x,
      ContDiff ℝ ∞ (fun s : ℝ => ((e (s : AddCircle T)).1 : E3)) ∧
      ∀ s, deriv (fun r : ℝ => ((e (r : AddCircle T)).1 : E3)) s ≠ 0 := by
  let : CompactSpace (collarHeightLevel ψ u t) :=
    isCompact_iff_compactSpace.mp (collarHeightLevel_compact ψ hψ u t)
  let : CompactSpace (connectedComponent x) :=
    isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  let : PreconnectedSpace (connectedComponent x) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent
  obtain ⟨φ, hφ, hv⟩ := exists_regular_collar_level_flow ψ hψ u t hreg
  have hchart (y : collarHeightLevel ψ u t) (a : ℝ) :
      ∃ k : OpenPartialHomeomorph ℝ (collarHeightLevel ψ u t), a ∈ k.source ∧
        ∀ s ∈ k.source, k s = φ s y :=
    exists_collar_level_curve_time_chart ψ hψ u t hreg (fun s => φ s y)
      (φ.continuous continuous_id continuous_const) (hφ y) a (hv y a)
  have hopen (y : collarHeightLevel ψ u t) : IsOpenMap (fun s : ℝ => φ s y) :=
    curve_isOpenMap_of_time_charts _ (hchart y)
  let Φ := φ.restrict (realFlow_component_invariant φ x)
  let x₀ : connectedComponent x := ⟨x, mem_connectedComponent⟩
  have hopenC (y : connectedComponent x) : IsOpenMap (fun s : ℝ => Φ s y) :=
    (hopen y.1).codRestrict (fun s => realFlow_component_invariant φ x s y.2)
  obtain ⟨k, hk0, hk⟩ := hchart x 0
  obtain ⟨ε, hε, hinj⟩ := curve_injOn_interval_of_time_chart (fun s => φ s x) k hk0 hk
  have hinjC : InjOn (fun s : ℝ => Φ s x₀) (Ioo (-ε) ε) := by
    intro a ha b hb hab
    exact hinj ha hb (congrArg Subtype.val hab)
  obtain ⟨T, hT, e, he⟩ := exists_flow_circle_homeomorph Φ hopenC x₀ ε hε hinjC
  have heq : (fun s : ℝ => ((e (s : AddCircle T)).1 : E3)) =
      fun s : ℝ => (φ s x : E3) := by
    funext s
    rw [he s]
    rfl
  refine ⟨T, hT, e, ?_, ?_⟩
  · rw [heq]
    exact hφ x
  · rw [heq]
    exact hv x

end PoincareConjecture.M25.Topology3D
