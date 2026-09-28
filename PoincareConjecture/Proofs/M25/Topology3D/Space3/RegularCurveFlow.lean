import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow
import Mathlib.Dynamics.Flow
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false

open Set
open scoped ContDiff Manifold InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]

noncomputable def boundedFieldFlow (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) : Flow ℝ E where
  toFun t x := boundedFlow f hK hL x t
  cont' := (boundedFlow_contDiff f hK hL hf hs).continuous.comp continuous_swap
  map_add' s t x := by
    change boundedFlow f hK hL x (s + t) =
      boundedFlow f hK hL (boundedFlow f hK hL x t) s
    rw [add_comm s t, boundedFlow_add]
  map_zero' := boundedFlow_zero f hK hL

variable {X : Type*} [TopologicalSpace X]

theorem realFlow_component_invariant (φ : Flow ℝ X) (x : X) :
    IsInvariant φ (connectedComponent x) := by
  intro t y hy
  have hconn : IsPreconnected (range (fun s : ℝ => φ s y)) :=
    isPreconnected_range (φ.continuous continuous_id continuous_const)
  have hstart : y ∈ range (fun s : ℝ => φ s y) := ⟨0, φ.map_zero_apply y⟩
  rw [connectedComponent_eq hy]
  exact hconn.subset_connectedComponent hstart ⟨t, rfl⟩

theorem exists_regular_collar_level_flow
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪u, ψ (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪u, ψ (p, 0)⟫_ℝ) q ≠ 0) :
    ∃ φ : Flow ℝ (collarHeightLevel ψ u t),
      (∀ x, ContDiff ℝ ∞ (fun s : ℝ => (φ s x : E3))) ∧
      ∀ x s, deriv (fun r : ℝ => (φ r x : E3)) s ≠ 0 := by
  obtain ⟨g, hg, hgc, hnonzero, hinv⟩ := exists_regular_collar_level_field ψ hψ u t hreg
  obtain ⟨K, L, hK, hL⟩ := compactField_bounds g hg hgc
  let Φ := boundedFieldFlow g hK hL hg hgc
  have hS : IsInvariant Φ (collarHeightLevel ψ u t) := fun s y hy => hinv K L hK hL y hy s
  refine ⟨Φ.restrict hS, ?_, ?_⟩
  · intro x
    exact (boundedFlow_contDiff g hK hL hg hgc).comp (contDiff_const.prodMk contDiff_id)
  · intro x s
    change deriv (boundedFlow g hK hL x.1) s ≠ 0
    rw [(boundedFlow_hasDerivAt g hK hL x.1 s).deriv]
    exact hnonzero _ (hinv K L hK hL x.1 x.2 s)

theorem exists_regular_collar_component_flow
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪u, ψ (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪u, ψ (p, 0)⟫_ℝ) q ≠ 0)
    (x : collarHeightLevel ψ u t) :
    ∃ φ : Flow ℝ (connectedComponent x),
      (∀ y, ContDiff ℝ ∞ (fun s : ℝ => ((φ s y).1 : E3))) ∧
      ∀ y s, deriv (fun r : ℝ => ((φ r y).1 : E3)) s ≠ 0 := by
  obtain ⟨φ, hφ, hv⟩ := exists_regular_collar_level_flow ψ hψ u t hreg
  exact ⟨φ.restrict (realFlow_component_invariant φ x), fun y => hφ y.1,
    fun y s => hv y.1 s⟩

end PoincareConjecture.M25.Topology3D
