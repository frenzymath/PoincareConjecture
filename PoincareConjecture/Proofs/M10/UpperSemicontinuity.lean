import PoincareConjecture.Statements.Ch06.ReducedLength
import Mathlib.Topology.Semicontinuity.Defs









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p q : M} {τ : ℝ}


theorem reducedLength_upperSemicontinuousAt_of_barrier
    (B : ReducedLengthUpperBarrier F T p q τ) :
    UpperSemicontinuousAt (fun z : M × ℝ ↦ reducedLength F T p z.1 z.2) (q, τ) := by
  intro c hc
  have hBc : B.representative (q, τ) < c := B.touches.trans_lt hc
  have hnear := B.representative_spacetime_smooth.continuousAt
    (eventually_lt_nhds hBc)
  filter_upwards [B.neighborhood_open.mem_nhds B.center_mem, hnear] with z hz hzc
  exact (B.dominates z hz).trans_lt hzc


theorem reducedLength_upperSemicontinuousAt [ConnectedSpace M]
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hτ : 0 < τ) (hmax : τ < τmax) :
    UpperSemicontinuousAt (fun z : M × ℝ ↦ reducedLength F T p z.1 z.2) (q, τ) := by
  obtain ⟨B, _⟩ := hDifferential.upper_barrier_extension p q τ hτ hmax 1 zero_lt_one
  exact reducedLength_upperSemicontinuousAt_of_barrier B


theorem reducedLength_upperSemicontinuousOn [ConnectedSpace M]
    (hDifferential : ReducedLengthDifferentialTheory F T τmax) (p : M) :
    UpperSemicontinuousOn (fun z : M × ℝ ↦ reducedLength F T p z.1 z.2)
      (Set.univ ×ˢ Set.Ioo 0 τmax) := by
  intro z hz
  exact UpperSemicontinuousAt.upperSemicontinuousWithinAt _
    (reducedLength_upperSemicontinuousAt hDifferential hz.2.1 hz.2.2)

end PoincareConjecture.M10
