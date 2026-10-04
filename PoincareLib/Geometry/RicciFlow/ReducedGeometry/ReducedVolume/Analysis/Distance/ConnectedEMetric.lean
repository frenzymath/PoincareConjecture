import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Clopen

/-!
# Finite distances in a connected extended metric space

An infinite-radius open ball is also closed. Connectedness makes it
the whole space, so conversion to a metric preserves the original
uniformity and its completeness.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.ReducedVolume

/-- Every distance in a preconnected extended metric space is finite. -/
theorem edist_ne_top_of_preconnected {X : Type*} [EMetricSpace X] [PreconnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  have hball : eball x ⊤ = (univ : Set X) :=
    IsClopen.eq_univ ⟨isClosed_eball_top, isOpen_eball⟩ ⟨x, by simp⟩
  have hy : y ∈ eball x ⊤ := by rw [hball]; trivial
  exact (by simpa only [mem_eball, edist_comm] using hy : edist x y < ⊤).ne

end PoincareMT.ReducedVolume
