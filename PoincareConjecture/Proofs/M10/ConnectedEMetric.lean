import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M10

theorem edist_ne_top_of_preconnected {X : Type*} [EMetricSpace X] [PreconnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  have hball : eball x ⊤ = (univ : Set X) :=
    IsClopen.eq_univ ⟨isClosed_eball_top, isOpen_eball⟩ ⟨x, by simp⟩
  have hy : y ∈ eball x ⊤ := by rw [hball]; trivial
  exact (by simpa only [mem_eball, edist_comm] using hy : edist x y < ⊤).ne

end PoincareConjecture.M10
