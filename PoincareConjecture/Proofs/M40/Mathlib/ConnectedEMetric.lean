import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set

namespace PoincareConjecture.M40

theorem edist_ne_top_of_preconnected {X : Type*} [PseudoEMetricSpace X]
    [PreconnectedSpace X] (x y : X) : edist x y ≠ ⊤ := by
  have hc : IsClopen (Metric.eball y ⊤) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hu : Metric.eball y ⊤ = Set.univ :=
    hc.eq_univ ⟨y, Metric.mem_eball_self (by simp)⟩
  have hx : x ∈ Metric.eball y ⊤ := by rw [hu]; exact mem_univ x
  exact ne_of_lt hx

end PoincareConjecture.M40
