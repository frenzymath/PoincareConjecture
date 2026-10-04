import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Clopen

/-!
# Finite extended distance on a preconnected space

The smoothing stage in Claim 18.22, Morgan-Tian p. 433, uses the real
distance of each selected component's actual Riemannian metric. Finite
distance follows from preconnectedness: every finite-distance class is
a nonempty clopen extended ball. The existing Mathlib metric conversion
can therefore be used without changing the edist or manifold topology.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.SurgeryComparison.Transport

/-- Every pair in a preconnected pseudo-emetric space has finite distance.
This supplies the compatible real metric in the quantitative smoothing
step of Claim 18.22, Morgan-Tian p. 433. -/
theorem edist_ne_top_of_preconnected {X : Type*} [PseudoEMetricSpace X]
    [PreconnectedSpace X] (x y : X) : edist x y ≠ ⊤ := by
  have hc : IsClopen (Metric.eball y ⊤) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hu : Metric.eball y ⊤ = Set.univ :=
    hc.eq_univ ⟨y, Metric.mem_eball_self (by simp)⟩
  have hx : x ∈ Metric.eball y ⊤ := by rw [hu]; exact mem_univ x
  exact ne_of_lt hx

end PoincareMT.SurgeryComparison.Transport
