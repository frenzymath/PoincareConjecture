import PoincareLib.Topology.Manifold.NeckCap.Cap.Bounds
import PoincareLib.Geometry.Riemannian.Distance.CompleteBalls

/-!
# Compact closure of a cap in a complete slice

The cap diameter bound puts its closure in a finite closed metric ball.
This permits the compact-region convergence estimates in the stability step
of Morgan--Tian, Claim 9.90, p. 241, to be used on the whole cap.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

/-- A quantitative cap in a complete slice has compact ambient closure. -/
theorem isCompact_closure_carrier (A : CapCertificate g) (hcomplete : MetricComplete g) :
    IsCompact (closure A.carrier) := by
  obtain ⟨x, hx⟩ := A.core_nonempty
  apply (g.isCompact_closedBall_of_metricComplete hcomplete x
    (A.cap_constant * A.connection.scalarCurvature x ^ (-1 / 2 : ℝ))).of_isClosed_subset
    isClosed_closure
  exact fun _ hy => A.edist_le_of_mem_closure le_rfl (A.core_subset_carrier hx) hy

end PoincareMT.CapCertificate
