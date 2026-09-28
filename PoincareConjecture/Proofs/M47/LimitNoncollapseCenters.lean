import PoincareConjecture.Proofs.M47.LimitNoncollapseWorldlines

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

theorem limitNoncollapse_pointMap_injective_at
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) {x y : C.carrier}
    (hx : x ∈ U) (hy : y ∈ U)
    (hxy : e.pointMap s hs x = e.pointMap s hs y) : x = y := by
  have hsp : e.forward s hs x = e.forward s hs y := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp hxy).2
  calc
    x = e.inverse s hs (e.forward s hs x) := (e.left_inverse s hs hx).symm
    _ = e.inverse s hs (e.forward s hs y) := by rw [hsp]
    _ = y := e.left_inverse s hs hy

theorem limitNoncollapse_convergence_center_identity
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (Cnv : GeneralizedBlowupConvergence S J) (k : ℕ)
    (h0 : 0 ∈ Icc (-Cnv.exhaustion.time k) 0) :
    (Cnv.embedding k).pointMap 0 h0 Cnv.limit.base = S.base (Cnv.subsequence k) :=
  Cnv.base_preserving k h0

end PoincareConjecture.M47
