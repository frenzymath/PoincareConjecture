import PoincareConjecture.Proofs.M14.Sec6_5_GradientIdentity
import Mathlib.Analysis.Calculus.Deriv.Mul










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}




theorem exponential_reducedLength_hasDerivWithinAt
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) :
    HasDerivWithinAt (E.reduced_length Z)
      (-M14GeneralizedKIntegral G (E.path Z s hs hpos)
        (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          ((E.path Z s hs hpos).curve t)) / s ^ 2) {r | (Z, r) ∈ E.domain} s := by
  let D := {r | (Z, r) ∈ E.domain}
  have hden : HasDerivWithinAt (fun r : ℝ => 2 * r) 2 D s := by
    simpa only [id_eq, mul_one] using (hasDerivWithinAt_id s D).const_mul 2
  have hquot := (E.action_time_derivative Z s hs hpos).div hden
    (mul_pos zero_lt_two hpos).ne'
  have heq : E.reduced_length Z =ᶠ[𝓝[D] s] (fun r => E.action Z r / (2 * r)) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hpos)]
      with r hr hr0
    exact E.reduced_length_eq Z r hr hr0
  apply (hquot.congr_of_eventuallyEq_of_mem heq hs).congr_deriv
  rw [exponential_harnackIntegral_eq hM12 E hs hpos]
  field_simp [hpos.ne']
  ring

end PoincareConjecture.M14
