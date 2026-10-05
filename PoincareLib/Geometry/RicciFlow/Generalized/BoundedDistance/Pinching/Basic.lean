import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Dense
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Geometry.LogPinching

/-!
# Pinching toward positive curvature

Morgan--Tian Definition 10.1, printed p. 245, implies the weak pinching
inequalities (10.1), printed p. 247. Their quantitative consequence is the
normalized negative-curvature bound used in Claim 10.11, printed p. 255.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

open Filter
open scoped Topology

/-- A uniform scalar bound on a rescaled region forces its negative
curvature part below `eta` times the rescaling factor. This is the
quantitative input to Morgan--Tian Claim 10.11, printed p. 255. -/
theorem generalizedWeakHamiltonIveyPinched.negative_part_lt
    {F : GeneralizedRicciFlowData.{u}}
    (h : generalizedWeakHamiltonIveyPinched F)
    {eta B Q t : ℝ} (heta : 0 < eta) (hB : 0 ≤ B)
    (hQ : Real.exp (3 + (B + 1) / (2 * eta)) / eta ≤ Q)
    (ht : t ∈ F.interval) (x : (F.slice t).carrier)
    (hscalar : F.scalar ⟨t, x⟩ ≤ B * Q) :
    (F.connection t).negativeCurvaturePart x < eta * Q := by
  exact Real.lt_mul_of_log_pinching heta hB hQ hscalar (h t ht x).2

/-- Along any points with uniformly bounded normalized scalar curvature,
the normalized negative part of a pinched blowup sequence tends to zero.
The points may vary in space and time, as required by Morgan--Tian
Claim 10.11, printed p. 255. -/
theorem GeneralizedBlowupSequence.negative_part_tendsto_zero
    (S : GeneralizedBlowupSequence.{u})
    (hpinch : ∀ k, generalizedWeakHamiltonIveyPinched (S.flow k))
    (p : ∀ k, (S.flow k).point) {B : ℝ} (hB : 0 ≤ B)
    (hscalar : ∀ᶠ k in atTop, (S.flow k).scalar (p k) ≤ B * S.scale k) :
    Tendsto (fun k ↦ ((S.flow k).connection (p k).1).negativeCurvaturePart (p k).2 /
      S.scale k) atTop (𝓝 0) := by
  apply Real.tendsto_zero_of_log_pinching hB S.scalar_diverges
  · exact Filter.Eventually.of_forall fun k ↦ le_max_right _ _
  · exact hscalar
  · apply Filter.Eventually.of_forall
    intro k
    have ht : (p k).1 ∈ (S.flow k).interval :=
      ((S.flow k).slice_nonempty_iff _).mp ⟨(p k).2⟩
    exact (hpinch k _ ht (p k).2).2

end PoincareMT
