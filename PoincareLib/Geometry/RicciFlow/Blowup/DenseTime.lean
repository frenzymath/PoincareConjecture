import PoincareLib.Geometry.RicciFlow.Generalized.DenseTime
import PoincareLib.Geometry.RicciFlow.Blowup.BoundedDistance
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.BoundsTheory
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Pinching.Basic

/-!
# Dense-time bounded-distance control on generalized blowup sequences

Adapted from Mapher commit `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`,
Definitions/Statements M29GeneralizedDistance and Proofs/M29. The current
source interfaces use `PoincareMT.DenseTime` to preserve the accepted earlier
theorem. Morgan--Tian, opening of the proof of Theorem 11.1, p. 269, applying
Theorem 10.2, pp. 245--246. See
`references/ricci-flow/mapher/dense-time-bounded-distance.md`.
-/

set_option autoImplicit false

open Filter

universe u

namespace PoincareMT

namespace DenseTime

abbrev GeneralizedBoundedDistanceHypotheses
    (S : GeneralizedBlowupSequence.{u}) (epsilon C : ℝ) : Prop :=
  DenseGeneralizedBoundedDistanceHypotheses S epsilon C

abbrev GeneralizedBoundedDistanceTheory : Prop :=
  DenseGeneralizedBoundedDistanceTheory.{u}

end DenseTime

theorem GeneralizedBoundedDistanceHypotheses.toDenseTime
    {S : GeneralizedBlowupSequence.{u}} {epsilon C : ℝ}
    (H : GeneralizedBoundedDistanceHypotheses S epsilon C) :
    DenseTime.GeneralizedBoundedDistanceHypotheses S epsilon C :=
  ⟨H.branch, fun k ↦ (H.canonical k).left_dense⟩

namespace DenseTime

/-- The source M29 implication with left-dense whole-slice canonical control. -/
theorem generalizedBoundedDistance
    (P : BoundedDistanceTheory.{u}) :
    GeneralizedBoundedDistanceTheory.{u} := by
  rcases P.dense_constants with ⟨epsilon0, hepsilon0, hsmall, estimate⟩
  refine ⟨epsilon0, hepsilon0, hsmall, ?_⟩
  intro epsilon hepsilon hle C hC S H A hA
  obtain ⟨D0, D, _hD0, hD, bound⟩ := estimate epsilon hepsilon hle C hC A hA.le
  refine ⟨D, hD, ?_⟩
  filter_upwards [S.scalar_diverges.eventually_ge_atTop D0] with k hk
  have hbranch : generalizedWeakHamiltonIveyPinched (S.flow k) := by
    rcases H.branch k with hpinched | hnonnegative
    · exact hpinched.2.weak
    · exact hnonnegative.2
  have htime : (S.base k).1 ∈ (S.flow k).interval :=
    ((S.flow k).slice_nonempty_iff _).mp ⟨(S.base k).2⟩
  have hscale : 0 ≤ S.scale k := (S.base_scalar_pos k).le
  have hradius : A / Real.sqrt (S.scale k) = A * S.scale k ^ (-1 / 2 : ℝ) := by
    rw [neg_div, Real.rpow_neg hscale, ← Real.sqrt_eq_rpow,
      div_eq_mul_inv]
  intro x hx
  apply bound (S.flow k) hbranch (S.base k).1 htime
    (S.base k).2 hk (H.canonical k) x
  change x ∈ ((S.flow k).metric (S.base k).1).ball (S.base k).2
    (A * S.scale k ^ (-1 / 2 : ℝ))
  rw [← hradius]
  exact hx

/-- The dense-time conclusion also supplies the accepted earlier-time conclusion. -/
theorem GeneralizedBoundedDistanceTheory.toEarlierTime
    (P : GeneralizedBoundedDistanceTheory.{u}) :
    PoincareMT.RepairedGeneralizedBoundedDistanceTheory.{u} := by
  obtain ⟨epsilon₀, hpos, hsmall, bound⟩ := P.constants
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon hepsilon hle C hC S H
  exact bound epsilon hepsilon hle C hC S H.toDenseTime

end DenseTime

end PoincareMT
