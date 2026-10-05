import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Bounds
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.DenseTheory

/-!
Adapted from Mapher `PoincareMT/Statements/M29GeneralizedDistance.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M29 generalized bounded-distance statement

Natural-language corollary (the opening of Morgan--Tian's proof of Theorem
11.1, p. 269, applying Theorem 10.2, pp. 245--246). First choose
one universal small epsilon0, then 0 < epsilon <= epsilon0 and C > 0. For
every generalized blowup sequence in the nonnegative-time normalization whose
members satisfy the Hamilton--Ivey or nonnegative-curvature alternative and whose earlier
high-curvature points have explicit strong canonical-neighborhood certificates,
the scalar curvature on every fixed normalized final-time ball is eventually
bounded by a constant times the base scalar. The conclusion is the concrete
`GeneralizedBlowupBoundedDistance` predicate; compactness and limit extraction
belong to M30. Appendix A.19--A.21 and the errata govern the neck/cap
certificates used by the proof.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

structure DenseGeneralizedBoundedDistanceTheory : Prop where
  /-- The applied M28 threshold and estimates, with no remaining theory premise. -/
  constants : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ C : ℝ, 0 < C →
        ∀ (S : GeneralizedBlowupSequence.{u}),
          DenseGeneralizedBoundedDistanceHypotheses S epsilon C →
            GeneralizedBlowupBoundedDistance S

end PoincareMT
