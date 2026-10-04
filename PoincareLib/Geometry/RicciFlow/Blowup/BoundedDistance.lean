import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance
import PoincareLib.Geometry.RicciFlow.Blowup.Sequence

/-!
# Bounded-distance estimates on generalized blowup sequences

Adapted without changing declaration bodies from Mapher commit
`4a6b36794e04c3fac86663910a73a924fed43f23`.
Morgan--Tian, Theorem 10.2, pp. 245--246, and the opening of the proof of
Theorem 11.1, p. 269. The uniform estimate remains an explicit premise.
See `references/ricci-flow/mapher/reviewed-bounded-distance.md`.
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure GeneralizedBoundedDistanceHypotheses
    (S : GeneralizedBlowupSequence.{u}) (epsilon C : ℝ) where
  branch : ∀ k, generalizedPinchedOrNonnegative (S.flow k)
  canonical : ∀ k, generalizedEarlierStrongCanonicalNeighborhoods
    (S.flow k) epsilon C (S.base k).1 (S.base k).2

structure RepairedGeneralizedBoundedDistanceTheory : Prop where
  /-- The applied M28 threshold and estimates, with no remaining theory premise. -/
  constants : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ C : ℝ, 0 < C →
        ∀ (S : GeneralizedBlowupSequence.{u}),
          GeneralizedBoundedDistanceHypotheses S epsilon C →
            GeneralizedBlowupBoundedDistance S

/-- The earlier-time corollary of the weak Hamilton--Ivey bounded-distance
estimate, with no time normalization on the nonnegative branch. -/
theorem m29GeneralizedBoundedDistance
    (P : RepairedBoundedDistanceTheory.{u}) :
    RepairedGeneralizedBoundedDistanceTheory.{u} := by
  rcases P.constants with ⟨epsilon0, hepsilon0, hsmall, estimate⟩
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

end PoincareMT
