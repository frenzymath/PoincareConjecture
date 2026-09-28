import PoincareConjecture.Statements.M29GeneralizedDistance
import PoincareConjecture.Proofs.M28.Sec10_1_Pinching

set_option autoImplicit false

open Filter

universe u

namespace PoincareConjecture

theorem m29GeneralizedBoundedDistance
    (P : RepairedBoundedDistanceTheory.{u}) :
    RepairedGeneralizedBoundedDistanceTheory.{u} := by
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

end PoincareConjecture
