import PoincareConjecture.Statements.M15Noncollapsing
import PoincareConjecture.Proofs.M15.Thm8_1_Assembly
import PoincareConjecture.Proofs.M15.Thm8_1_Provider
import PoincareConjecture.Proofs.M15.Thm8_10_Assembly

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareConjecture

theorem noncollapsingGeneralizedAndCompact
    (n : ℕ)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hM12 : ∀ d : ℕ, GeneralizedRicciGaugeTheory.{u} d)
    (hM13 : ∀ d : ℕ, GeneralizedParabolicRescalingTheory.{u} d)
    (hM14 : ∀ d : ℕ, GeneralizedLGeometryTheory.{u} d)
    (hOrdinary : M14OrdinaryProviders.{u} 3) :
    NoncollapsingConclusion.{u} n := by
  refine {
    generalized := {
      uniform := Proofs.M15.generalizedUniformTheorem hM04 n (hM12 n) (hM13 n) (hM14 n)
      provider_bridge := ?_
    }
    compact := ⟨Proofs.M15.compactTheorem810 hM04 (hM12 3) (hM13 3) (hM14 3) hOrdinary⟩
  }
  intro X _ time I G Omega taubar l0 V r0 U
  exact Proofs.M15.provider_implies_noncollapse G Omega taubar l0 V r0 U

end PoincareConjecture
