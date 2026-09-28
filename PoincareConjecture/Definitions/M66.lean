import PoincareConjecture.Definitions.M65
import PoincareConjecture.Definitions.M58LoopSmoothing

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

structure M66ClassData {t₀ t₁ : ℝ}
    (P : M65RawFlowInput M t₀ t₁) where
  strict_time : t₀ < t₁
  connected : IsConnected (Set.univ : Set M)
  basepoint : M
  pi_two_subsingleton : Subsingleton (HomotopyGroup.Pi 2 M basepoint)

  raw_nontrivial : ¬ P.family.Homotopic (constantLoopFamily basepoint)
  scalar_infimum_attained : ∀ t : Set.Icc t₀ t₁, ∃ x : M,
    (P.flow.connection t.1).scalarCurvature x =
      flowScalarCurvatureInfimum P.flow t.1
  scalar_infimum_continuous : Continuous (fun t : Set.Icc t₀ t₁ =>
    flowScalarCurvatureInfimum P.flow t.1)

noncomputable def m66Width {t₀ t₁ : ℝ}
    (P : M65RawFlowInput M t₀ t₁)
    (t : Set.Icc t₀ t₁) : ℝ :=
  m61FreeClassWidth (P.flow.metric t.1) P.family

end PoincareConjecture
