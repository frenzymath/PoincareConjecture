import PoincareConjecture.Proofs.M64.FamilyAdapters
import PoincareConjecture.Statements.M64Approximation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}

theorem m64FamilyApproximationTheory_from_static_raw
    (hM63 : M63RampEstimatesTheory.{u})
    (compact : IsCompact (Set.univ : Set M))
    (analytic : M63AnalyticConclusion F G)
    (raw_family : ∀ Gamma : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := M)), M61NullFamily Gamma →
      ∀ zeta : ℝ, 0 < zeta → ∃ N0 : ℕ, 0 < N0 ∧
        ∀ N : ℕ, N0 ≤ N →
          ∃ A : M64RawFamilyApproximation (F.metric a) (F.connection a) Gamma zeta,
            A.count = N) :
    M64FamilyApproximationTheory F G := by
  intro Gamma hnull zeta hzeta
  obtain ⟨N0, hN0, hraw⟩ := raw_family Gamma hnull zeta hzeta
  refine ⟨N0, hN0, ?_⟩
  intro N hNN
  obtain ⟨raw, hcount⟩ := hraw N hNN
  exact m64EvolvingApproximation_from_M63 hM63 compact analytic hnull hzeta raw hcount

end PoincareConjecture
