import PoincareConjecture.Statements.M65
import PoincareConjecture.Proofs.M65.Mathlib.IntervalHomotopy

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {t₀ t₁ : ℝ} {P : M65RawFlowInput M t₀ t₁}
  {zeta circumference : ℝ}
  {A : M63RawApproximation P.flow P.family zeta}
  {product : M62.CircleProductData P.flow circumference}

theorem m65ProjectedFamily_homotopic
    (S : M63ProductSolutionFamily product A) (t : Set.Icc t₀ t₁) :
    P.family.Homotopic (S.projected t) := by
  have h := ContinuousMap.homotopic_of_continuous_icc
    S.projected S.projected_continuous ⟨t₀, le_rfl, P.time_ordered⟩ t
  rw [S.projected_initial ⟨le_rfl, P.time_ordered⟩] at h
  exact A.homotopic.trans h

theorem m65ProjectedFamily_initial_area_close
    (S : M63ProductSolutionFamily product A) (c : LoopTwoSphere) :
    |fillingArea (P.flow.metric t₀)
        (S.projected ⟨t₀, le_rfl, P.time_ordered⟩ c) -
      fillingArea (P.flow.metric t₀) (P.family c)| < zeta := by
  rw [S.projected_initial ⟨le_rfl, P.time_ordered⟩]
  exact A.area_error c

def m65DeformedFamilyOfProjectedEstimate
    (S : M63ProductSolutionFamily product A)
    (terminal : ∀ c,
      freeLoopLength (P.flow.metric t₁)
          (S.projected ⟨t₁, P.time_ordered, le_rfl⟩ c) < zeta ∨
        fillingArea (P.flow.metric t₁)
            (S.projected ⟨t₁, P.time_ordered, le_rfl⟩ c) ≤
          areaComparisonProfile P.flow
            (fillingArea (P.flow.metric t₀) (A.family c)) t₁ + zeta) :
    M65DeformedFamily M P zeta where
  family := S.projected
  family_continuous := S.projected_continuous
  null := S.projected_null
  free_homotopy_to_initial := m65ProjectedFamily_homotopic S
  initial_area_close := m65ProjectedFamily_initial_area_close S
  terminal_alternative c := by
    rw [S.projected_initial ⟨le_rfl, P.time_ordered⟩]
    exact terminal c

end PoincareConjecture
