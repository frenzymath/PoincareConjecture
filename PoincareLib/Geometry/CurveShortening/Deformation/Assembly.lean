import PoincareLib.Geometry.RicciFlow.Extinction.Width.Deformation.Theory
import PoincareLib.Topology.Homotopy.Interval.Family

/-!
# Structural assembly of the projected deformation

The exact projected ramp solutions give continuous null families and preserve
the raw free homotopy class, as in the paragraph following Claim 19.22,
Morgan--Tian p. 453. The initial estimate is the approximation estimate of
Lemma 19.17. The final constructor packages these facts for Proposition
18.24, p. 433, once the terminal analytic estimate has been established.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {t₀ t₁ : ℝ} {P : M65RawFlowInput M t₀ t₁}
  {zeta circumference : ℝ}
  {A : M63RawApproximation P.flow P.family zeta}
  {product : M62.CircleProductData P.flow circumference}

/-- The projected families after Claim 19.22, p. 453, preserve the input
family's free homotopy class at every included time, in the C1 topology. -/
theorem m65ProjectedFamily_homotopic
    (S : M63ProductSolutionFamily product A) (t : Set.Icc t₀ t₁) :
    P.family.Homotopic (S.projected t) := by
  have h := ContinuousMap.homotopic_of_continuous_icc
    S.projected S.projected_continuous ⟨t₀, le_rfl, P.time_ordered⟩ t
  rw [S.projected_initial ⟨le_rfl, P.time_ordered⟩] at h
  exact A.homotopic.trans h

/-- The initial projected slice is the exact approximation, so Lemma 19.17,
pp. 449-453, gives the initial estimate of Proposition 18.24, p. 433. -/
theorem m65ProjectedFamily_initial_area_close
    (S : M63ProductSolutionFamily product A) (c : LoopTwoSphere) :
    |fillingArea (P.flow.metric t₀)
        (S.projected ⟨t₀, le_rfl, P.time_ordered⟩ c) -
      fillingArea (P.flow.metric t₀) (P.family c)| < zeta := by
  rw [S.projected_initial ⟨le_rfl, P.time_ordered⟩]
  exact A.area_error c

/-- Package the family following Claim 19.22, p. 453, after its terminal
estimate has been proved. The terminal estimate refers to the same actual
solutions and approximation; this constructor alone does not prove M65. -/
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

end PoincareMT
