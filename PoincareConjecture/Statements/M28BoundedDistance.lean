import PoincareConjecture.Definitions.M28BoundedDistance
import PoincareConjecture.Statements.M25NeckCapTopology














set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



def M28SameTimeEstimateStatement (epsilon₀ : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
    ∀ C : ℝ, 0 < C → ∀ A : ℝ, 0 ≤ A →
      ∃ D₀ D : ℝ, 0 < D₀ ∧ 0 < D ∧
        ∀ F : GeneralizedRicciFlowData.{u},
          generalizedWeakHamiltonIveyPinched F →
          ∀ t, t ∈ F.interval → ∀ x : (F.slice t).carrier,
            D₀ ≤ F.scalar ⟨t, x⟩ →
            generalizedSliceStrongCanonicalNeighborhoods F epsilon C
              (4 * F.scalar ⟨t, x⟩) t →
            RepairedBoundedDistanceEstimate F A D t x



def M28DenseTimeEstimateStatement (epsilon₀ : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
    ∀ C : ℝ, 0 < C → ∀ A : ℝ, 0 ≤ A →
      ∃ D₀ D : ℝ, 0 < D₀ ∧ 0 < D ∧
        ∀ F : GeneralizedRicciFlowData.{u},
          generalizedWeakHamiltonIveyPinched F →
          ∀ t, t ∈ F.interval → ∀ x : (F.slice t).carrier,
            D₀ ≤ F.scalar ⟨t, x⟩ →
            generalizedEarlierDenseStrongCanonicalNeighborhoods F epsilon C t x →
            RepairedBoundedDistanceEstimate F A D t x

structure RepairedBoundedDistanceTheory : Prop where
  bounds : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
    M28SameTimeEstimateStatement.{u} epsilon₀ ∧ M28DenseTimeEstimateStatement.{u} epsilon₀

namespace RepairedBoundedDistanceTheory

theorem same_time_constants (P : RepairedBoundedDistanceTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      M28SameTimeEstimateStatement.{u} epsilon₀ := by
  obtain ⟨epsilon₀, hpos, hsmall, hsame, _⟩ := P.bounds
  exact ⟨epsilon₀, hpos, hsmall, hsame⟩

theorem dense_constants (P : RepairedBoundedDistanceTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      M28DenseTimeEstimateStatement.{u} epsilon₀ := by
  obtain ⟨epsilon₀, hpos, hsmall, _, hdense⟩ := P.bounds
  exact ⟨epsilon₀, hpos, hsmall, hdense⟩


theorem constants (P : RepairedBoundedDistanceTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
    ∀ C : ℝ, 0 < C → ∀ A : ℝ, 0 ≤ A →
      ∃ D₀ D : ℝ, 0 < D₀ ∧ 0 < D ∧
        ∀ F : GeneralizedRicciFlowData.{u},
          generalizedWeakHamiltonIveyPinched F →
          ∀ t, t ∈ F.interval → ∀ x : (F.slice t).carrier,
            D₀ ≤ F.scalar ⟨t, x⟩ →
            generalizedEarlierStrongCanonicalNeighborhoods F epsilon C t x →
            RepairedBoundedDistanceEstimate F A D t x := by
  obtain ⟨epsilon₀, hpos, hsmall, estimate⟩ := P.same_time_constants
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon hepsilon hle C hC A hA
  obtain ⟨D₀, D, hD₀, hD, bound⟩ := estimate epsilon hepsilon hle C hC A hA
  refine ⟨D₀, D, hD₀, hD, ?_⟩
  intro F hpinched t ht x hx hcanonical
  exact bound F hpinched t ht x hx (hcanonical t ht le_rfl)

end RepairedBoundedDistanceTheory

end PoincareConjecture
