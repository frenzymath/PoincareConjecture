import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.DenseTheory

/-!
# Bounded-distance estimates from dense-time canonical control

Adapted from Mapher commit `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`,
Definitions/Statements M28BoundedDistance. The service remains an explicit
predecessor hypothesis. The earlier-time interface is preserved and recovered
by `DenseTime.BoundedDistanceTheory.toEarlierTime`.

Morgan--Tian, Theorem 10.2, pp. 245--246; the source regular-time boundary
review of 18 September 2026. See
`references/ricci-flow/mapher/dense-time-bounded-distance.md`.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

namespace DenseTime

def SameTimeEstimateStatement (epsilon₀ : ℝ) : Prop :=
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

def DenseTimeEstimateStatement (epsilon₀ : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
    ∀ C : ℝ, 0 < C → ∀ A : ℝ, 0 ≤ A →
      ∃ D₀ D : ℝ, 0 < D₀ ∧ 0 < D ∧
        ∀ F : GeneralizedRicciFlowData.{u},
          generalizedWeakHamiltonIveyPinched F →
          ∀ t, t ∈ F.interval → ∀ x : (F.slice t).carrier,
            D₀ ≤ F.scalar ⟨t, x⟩ →
            generalizedEarlierDenseStrongCanonicalNeighborhoods F epsilon C t x →
            RepairedBoundedDistanceEstimate F A D t x

/-- The current source service supplies both estimates at one accuracy threshold. -/
abbrev BoundedDistanceTheory : Prop := DenseBoundedDistanceTheory.{u}

theorem BoundedDistanceTheory.same_time_constants (P : BoundedDistanceTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      SameTimeEstimateStatement.{u} epsilon₀ := by
  obtain ⟨epsilon₀, hpos, hsmall, hsame, _⟩ := P.bounds
  exact ⟨epsilon₀, hpos, hsmall, hsame⟩

theorem BoundedDistanceTheory.dense_constants (P : BoundedDistanceTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      DenseTimeEstimateStatement.{u} epsilon₀ := by
  obtain ⟨epsilon₀, hpos, hsmall, _, hdense⟩ := P.bounds
  exact ⟨epsilon₀, hpos, hsmall, hdense⟩

/-- The printed earlier-time assumption includes control at the tested time. -/
theorem BoundedDistanceTheory.toEarlierTime
    (P : BoundedDistanceTheory.{u}) :
    PoincareMT.RepairedBoundedDistanceTheory.{u} := by
  obtain ⟨epsilon₀, hpos, hsmall, estimate⟩ := P.same_time_constants
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon hepsilon hle C hC A hA
  obtain ⟨D₀, D, hD₀, hD, bound⟩ := estimate epsilon hepsilon hle C hC A hA
  refine ⟨D₀, D, hD₀, hD, ?_⟩
  intro F hpinched t ht x hx hcanonical
  exact bound F hpinched t ht x hx (hcanonical t ht le_rfl)

end DenseTime

end PoincareMT
