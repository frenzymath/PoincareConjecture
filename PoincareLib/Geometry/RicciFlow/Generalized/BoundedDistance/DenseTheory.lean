import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Dense

/-!
Adapted from Mapher `PoincareMT/Statements/M28BoundedDistance.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M28 bounded-distance curvature statement

The constants are chosen in the order used by Theorem 10.2, before the flow,
time and basepoint are supplied. Its proof supports same-time canonical control;
a compact-path continuity argument gives the dense-time version. Both use one
universal accuracy threshold. The printed earlier-time statement is a checked
corollary. See the regular-time boundary review dated 2026-09-18.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Theorem 10.2's proof uses canonical neighborhoods on the tested slice;
their strong necks already contain the required backward cylinders. -/
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

/-- Scalar and length continuity extend the estimate to times approached by
whole controlled slices; no canonical carrier is asserted at an excluded time. -/
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

structure DenseBoundedDistanceTheory : Prop where
  bounds : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
    M28SameTimeEstimateStatement.{u} epsilon₀ ∧ M28DenseTimeEstimateStatement.{u} epsilon₀

namespace DenseBoundedDistanceTheory

theorem same_time_constants (P : DenseBoundedDistanceTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      M28SameTimeEstimateStatement.{u} epsilon₀ := by
  obtain ⟨epsilon₀, hpos, hsmall, hsame, _⟩ := P.bounds
  exact ⟨epsilon₀, hpos, hsmall, hsame⟩

theorem dense_constants (P : DenseBoundedDistanceTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      M28DenseTimeEstimateStatement.{u} epsilon₀ := by
  obtain ⟨epsilon₀, hpos, hsmall, _, hdense⟩ := P.bounds
  exact ⟨epsilon₀, hpos, hsmall, hdense⟩

/-- The printed earlier-time hypothesis includes its tested time slice. -/
theorem constants (P : DenseBoundedDistanceTheory.{u}) :
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

end DenseBoundedDistanceTheory

end PoincareMT
