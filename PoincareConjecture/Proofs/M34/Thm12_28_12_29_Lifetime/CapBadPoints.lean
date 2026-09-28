import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapScalarBounds
import PoincareConjecture.Proofs.M34.Mathlib.EarlierBadPoint











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

variable {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0)
  (P : M34StandardCapPredecessors)
  (R : OrdinaryProductRicciGeometry F.flow.metric (partialFlowSpacetimeInterval F))

local notation "G" => ordinaryChapter11Flow
  (I := partialFlowSpacetimeInterval F) (F := F.flow) R

include P



theorem partialFlow_chapter11_bad_points (Good : (G).point → Prop)
    (hbad : ∀ Q : ℝ, 0 < Q → ∃ p : (G).point, Q ≤ (G).scalar p ∧ ¬ Good p) :
    ∃ p : ℕ → (G).point,
      (∀ k : ℕ, (k : ℝ) + 1 < (G).scalar (p k) ∧ ¬ Good (p k) ∧
        ∀ q : (G).point, q.1 ≤ (p k).1 → 4 * (G).scalar (p k) ≤ (G).scalar q → Good q) ∧
      Tendsto (fun k => (G).scalar (p k)) atTop atTop := by
  classical
  have hchoose (k : ℕ) : ∃ p : (G).point,
      (k : ℝ) + 1 < (G).scalar p ∧ ¬ Good p ∧
        ∀ q : (G).point, q.1 ≤ p.1 → 4 * (G).scalar p ≤ (G).scalar q → Good q := by
    obtain ⟨p0, hseed, hbad0⟩ := hbad (2 * ((k : ℝ) + 1) + 1) (by positivity)
    obtain ⟨B, hB⟩ := partialFlow_chapter11_scalar_past_bound F P R
      (ordinaryChapter11Point_time_mem R p0)
    have hbounded : BddAbove ((G).scalar '' {p : (G).point | p.1 ≤ p0.1 ∧ ¬ Good p}) := by
      refine ⟨B, ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      exact hB q hq.1
    have hpos : 0 < (G).scalar p0 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    obtain ⟨p, _, hp, hvalue, hgood⟩ := exists_bad_point_with_earlier_good
      (fun p : (G).point => p.1) (G).scalar Good p0 hbad0 hpos hbounded
    have hpvalue : (k : ℝ) + 1 < (G).scalar p := by linarith
    refine ⟨p, hpvalue, hp, ?_⟩
    intro q htime hhigh
    apply hgood q htime
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  choose p hp using hchoose
  refine ⟨p, hp, ?_⟩
  apply tendsto_atTop_mono (g := fun k : ℕ => (G).scalar (p k))
    (f := fun k : ℕ => (k : ℝ)) _ tendsto_natCast_atTop_atTop
  intro k
  linarith [(hp k).1]

end PoincareConjecture.M34
