import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Predecessors
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Generalized.Restriction

/-!
# Bounded distance and uniform backward durations

The opening of the proof of Morgan--Tian Theorem 11.1, p. 269, applies
Theorem 10.2 and Assumption (5) to every fixed normalized terminal ball.
The duration below is uniform in the points of that ball. It still supplies
singleton cylinders; gluing them into a smooth ball cylinder is separate.
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

/-- M29 supplies a positive threshold for the bounded-distance step of
Theorem 11.1, p. 269. The final threshold must also satisfy the later
geometric smallness bounds. -/
theorem exists_boundedDistance_threshold (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
      ∀ (S : GeneralizedBlowupSequence.{u}) (epsilon C kappa r₀ mu : ℝ),
        epsilon ≤ epsilon₀ → M30CommonBlowupControls S epsilon C kappa r₀ mu →
        GeneralizedBlowupBoundedDistance S := by
  obtain ⟨epsilon29, hepsilon29, _, hbound⟩ := P.m29.constants
  refine ⟨min epsilon29 (1 / 400), lt_min hepsilon29 (by norm_num),
    min_le_right _ _, ?_⟩
  intro S epsilon C kappa r₀ mu hle H
  exact hbound epsilon H.epsilon_pos (hle.trans (min_le_left _ _)) C H.C_pos S
    ⟨H.branch, H.canonical⟩

variable {S : GeneralizedBlowupSequence.{u}} {k : ℕ}
  {x : ((S.flow k).slice (S.base k).1).carrier} {mu D : ℝ}

/-- The duration denominator is positive even if the point's scalar is
negative (Theorem 11.1, Assumption (5), p. 268). -/
theorem backwardDuration_denominator_pos :
    0 < max (S.scale k) ((S.flow k).scalar ⟨(S.base k).1, x⟩) :=
  (S.base_scalar_pos k).trans_le (le_max_left _ _)

/-- Positive survival constant gives a positive normalized duration
(Theorem 11.1, Assumption (5), p. 268). -/
theorem backwardDuration_pos (hmu : 0 < mu) :
    0 < m30BackwardDuration S k x mu :=
  div_pos (mul_pos hmu (S.base_scalar_pos k)) backwardDuration_denominator_pos

/-- The normalized duration never exceeds its survival constant
(Theorem 11.1, Assumption (5), p. 268). -/
theorem backwardDuration_le (hmu : 0 ≤ mu) :
    m30BackwardDuration S k x mu ≤ mu := by
  apply (div_le_iff₀ backwardDuration_denominator_pos).mpr
  exact mul_le_mul_of_nonneg_left (le_max_left _ _) hmu

/-- A scalar bound gives the uniform positive duration used at the opening
of Theorem 11.1, p. 269. -/
theorem le_backwardDuration (hmu : 0 ≤ mu) (hD : 1 ≤ D)
    (hR : (S.flow k).scalar ⟨(S.base k).1, x⟩ ≤ D * S.scale k) :
    mu / D ≤ m30BackwardDuration S k x mu := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hmax : max (S.scale k) ((S.flow k).scalar ⟨(S.base k).1, x⟩) ≤
      D * S.scale k := by
    refine max_le ?_ hR
    exact le_mul_of_one_le_left (S.base_scalar_pos k).le hD
  apply (le_div_iff₀ backwardDuration_denominator_pos).mpr
  calc
    mu / D * max (S.scale k) ((S.flow k).scalar ⟨(S.base k).1, x⟩) ≤
        mu / D * (D * S.scale k) :=
      mul_le_mul_of_nonneg_left hmax (div_nonneg hmu hDpos.le)
    _ = mu * S.scale k := by rw [← mul_assoc, div_mul_cancel₀ _ hDpos.ne']

/-- M29 and Assumption (5) supply a common backward singleton cylinder at
each point of a fixed normalized ball (Theorem 11.1, p. 269). This statement
does not assert that the independently selected cylinders form a smooth map
of the spatial variable. -/
theorem exists_uniform_backward_worldlines
    (hbound : GeneralizedBlowupBoundedDistance S)
    (hmu : 0 < mu) (hsurvival : GeneralizedMaximalBackwardFlowLineSurvival S mu)
    (A : ℝ) (hA : 0 < A) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ᶠ k : ℕ in atTop,
      ∀ x ∈ S.baseBall k A,
        ∃ e : GeneralizedFlowCylinder (S.flow k) ((S.flow k).slice (S.base k).1)
          (S.base k).1 (S.scale k) (Set.Icc (-tau) 0) ({x} : Set _),
          ∀ h₀, e.pointMap 0 h₀ x = (⟨(S.base k).1, x⟩ : (S.flow k).point) := by
  obtain ⟨D, _, hD⟩ := hbound A hA
  have hmax : 0 < max 1 D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨mu / max 1 D, div_pos hmu hmax, ?_⟩
  filter_upwards [hD, hsurvival A hA] with k hk hsurv
  intro x hx
  obtain ⟨line⟩ := hsurv x hx
  have hR : (S.flow k).scalar ⟨(S.base k).1, x⟩ ≤ max 1 D * S.scale k :=
    (hk x hx).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (S.base_scalar_pos k).le)
  have htime : Set.Icc (-(mu / max 1 D)) 0 ⊆ line.maximal_interval := by
    apply Set.Subset.trans _ line.requested_interval_subset
    intro t ht
    exact ⟨(neg_le_neg (le_backwardDuration hmu.le (le_max_left 1 D) hR)).trans ht.1, ht.2⟩
  refine ⟨Cylinder.restrict line.embedding htime Set.Subset.rfl, ?_⟩
  intro h₀
  exact line.zero_identity

end PoincareMT.M30
