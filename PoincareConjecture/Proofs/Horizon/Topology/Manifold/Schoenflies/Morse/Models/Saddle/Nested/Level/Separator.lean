import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Level.Components

noncomputable section
set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)

def sectionPolynomial (q : E2) : Real := ‖q‖^2 + (sourceHeight q)^2

theorem continuous_sectionPolynomial : Continuous sectionPolynomial := by
  unfold sectionPolynomial sourceHeight
  fun_prop

def filledSection : Set E2 := {q | sectionPolynomial q ≤ 1} ∪ closedBall 0 (79 / 100)

theorem isCompact_filledSection : IsCompact filledSection := by
  have hsub : {q : E2 | sectionPolynomial q ≤ 1} ⊆ closedBall 0 1 := by
    intro q hq
    rw [mem_closedBall_zero_iff]
    change ‖q‖^2 + (sourceHeight q)^2 ≤ 1 at hq
    nlinarith [sq_nonneg (sourceHeight q), norm_nonneg q]
  exact ((isCompact_closedBall 0 1).of_isClosed_subset
    (isClosed_le continuous_sectionPolynomial continuous_const) hsub).union
      (isCompact_closedBall 0 (79 / 100))

theorem separator_sphere_sublevel {q : E2} (hq : q ∈ sphere 0 (79 / 100)) :
    sectionPolynomial q < 1 := by
  have hn := mem_sphere_zero_iff_norm.mp hq
  have hxy : (q 0)^2 + (q 1)^2 = (79 / 100 : Real)^2 := by
    rw [← norm_sq_two, hn]
  have hx : -(79 / 100 : Real) ≤ q 0 ∧ q 0 ≤ 79 / 100 := by
    constructor <;> nlinarith [sq_nonneg (q 1)]
  have hz : (1389 / 10000 : Real) ≤ sourceHeight q ∧ sourceHeight q ≤ 6129 / 10000 := by
    dsimp [sourceHeight]
    constructor <;> nlinarith [hx.1, hx.2]
  have hs : 0 ≤ ((6129 / 10000 : Real) - sourceHeight q) *
      ((6129 / 10000 : Real) + sourceHeight q) :=
    mul_nonneg (by linarith [hz.2]) (by linarith [hz.1])
  dsimp [sectionPolynomial]
  rw [hn]
  nlinarith

theorem innerOval_subset_separator_ball : innerOval ⊆ ball (0 : E2) (79 / 100) := by
  intro q hq
  have hz := sourceHeight_mem_of_mem_innerOval hq
  have hroot : (63 / 100 : Real) < upperRoot := by
    have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 19)
    have hn := Real.sqrt_nonneg (19 : Real)
    dsimp [upperRoot]
    nlinarith
  have he := (mem_levelSet_iff q).mp (levelSet_eq_outerOval_union_innerOval ▸ Or.inr hq)
  rw [mem_ball_zero_iff]
  nlinarith [hz.1, sq_nonneg (sourceHeight q - 63 / 100), norm_nonneg q]

private theorem strict_sublevel_subset_interior_filledSection :
    {q : E2 | sectionPolynomial q < 1} ⊆ interior filledSection :=
  (isOpen_lt continuous_sectionPolynomial continuous_const).subset_interior_iff.mpr
    (fun q hq => Or.inl (show sectionPolynomial q ≤ 1 from le_of_lt hq))

private theorem separator_ball_subset_interior_filledSection :
    ball (0 : E2) (79 / 100) ⊆ interior filledSection :=
  isOpen_ball.subset_interior_iff.mpr (fun _ hq => Or.inr (ball_subset_closedBall hq))

theorem frontier_filledSection_subset_outerOval : frontier filledSection ⊆ outerOval := by
  intro q hq
  have hnot : q ∉ interior filledSection := hq.2
  have hparts := frontier_union_subset {q : E2 | sectionPolynomial q ≤ 1}
    (closedBall (0 : E2) (79 / 100)) hq
  rcases hparts with hs | hr
  · have he := frontier_le_subset_eq continuous_sectionPolynomial continuous_const hs.1
    have hlevel : q ∈ levelSet := (mem_levelSet_iff q).mpr he
    rcases levelSet_eq_outerOval_union_innerOval ▸ hlevel with ho | hi
    · exact ho
    · exact (hnot (separator_ball_subset_interior_filledSection
        (innerOval_subset_separator_ball hi))).elim
  · rw [frontier_closedBall _ (by norm_num : (79 / 100 : Real) ≠ 0)] at hr
    exact (hnot (strict_sublevel_subset_interior_filledSection
      (separator_sphere_sublevel hr.2))).elim

end Poincare.Manifold.Schoenflies.Saddle.Nested
