import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.ScalarIdentity
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.ProperPotential
import PoincareLib.Geometry.Riemannian.Metric.Gradient
import Mathlib.Topology.Order.IntermediateValue

/-!
# Compact regular levels of a shrinking potential

Hamilton conservation and bounded scalar curvature force the gradient norm to
infinity on high potential levels. Properness and connectedness make every
level above the minimum nonempty and compact in the noncompact case.

These are the regularity and exhaustion inputs to Morgan--Tian,
Proposition 9.46, pp. 209-213, and its completion after Claim 9.51, p. 215.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

/-- The squared gradient dominates the potential up to a constant. -/
theorem exists_potential_gradient_sq_lower_bound
    (S : GradientShrinkingSolitonData 3 M) (hD : S.connection.CurvatureTensorCalculus) :
    ∃ A : ℝ, ∀ x : M, S.potential x - A ≤
      S.metric.inner x (S.connection.gradient S.potential x)
        (S.connection.gradient S.potential x) := by
  obtain ⟨K, -, hK⟩ := S.bounded_curvature
  obtain ⟨H, hH⟩ := S.exists_hamilton_conservation_threeDimensional hD
  refine ⟨3 * K - H, ?_⟩
  intro x
  have hR : S.connection.scalarCurvature x ≤ 3 * K :=
    (S.connection.scalarCurvature_le_curvatureTensorNorm_sharp x).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hK x)) (by norm_num))
  linarith [hH x]

/-- Every prescribed squared gradient bound holds on a sufficiently high
closed superlevel of the original potential. -/
theorem exists_gradient_sq_gt_on_superlevel
    (S : GradientShrinkingSolitonData 3 M) (hD : S.connection.CurvatureTensorCalculus)
    (B : ℝ) :
    ∃ a : ℝ, ∀ x : M, a ≤ S.potential x → B <
      S.metric.inner x (S.connection.gradient S.potential x)
        (S.connection.gradient S.potential x) := by
  obtain ⟨A, hA⟩ := S.exists_potential_gradient_sq_lower_bound hD
  refine ⟨A + B + 1, ?_⟩
  intro x hx
  linarith [hA x]

/-- In particular, all sufficiently high potential levels are regular. -/
theorem exists_regular_potential_superlevel
    (S : GradientShrinkingSolitonData 3 M) (hD : S.connection.CurvatureTensorCalculus) :
    ∃ a : ℝ, ∀ x : M, a ≤ S.potential x →
      mfderiv (𝓡 3) 𝓘(ℝ, ℝ) S.potential x ≠ 0 := by
  obtain ⟨a, ha⟩ := S.exists_gradient_sq_gt_on_superlevel hD 0
  refine ⟨a, ?_⟩
  intro x hx hz
  have hg : S.connection.gradient S.potential x = 0 :=
    (S.metric.gradient_eq_zero_iff_mfderiv_eq_zero S.potential x).2 hz
  have hp := ha x hx
  simp [hg] at hp

/-- The potential attains a global minimum. -/
theorem exists_potential_minimum (S : GradientShrinkingSolitonData 3 M) :
    ∃ p : M, ∀ x : M, S.potential p ≤ S.potential x := by
  let q : M := Classical.choice (inferInstance : Nonempty M)
  obtain ⟨p, hp, hmin⟩ := (S.isCompact_potential_sublevel (S.potential q)).exists_isMinOn
    ⟨q, show S.potential q ≤ S.potential q from le_rfl⟩
    S.potential_C2.continuous.continuousOn
  refine ⟨p, ?_⟩
  intro x
  by_cases hx : S.potential x ≤ S.potential q
  · exact hmin hx
  · exact hp.trans (le_of_not_ge hx)

/-- A bounded-above proper potential would make the whole manifold compact. -/
theorem exists_potential_gt_of_noncompact
    (S : GradientShrinkingSolitonData 3 M) (hM : ¬ CompactSpace M) (a : ℝ) :
    ∃ x : M, a < S.potential x := by
  by_contra h
  push Not at h
  apply hM
  have heq : {x : M | S.potential x ≤ a} = univ := by
    ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact h x
  exact isCompact_univ_iff.mp (heq ▸ S.isCompact_potential_sublevel a)

/-- Every level above a given potential value is attained on a noncompact
connected shrinking soliton. -/
theorem potential_level_nonempty_of_noncompact
    (S : GradientShrinkingSolitonData 3 M) (hM : ¬ CompactSpace M)
    (p : M) {a : ℝ} (ha : S.potential p ≤ a) :
    (S.potential ⁻¹' {a}).Nonempty := by
  obtain ⟨q, hq⟩ := S.exists_potential_gt_of_noncompact hM a
  obtain ⟨x, hx⟩ := intermediate_value_univ p q S.potential_C2.continuous ⟨ha, hq.le⟩
  exact ⟨x, hx⟩

/-- Potential levels are compact as subsets of the original manifold. -/
theorem isCompact_potential_level (S : GradientShrinkingSolitonData 3 M) (a : ℝ) :
    IsCompact (S.potential ⁻¹' {a}) := by
  apply (S.isCompact_potential_sublevel a).of_isClosed_subset
    (isClosed_singleton.preimage S.potential_C2.continuous)
  intro x hx
  exact le_of_eq hx

/- Every level above the regularity threshold and a global minimum is a
nonempty compact regular level. -/
theorem exists_nonempty_compact_regular_potential_level_of_noncompact
    (S : GradientShrinkingSolitonData 3 M) (hD : S.connection.CurvatureTensorCalculus)
    (hM : ¬ CompactSpace M) :
    ∃ a : ℝ, ∃ x : M, S.potential x = a ∧
      IsCompact (S.potential ⁻¹' {a}) ∧
      (∀ y : M, a ≤ S.potential y →
        mfderiv (𝓡 3) 𝓘(ℝ, ℝ) S.potential y ≠ 0) := by
  obtain ⟨a₀, ha₀⟩ := S.exists_regular_potential_superlevel hD
  obtain ⟨p, hp⟩ := S.exists_potential_minimum
  let a := max a₀ (S.potential p) + 1
  have hone : (0 : ℝ) ≤ 1 := by norm_num
  have hpa : S.potential p ≤ a := by
    dsimp [a]
    exact (le_max_right _ _).trans (le_add_of_nonneg_right hone)
  obtain ⟨x, hx⟩ := S.potential_level_nonempty_of_noncompact hM p
    hpa
  refine ⟨a, x, hx, S.isCompact_potential_level a, ?_⟩
  intro y hy
  apply ha₀ y
  exact (le_max_left _ _).trans (by dsimp [a] at hy ⊢; linarith)

/-- All sufficiently high potential levels are nonempty compact regular
levels on a noncompact shrinker. -/
theorem exists_high_nonempty_compact_regular_potential_levels
    (S : GradientShrinkingSolitonData 3 M) (hD : S.connection.CurvatureTensorCalculus)
    (hM : ¬ CompactSpace M) :
    ∃ a : ℝ, ∀ b : ℝ, a ≤ b →
      (S.potential ⁻¹' {b}).Nonempty ∧ IsCompact (S.potential ⁻¹' {b}) ∧
        ∀ y : M, b ≤ S.potential y →
          mfderiv (𝓡 3) 𝓘(ℝ, ℝ) S.potential y ≠ 0 := by
  obtain ⟨a, x, hx, -, hreg⟩ :=
    S.exists_nonempty_compact_regular_potential_level_of_noncompact hD hM
  refine ⟨a, fun b hb => ⟨?_, S.isCompact_potential_level b, ?_⟩⟩
  · exact S.potential_level_nonempty_of_noncompact hM x (hx ▸ hb)
  · exact fun y hy => hreg y (hb.trans hy)

end PoincareMT.GradientShrinkingSolitonData
