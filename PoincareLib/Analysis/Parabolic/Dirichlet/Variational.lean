import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Variational resolvents on an energy completion

The adjoint of the completed inclusion constructs the variational resolvent.
This is the functional-analytic step in Chow et al., Part III, Section 24.5.1,
Theorem 24.30, p. 290. It follows the construction in Chow--Liao--Qin,
`Analysis/Elliptic/WithBoundary/InteriorVariational.lean`, revision
`1b535dd102b94cc42b107cca27059687888f08b3` (Apache-2.0).
-/

set_option autoImplicit false

noncomputable section

open UniformSpace
open scoped InnerProductSpace

namespace Poincare.Analysis.Dirichlet

variable {V H : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Extend an energy-bounded inclusion to the Hilbert completion. -/
def completionMap (j : V →L[ℝ] H) : Completion V →L[ℝ] H :=
  j.extend Completion.toComplL

@[simp] theorem completionMap_coe (j : V →L[ℝ] H) (v : V) :
    completionMap j v = j v :=
  j.extend_eq Completion.denseRange_coe (Completion.isUniformInducing_coe V) v

theorem norm_completionMap_apply_le (j : V →L[ℝ] H) {C : ℝ}
    (hj : ∀ v, ‖j v‖ ≤ C * ‖v‖) (v : Completion V) :
    ‖completionMap j v‖ ≤ C * ‖v‖ := by
  induction v using Completion.induction_on with
  | hp => exact isClosed_le (completionMap j).continuous.norm (continuous_const.mul continuous_norm)
  | ih v => simpa using hj v

/-- Riesz representation constructs the solution of the variational equation. -/
def resolvent (j : V →L[ℝ] H) : H →L[ℝ] Completion V :=
  (completionMap j).adjoint

theorem resolvent_inner (j : V →L[ℝ] H) (f : H) (v : Completion V) :
    ⟪resolvent j f, v⟫_ℝ = ⟪f, completionMap j v⟫_ℝ :=
  (completionMap j).adjoint_inner_left v f

theorem resolvent_unique (j : V →L[ℝ] H) (f : H) (u : Completion V)
    (hu : ∀ v, ⟪u, v⟫_ℝ = ⟪f, completionMap j v⟫_ℝ) :
    u = resolvent j f := by
  apply ext_inner_right ℝ
  intro v
  rw [hu, resolvent_inner]

/-- It suffices to test the variational equation on the original dense space. -/
theorem resolvent_unique_of_test (j : V →L[ℝ] H) (f : H) (u : Completion V)
    (hu : ∀ v : V, ⟪u, (v : Completion V)⟫_ℝ = ⟪f, j v⟫_ℝ) :
    u = resolvent j f := by
  apply resolvent_unique
  intro v
  induction v using Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (completionMap j).continuous)
  | ih v => simpa using hu v

theorem norm_resolvent_le (j : V →L[ℝ] H) (hj : ∀ v, ‖j v‖ ≤ ‖v‖) :
    ‖resolvent j‖ ≤ 1 := by
  change ‖(completionMap j).adjoint‖ ≤ 1
  rw [LinearIsometryEquiv.norm_map]
  exact (completionMap j).opNorm_le_bound zero_le_one fun v =>
    norm_completionMap_apply_le j (C := 1) (by simpa using hj) v

/-- The resolvent as an operator on the ambient Hilbert space. -/
def ambientResolvent (j : V →L[ℝ] H) : H →L[ℝ] H :=
  (completionMap j).comp (resolvent j)

theorem ambientResolvent_inner (j : V →L[ℝ] H) (f h : H) :
    ⟪ambientResolvent j f, h⟫_ℝ = ⟪resolvent j f, resolvent j h⟫_ℝ := by
  exact ((completionMap j).adjoint_inner_right (resolvent j f) h).symm

theorem ambientResolvent_nonneg (j : V →L[ℝ] H) (f : H) :
    0 ≤ ⟪ambientResolvent j f, f⟫_ℝ := by
  rw [ambientResolvent_inner]
  exact real_inner_self_nonneg

theorem ambientResolvent_isSelfAdjoint (j : V →L[ℝ] H) :
    IsSelfAdjoint (ambientResolvent j) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [ambientResolvent, resolvent, ContinuousLinearMap.adjoint_comp]

end Poincare.Analysis.Dirichlet
