import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic

/-! Adapted from Mapher `PoincareMT/Proofs/M08/PathCongruence.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. -/


/-!
# Equality of backward paths on their parameter domains

The action ignores changes outside the open integration interval. Within
velocities respect equality on their domain, including constant curves.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.LGeometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- Within velocities respect equality of curves on the within domain. -/
theorem curveVelocityWithin_congr {γ δ : ℝ → M} {I : Set ℝ}
    (h : Set.EqOn γ δ I) {s : ℝ} (hs : s ∈ I) :
    curveVelocityWithin (n := n) γ I s = curveVelocityWithin (n := n) δ I s := by
  unfold curveVelocityWithin
  rw [mfderivWithin_congr_of_mem h hs]
  rfl

/-- A curve constant on its parameter domain has zero within velocity there. -/
theorem curveVelocityWithin_eq_zero_of_constant {γ : ℝ → M} {I : Set ℝ} {x : M}
    (h : ∀ s ∈ I, γ s = x) {s : ℝ} (hs : s ∈ I) :
    curveVelocityWithin (n := n) γ I s = 0 := by
  rw [curveVelocityWithin_congr h hs]
  simp only [curveVelocityWithin, mfderivWithin_const, zero_apply]
  rfl

/-- A locally constant curve has zero ordinary velocity. -/
theorem curveVelocity_eq_zero_of_eventually_constant {γ : ℝ → M} {x : M} {s : ℝ}
    (h : γ =ᶠ[𝓝 s] fun _ ↦ x) : curveVelocity (n := n) γ s = 0 := by
  unfold curveVelocity
  rw [h.mfderiv_eq, mfderiv_const]
  rfl

/-- Backward action depends only on the curve on the open integration interval. -/
theorem backwardLLength_congr_on_interior {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {a b : ℝ} (hab : a ≤ b) {γ δ : ℝ → M}
    (h : Set.EqOn γ δ (Set.Ioo a b)) :
    backwardLLength F T a b γ = backwardLLength F T a b δ := by
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro s hs
  have hnear : γ =ᶠ[𝓝 s] δ :=
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) h
  have hderiv := hnear.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
  simp only [backwardLIntegrand, curveVelocity, hderiv, hnear.eq_of_nhds]
  congr 2
  exact congrArg (fun x : M ↦ (F.metric (T - s)).inner x
    ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) δ s) 1)
    ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) δ s) 1)) hnear.eq_of_nhds

/-- Equality on the closed path interval in particular preserves backward action. -/
theorem backwardLLength_congr {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {a b : ℝ} (hab : a ≤ b) {γ δ : ℝ → M}
    (h : Set.EqOn γ δ (Set.Icc a b)) :
    backwardLLength F T a b γ = backwardLLength F T a b δ :=
  backwardLLength_congr_on_interior F T hab (h.mono Set.Ioo_subset_Icc_self)

end PoincareMT.LGeometry
