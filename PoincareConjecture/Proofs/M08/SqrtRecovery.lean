import PoincareConjecture.Proofs.M08.SquareEnergy








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem sqrtPullback_regular {a b : ℝ} (ha : 0 ≤ a) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α (Ioo (Real.sqrt a) (Real.sqrt b))) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (fun τ ↦ α (Real.sqrt τ)) (Ioo a b) := by
  have hsqrt : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) 1 Real.sqrt (Ioo a b) := by
    intro τ hτ
    exact (Real.contDiffAt_sqrt (ne_of_gt (ha.trans_lt hτ.1))).contMDiffAt.contMDiffWithinAt
  exact hα.comp hsqrt (fun τ hτ ↦
    ⟨Real.sqrt_lt_sqrt ha hτ.1, Real.sqrt_lt_sqrt (ha.trans hτ.1.le) hτ.2⟩)

theorem regularizedLIntegrand_sqrtPullback {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {a b : ℝ} (ha : 0 ≤ a) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α (Ioo (Real.sqrt a) (Real.sqrt b)))
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt a) (Real.sqrt b)) :
    regularizedLIntegrand F T α s =
      backwardLIntegrand F T (fun τ ↦ α (Real.sqrt τ)) (s ^ 2) * (2 * s) := by
  let δ : ℝ → M := fun τ ↦ α (Real.sqrt τ)
  have hpos := (sq_mem_backward_interior ha hs).1
  have hτ := (sq_mem_backward_interior ha hs).2
  have hδ := ((sqrtPullback_regular ha α hα) (s ^ 2) hτ).contMDiffAt
    (isOpen_Ioo.mem_nhds hτ)
  have hnear : α =ᶠ[𝓝 s] fun r ↦ δ (r ^ 2) := by
    filter_upwards [Ioi_mem_nhds hpos] with r hr
    simp only [δ, Real.sqrt_sq hr.le]
  have hvel : curveVelocity (n := n) α s = (2 * s) • curveVelocity (n := n) δ (s ^ 2) := by
    have heq : curveVelocity (n := n) α s = curveVelocity (n := n) (fun r ↦ δ (r ^ 2)) s := by
      unfold curveVelocity
      rw [hnear.mfderiv_eq]
      rfl
    exact heq.trans (curveVelocity_comp_sq (hδ.mdifferentiableAt one_ne_zero))
  change regularizedLIntegrand F T α s = backwardLIntegrand F T δ (s ^ 2) * (2 * s)
  unfold regularizedLIntegrand backwardLIntegrand
  rw [Real.sqrt_sq hpos.le, hnear.eq_of_nhds]
  simp only [hvel, map_smul, smul_apply, smul_eq_mul]
  ring

noncomputable def backwardPathOfSqrt {J : Set ℝ} (F : RicciFlow n M J)
    (T a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hT : T ∈ J)
    (htime : ∀ τ ∈ Icc a b, T - τ ∈ J)
    (α : ℝ → M) (hcont : ContinuousOn α (Icc (Real.sqrt a) (Real.sqrt b)))
    (hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α (Ioo (Real.sqrt a) (Real.sqrt b)))
    (hint : IntervalIntegrable (regularizedLIntegrand F T α) volume (Real.sqrt a) (Real.sqrt b)) :
    BackwardTimePath F T a b where
  curve := fun τ ↦ α (Real.sqrt τ)
  nonnegative := ha
  ordered := hab
  terminal_mem := hT
  time_mem := htime
  continuous := hcont.comp Real.continuous_sqrt.continuousOn
    (fun τ hτ ↦ ⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩)
  regular := sqrtPullback_regular ha α hreg
  l_integrable := intervalIntegrable_of_square_transform ha hab.le hint
    (fun _ hs ↦ regularizedLIntegrand_sqrtPullback F T ha α hreg hs)

theorem backwardPathOfSqrt_action {J : Set ℝ} (F : RicciFlow n M J)
    (T a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hT : T ∈ J)
    (htime : ∀ τ ∈ Icc a b, T - τ ∈ J)
    (α : ℝ → M) (hcont : ContinuousOn α (Icc (Real.sqrt a) (Real.sqrt b)))
    (hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α (Ioo (Real.sqrt a) (Real.sqrt b)))
    (hint : IntervalIntegrable (regularizedLIntegrand F T α) volume (Real.sqrt a) (Real.sqrt b)) :
    backwardLLength F T a b (backwardPathOfSqrt F T a b ha hab hT htime α hcont hreg hint).curve =
      regularizedLAction F T a b α := by
  rw [backwardLLength_eq_transformed]
  apply intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_le_sqrt hab.le)
  intro s hs
  exact (regularizedLIntegrand_sqrtPullback F T ha α hreg hs).symm

end PoincareConjecture.M08
