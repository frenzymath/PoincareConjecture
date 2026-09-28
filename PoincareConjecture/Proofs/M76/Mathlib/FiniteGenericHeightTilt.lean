import PoincareConjecture.Proofs.M76.Mathlib.FiniteGenericHeight
import Mathlib.Topology.Order.OrderClosed











set_option autoImplicit false

open Set Filter
open scoped Topology






theorem Set.Finite.exists_generic_affine_height_tilt
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : s.Finite) (A : E →ᵃ[ℝ] ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (B : E →ₗ[ℝ] ℝ) (δ : ℝ), δ ∈ Ioo 0 ε ∧ InjOn B s ∧
      ∀ t ∈ Ioo (0 : ℝ) δ,
        InjOn (A + t • B.toAffineMap) s ∧
        ∀ x ∈ s, ∀ y ∈ s, A x < A y →
          (A + t • B.toAffineMap) x < (A + t • B.toAffineMap) y := by
  obtain ⟨B, hB⟩ := hs.exists_linearMap_injOn (K := ℝ)
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ s, ∀ y ∈ s,
      A x < A y → A x + t * B x < A y + t * B y := by
    apply hs.eventually_all.mpr
    intro x hx
    apply hs.eventually_all.mpr
    intro y hy
    by_cases hxy : A x < A y
    · have hcontx : ContinuousAt (fun t : ℝ => A x + t * B x) 0 := by fun_prop
      have hconty : ContinuousAt (fun t : ℝ => A y + t * B y) 0 := by fun_prop
      filter_upwards [hcontx.eventually_lt hconty (by simpa only [zero_mul, add_zero] using hxy)]
        with t ht
      exact fun _ => ht
    · exact Eventually.of_forall fun _ h => (hxy h).elim
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min ε η / 2
  have hδ : δ ∈ Ioo (0 : ℝ) ε := by
    dsimp only [δ]
    constructor
    · exact half_pos (lt_min hε hη)
    · exact (half_lt_self (lt_min hε hη)).trans_le (min_le_left _ _)
  refine ⟨B, δ, hδ, hB, ?_⟩
  intro t ht
  have htη : t < η := ht.2.trans_le ((half_le_self (le_of_lt (lt_min hε hη))).trans
    (min_le_right _ _))
  have hstrict : ∀ x ∈ s, ∀ y ∈ s, A x < A y →
      (A + t • B.toAffineMap) x < (A + t • B.toAffineMap) y := by
    intro x hx y hy hxy
    change A x + t * B x < A y + t * B y
    have htball : t ∈ Metric.ball (0 : ℝ) η := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht.1]
      exact htη
    exact hball htball x hx y hy hxy
  refine ⟨?_, hstrict⟩
  intro x hx y hy heq
  rcases lt_trichotomy (A x) (A y) with hxy | hxy | hxy
  · exact (ne_of_lt (hstrict x hx y hy hxy) heq).elim
  · apply hB hx hy
    have heq' : A x + t * B x = A y + t * B y := heq
    rw [hxy] at heq'
    exact (mul_left_cancel₀ ht.1.ne') (add_left_cancel heq')
  · exact (ne_of_lt (hstrict y hy x hx hxy) heq.symm).elim
