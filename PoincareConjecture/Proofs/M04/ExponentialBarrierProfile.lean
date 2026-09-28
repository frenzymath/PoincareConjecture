import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic

set_option autoImplicit false

open Set Topology Filter Polynomial
open scoped BigOperators

universe u

namespace PoincareConjecture.M04

theorem deriv_expNegInvGlue (s : ℝ) :
    deriv expNegInvGlue s = s⁻¹ ^ 2 * expNegInvGlue s := by
  have h := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) s).deriv
  simpa using h

theorem deriv_deriv_expNegInvGlue (s : ℝ) :
    deriv (deriv expNegInvGlue) s =
      (s⁻¹ ^ 4 - 2 * s⁻¹ ^ 3) * expNegInvGlue s := by
  rw [show deriv expNegInvGlue = (fun x ↦ x⁻¹ ^ 2 * expNegInvGlue x) by
    funext x; exact deriv_expNegInvGlue x]
  have h := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (X ^ 2 : ℝ[X]) s).deriv
  simp only [eval_X_pow, eval_mul, eval_sub, derivative_X_pow, eval_C] at h
  convert h using 1 <;> ring

set_option maxHeartbeats 1000000 in

theorem exists_exponential_barrier_decay
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {q L G : X → ℝ} (hq : ContinuousOn q K) (hL : ContinuousOn L K)
    (hG : ContinuousOn G K) (hzero : ∀ x ∈ K, q x = 0 → 0 < G x) (b : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ K,
      (b - L x) * deriv expNegInvGlue (q x) -
          G x * deriv (deriv expNegInvGlue) (q x) ≤
        A * expNegInvGlue (q x) := by
  let P : X → ℝ := fun x ↦ (b - L x) * q x ^ 2 -
    (1 - 2 * q x) * G x
  let U : ℝ → Set K := fun A ↦ {x | q x < 0 ∨ P x < A * q x ^ 4}
  have hP : ContinuousOn P K := by
    have hcoef : ContinuousOn (fun x : X ↦ (1 : ℝ) - 2 * q x) K :=
      continuousOn_const.sub (continuousOn_const.mul hq)
    exact ((continuousOn_const.sub hL).mul (hq.pow 2)).sub
      (hcoef.mul hG)
  have hUo (A : ℝ) (hA : 0 < A) : IsOpen (U A) := by
    change IsOpen ({x : K | q x < 0} ∪ {x : K | P x < A * q x ^ 4})
    exact (isOpen_lt hq.domRestrict continuous_const).union
      (isOpen_lt hP.domRestrict ((continuousOn_const.mul (hq.pow 4)).domRestrict))
  have hcover : (Set.univ : Set K) ⊆ ⋃ A : {a : ℝ // 0 < a}, U A := by
    intro x _
    by_cases hx : q x < 0
    · exact mem_iUnion.2 ⟨⟨1, zero_lt_one⟩, Or.inl hx⟩
    by_cases hq0 : q x = 0
    · have hneg : P x < 0 := by
        simpa [P, hq0] using (neg_lt_zero.mpr (hzero x x.property hq0))
      exact mem_iUnion.2 ⟨⟨1, zero_lt_one⟩, Or.inr (by simpa [hq0] using hneg)⟩
    · have hqpos : 0 < q x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hq0)
      let c : ℝ := max 1 (P x / q x ^ 4 + 1)
      have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      have hratio : P x < c * q x ^ 4 := by
        have hq4 : 0 < q x ^ 4 := pow_pos hqpos 4
        have hc' : P x / q x ^ 4 < c := lt_of_lt_of_le
          (by nlinarith [show (0 : ℝ) < 1 from zero_lt_one])
          (le_max_right _ _)
        exact (div_lt_iff₀ hq4).mp hc'
      exact mem_iUnion.2 ⟨⟨c, hc⟩, Or.inr hratio⟩
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨A, hAK⟩ := (isCompact_univ : IsCompact (Set.univ : Set K)).elim_directed_cover
    (fun a : {a : ℝ // 0 < a} ↦ U a)
    (fun a ↦ hUo a a.property)
    hcover
    (by
      intro a b
      let c : {a : ℝ // 0 < a} := ⟨max (a : ℝ) (b : ℝ),
        lt_of_lt_of_le a.property (le_max_left _ _)⟩
      refine ⟨c, ?_, ?_⟩
      · intro x hx
        rcases hx with hxq | hxP
        · exact Or.inl hxq
        · exact Or.inr (hxP.trans_le (mul_le_mul_of_nonneg_right
            (le_max_left _ _) (by positivity)))
      · intro x hx
        rcases hx with hxq | hxP
        · exact Or.inl hxq
        · exact Or.inr (hxP.trans_le (mul_le_mul_of_nonneg_right
            (le_max_right _ _) (by positivity))))
  refine ⟨A, A.property, ?_⟩
  intro x hx
  by_cases hqx : q x ≤ 0
  · have hz : expNegInvGlue (q x) = 0 := expNegInvGlue.zero_of_nonpos hqx
    have hdz : deriv expNegInvGlue (q x) = 0 := by simp [deriv_expNegInvGlue, hz]
    have hddz : deriv (deriv expNegInvGlue) (q x) = 0 := by
      simp [deriv_deriv_expNegInvGlue, hz]
    simp [hz, hdz, hddz]
  · have hqx' : 0 < q x := lt_of_not_ge hqx
    have hmem : (⟨x, hx⟩ : K) ∈ U A := hAK (Set.mem_univ _)
    change q x < 0 ∨ P x < A * q x ^ 4 at hmem
    have hPineq : P x < A * q x ^ 4 :=
      hmem.resolve_left (not_lt_of_ge (le_of_lt hqx'))
    rw [deriv_expNegInvGlue, deriv_deriv_expNegInvGlue]
    have hψ : 0 < expNegInvGlue (q x) := expNegInvGlue.pos_of_pos hqx'
    have hq0 : q x ≠ 0 := ne_of_gt hqx'
    have hcoeff : (b - L x) * (q x)⁻¹ ^ 2 -
        G x * ((q x)⁻¹ ^ 4 - 2 * (q x)⁻¹ ^ 3) ≤ A := by
      apply (le_of_mul_le_mul_right ?_ (pow_pos hqx' 4))
      calc
        ((b - L x) * (q x)⁻¹ ^ 2 -
            G x * ((q x)⁻¹ ^ 4 - 2 * (q x)⁻¹ ^ 3)) * q x ^ 4 = P x := by
              field_simp [hq0]
              ring
        _ ≤ A * q x ^ 4 := hPineq.le
    calc
      _ = ((b - L x) * (q x)⁻¹ ^ 2 -
          G x * ((q x)⁻¹ ^ 4 - 2 * (q x)⁻¹ ^ 3)) * expNegInvGlue (q x) := by
            ring
      _ ≤ A * expNegInvGlue (q x) := mul_le_mul_of_nonneg_right hcoeff hψ.le

end PoincareConjecture.M04

