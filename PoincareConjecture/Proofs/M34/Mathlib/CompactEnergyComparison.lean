import PoincareConjecture.Proofs.M04.CompactParabolic
import Mathlib.Analysis.SpecialFunctions.Sqrt










set_option autoImplicit false

open Set

namespace Real



noncomputable def quadraticGrowthBarrier (c B t : ℝ) : ℝ := B / (1 - c * B * t)



theorem quadraticGrowthBarrier_zero (c B : ℝ) : quadraticGrowthBarrier c B 0 = B := by
  simp [quadraticGrowthBarrier]



theorem hasDerivAt_quadraticGrowthBarrier (c B t : ℝ) (ht : 1 - c * B * t ≠ 0) :
    HasDerivAt (quadraticGrowthBarrier c B)
      (c * quadraticGrowthBarrier c B t ^ 2) t := by
  have hd := (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).const_mul (c * B))
  have h := (hasDerivAt_const t B).div hd ht
  convert! h using 1
  dsimp [quadraticGrowthBarrier]
  field_simp
  ring



theorem quadraticGrowthBarrier_le_twice {c B t : ℝ} (hB : 0 ≤ B)
    (ht : c * B * t ≤ 1 / 2) : quadraticGrowthBarrier c B t ≤ 2 * B := by
  have hden : 0 < 1 - c * B * t := by linarith
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_le_mul_of_nonneg_left ht hB]

end Real




theorem compact_nonnegative_norm_le_quadraticGrowthBarrier
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {T B c : ℝ}
    (hT : 0 < T) (hB : 0 < B) (hc : 0 ≤ c) (hden : c * B * T < 1)
    (N V : ℝ → X → ℝ)
    (hcont : ContinuousOn (Function.uncurry N) (Icc 0 T ×ˢ (univ : Set X)))
    (hN : ∀ t ∈ Icc 0 T, ∀ x : X, 0 ≤ N t x)
    (hderiv : ∀ t ∈ Icc 0 T, ∀ x : X,
      HasDerivWithinAt (fun s => N s x ^ 2) (V t x) (Icc 0 T) t)
    (hmax : ∀ t ∈ Ioc 0 T, ∀ x : X,
      (∀ z : X, N t z ^ 2 ≤ N t x ^ 2) → V t x ≤ c * N t x ^ 3)
    (hinit : ∀ x : X, N 0 x ≤ B) :
    ∀ t ∈ Icc 0 T, ∀ x : X, N t x ≤ Real.quadraticGrowthBarrier c B t := by
  let y := Real.quadraticGrowthBarrier c B
  have hdpos (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < 1 - c * B * t := by
    have hb := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hc hB.le)
    linarith
  have hypos (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < y t :=
    div_pos hB (hdpos t ht)
  have hyd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt y (c * y t ^ 2) t :=
    Real.hasDerivAt_quadraticGrowthBarrier c B t (ne_of_gt (hdpos t ht))
  have hycont : ContinuousOn y (Icc 0 T) :=
    fun t ht => (hyd t ht).continuousAt.continuousWithinAt
  have hyp : ContinuousOn (fun p : ℝ × X => y p.1) (Icc 0 T ×ˢ univ) :=
    hycont.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  let f : ℝ → X → ℝ := fun t x => y t ^ 2 - N t x ^ 2
  let v : ℝ → X → ℝ := fun t x => 2 * c * y t ^ 3 - V t x
  have hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set X)) :=
    (hyp.pow 2).sub (hcont.pow 2)
  have hv : ∀ t ∈ Icc 0 T, ∀ x : X,
      HasDerivWithinAt (fun s => f s x) (v t x) (Icc 0 T) t := by
    intro t ht x
    have hy2 : HasDerivAt (fun s => y s ^ 2) (2 * c * y t ^ 3) t := by
      convert! (hyd t ht).pow 2 using 1
      ring
    exact hy2.hasDerivWithinAt.sub (hderiv t ht x)
  have hcoef : ContinuousOn (fun p : ℝ × X => c * (y p.1 + N p.1 p.2))
      (Icc 0 T ×ˢ univ) := continuousOn_const.mul (hyp.add hcont)
  obtain ⟨A, hA⟩ := ((isCompact_Icc.prod isCompact_univ).image_of_continuousOn hcoef).bddAbove
  have hminimum : ∀ t ∈ Ioc 0 T, ∀ x : X,
      (∀ z : X, f t x ≤ f t z) → f t x ≤ 0 → -(-A) * f t x ≤ v t x := by
    intro t ht x hmin hfneg
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have hmaxN : ∀ z : X, N t z ^ 2 ≤ N t x ^ 2 := by
      intro z
      have hm := hmin z
      dsimp [f] at hm
      linarith
    have hvel := hmax t ht x hmaxN
    have hy := (hypos t ht').le
    have hn := hN t ht' x
    have hyN : y t ≤ N t x := by
      dsimp [f] at hfneg
      nlinarith
    have hpoly : (y t + N t x) * (y t ^ 2 - N t x ^ 2) ≤
        y t ^ 3 - N t x ^ 3 := by
      nlinarith only [mul_nonneg (mul_nonneg hy hn) (sub_nonneg.mpr hyN)]
    have hax : c * (y t + N t x) ≤ A :=
      hA (mem_image_of_mem _ (show (t, x) ∈ Icc 0 T ×ˢ univ from ⟨ht', mem_univ x⟩))
    have hmul := mul_le_mul_of_nonpos_right hax hfneg
    have hpoly' := mul_le_mul_of_nonneg_left hpoly hc
    have hycube := mul_nonneg hc (pow_nonneg hy 3)
    dsimp [f, v] at hmul ⊢
    nlinarith
  have hinitial : ∀ x : X, 0 ≤ f 0 x := by
    intro x
    have hn := hN 0 ⟨le_rfl, hT.le⟩ x
    have hb := hinit x
    dsimp [f, y]
    rw [Real.quadraticGrowthBarrier_zero]
    nlinarith
  have hbound := PoincareConjecture.M04.compact_min_velocity_nonnegative
    (K := -A) hT f v hf hv hminimum hinitial
  intro t ht x
  have hb := hbound t ht x
  have hn := hN t ht x
  have hy := (hypos t ht).le
  dsimp [f] at hb
  change N t x ≤ y t
  nlinarith
