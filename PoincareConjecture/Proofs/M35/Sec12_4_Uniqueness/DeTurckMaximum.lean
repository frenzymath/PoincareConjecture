import PoincareConjecture.Proofs.M04.ShiBarrierMaximum

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M35.Uniqueness

theorem nonpositive_of_uniform_end_and_maximum_velocity
    {M : Type*} [TopologicalSpace M] {T L : ℝ} (hT : 0 < T) (hL : 0 ≤ L)
    (v : ℝ → M → ℝ)
    (hcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hinit : ∀ x, v 0 x ≤ 0)
    (hend : ∀ ε > 0, ∀ x : M, ∃ K : Set M, IsCompact K ∧ x ∈ K ∧
      ∀ t ∈ Icc 0 T, ∀ y ∈ K \ interior K, v t y ≤ ε)
    (hvelocity : ∀ t ∈ Ioc 0 T, ∀ x, IsLocalMax (v t) x → 0 < v t x →
      ∃ d : ℝ, HasDerivWithinAt (fun s => v s x) d (Icc 0 T) t ∧ d ≤ L * v t x) :
    ∀ t ∈ Icc 0 T, ∀ x, v t x ≤ 0 := by
  have hε (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ∈ Icc 0 T) (x : M) :
      v t x ≤ ε * Real.exp (L * t) := by
    obtain ⟨K, hK, hxK, hboundary⟩ := hend ε hε x
    let f : ℝ → M → ℝ := fun s y => ε * Real.exp (L * s) - v s y
    have hfinit (y : M) (_hy : y ∈ K) : 0 ≤ f 0 y := by
      dsimp [f]
      simp only [mul_zero, Real.exp_zero, mul_one]
      linarith [hinit y]
    have hfboundary (s : ℝ) (hs : s ∈ Icc 0 T) (y : M)
        (hy : y ∈ K \ interior K) : 0 ≤ f s y := by
      have he : 1 ≤ Real.exp (L * s) :=
        Real.one_le_exp_iff.mpr (mul_nonneg hL hs.1)
      have hb := hboundary s hs y hy
      have hm := mul_le_mul_of_nonneg_left he hε.le
      dsimp [f]
      nlinarith
    have hfcont : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ K) := by
      exact ((continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_fst))).continuousOn.sub
          hcont).mono (prod_mono Subset.rfl (subset_univ K))
    have hfsupport (s : ℝ) (hs : s ∈ Ioc 0 T) (y : M) (hy : y ∈ interior K)
        (hmin : ∀ z ∈ K, f s y ≤ f s z) (hneg : f s y < 0)
        (δ : ℝ) (hδ : 0 < δ) :
        ∃ ψ : ℝ → ℝ, ∃ d : ℝ, ψ s = f s y ∧
          (∀ᶠ r in 𝓝[Icc 0 s] s, f r y ≤ ψ r) ∧
          HasDerivWithinAt ψ d (Icc 0 s) s ∧ -(-L) * f s y - δ ≤ d := by
      have hmax : IsLocalMax (v s) y := by
        filter_upwards [isOpen_interior.mem_nhds hy] with z hz
        have hm := hmin z (interior_subset hz)
        dsimp [f] at hm
        linarith
      have hvpos : 0 < v s y := by
        have hp : 0 < ε * Real.exp (L * s) := mul_pos hε (Real.exp_pos _)
        dsimp [f] at hneg
        linarith
      obtain ⟨d, hd, hdb⟩ := hvelocity s hs y hmax hvpos
      have he : HasDerivAt (fun r => ε * Real.exp (L * r))
          (ε * Real.exp (L * s) * L) s := by
        convert! (((hasDerivAt_id s).const_mul L).exp.const_mul ε) using 1
        simp only [id_eq, mul_one]
        ring
      refine ⟨fun r => f r y, ε * Real.exp (L * s) * L - d, rfl,
        Filter.Eventually.of_forall (fun _ => le_rfl),
        (he.hasDerivWithinAt.sub hd).mono (Icc_subset_Icc le_rfl hs.2), ?_⟩
      dsimp [f]
      nlinarith
    have hf := M04.compact_subset_min_velocity_nonnegative_of_upper_support hK hT f
      hfinit hfboundary hfcont hfsupport t ht x hxK
    exact sub_nonneg.mp hf
  intro t ht x
  by_contra h
  have hv : 0 < v t x := lt_of_not_ge h
  let ε := v t x / (2 * Real.exp (L * t))
  have heps : 0 < ε := div_pos hv (mul_pos zero_lt_two (Real.exp_pos _))
  have hb := hε ε heps t ht x
  have heq : ε * Real.exp (L * t) = v t x / 2 := by
    dsimp [ε]
    field_simp [Real.exp_ne_zero]
  rw [heq] at hb
  linarith

end PoincareConjecture.M35.Uniqueness
