import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith









set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Topology intervalIntegral

namespace intervalIntegral




theorem sub_le_integral_of_nonneg_approximation
    {T L : ℝ → ℝ} {R : ℝ → ℝ → ℝ} {A B a b : ℝ} (hA : 0 ≤ A)
    (hT : ContinuousOn T (Icc a b)) (hL : ContinuousOn L (Icc a b))
    (hR : ∀ ε : ℝ, 0 < ε → ContinuousOn (R ε) (Icc a b))
    (herror : ∀ ε : ℝ, 0 < ε → ∀ r ∈ Icc a b,
      0 ≤ R ε r - T r ∧ R ε r - T r ≤ ε * L r)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ s t : ℝ,
      s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      R ε t - R ε s ≤ ∫ r in s..t, A * R ε r + B * L r)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    T t - T s ≤ ∫ r in s..t, A * T r + B * L r := by
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have hTi : IntervalIntegrable T volume s t :=
    (hT.mono (by simpa only [uIcc_of_le hst] using hsub)).intervalIntegrable
  have hLi : IntervalIntegrable L volume s t :=
    (hL.mono (by simpa only [uIcc_of_le hst] using hsub)).intervalIntegrable
  let I : ℝ := ∫ r in s..t, A * T r + B * L r
  let C : ℝ := L s + A * ∫ r in s..t, L r
  have happrox (ε : ℝ) (hε : 0 < ε) : T t - T s ≤ I + ε * C := by
    have hRi : IntervalIntegrable (R ε) volume s t :=
      ((hR ε hε).mono (by simpa only [uIcc_of_le hst] using hsub)).intervalIntegrable
    have hi : (∫ r in s..t, A * R ε r + B * L r) ≤
        I + (A * ε) * ∫ r in s..t, L r := by
      calc
        _ ≤ ∫ r in s..t, (A * T r + B * L r) + (A * ε) * L r := by
          apply integral_mono_on hst ((hRi.const_mul A).add (hLi.const_mul B))
            (((hTi.const_mul A).add (hLi.const_mul B)).add (hLi.const_mul (A * ε)))
          intro r hr
          have he := mul_le_mul_of_nonneg_left (herror ε hε r (hsub hr)).2 hA
          nlinarith
        _ = I + (A * ε) * ∫ r in s..t, L r := by
          rw [integral_add ((hTi.const_mul A).add (hLi.const_mul B))
            (hLi.const_mul (A * ε)), integral_const_mul]
    have hb := hbound ε hε s t hs ht hst
    have he_s := (herror ε hε s hs).2
    have he_t := (herror ε hε t ht).1
    dsimp only [C]
    nlinarith
  have hlim : Tendsto (fun ε : ℝ ↦ I + ε * C) (𝓝[>] 0) (𝓝 I) := by
    have hlim0 : Tendsto (fun ε : ℝ ↦ I + ε * C) (𝓝 0) (𝓝 (I + 0 * C)) :=
      tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
    have hlim' : Tendsto (fun ε : ℝ ↦ I + ε * C) (𝓝[>] 0) (𝓝 (I + 0 * C)) :=
      hlim0.mono_left inf_le_left
    simpa only [zero_mul, add_zero] using hlim'
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact happrox ε hε

end intervalIntegral
