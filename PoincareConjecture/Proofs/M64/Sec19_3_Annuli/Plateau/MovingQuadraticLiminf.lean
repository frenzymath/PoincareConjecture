import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MovingMetricColumns

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness

private theorem inner_tendsto_of_weak_strong
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {u w : ℕ → H} {v z : H} (hu : WeakConverges u v) (hw : Tendsto w atTop (𝓝 z))
    {A : ℝ} (hA : ∀ j, ‖u j‖ ≤ A) :
    Tendsto (fun j => inner ℝ (w j) (u j)) atTop (𝓝 (inner ℝ z v)) := by
  have hzero : Tendsto (fun j => inner ℝ (w j - z) (u j)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm (fun j => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hA j) (norm_nonneg _)))
    simpa only [sub_self, norm_zero, zero_mul] using ((hw.sub_const z).norm.mul_const A)
  have hfixed := hu ((InnerProductSpace.toDual ℝ H) z)
  simp only [InnerProductSpace.toDual_apply_apply] at hfixed
  have hh := hzero.add hfixed
  simpa only [inner_sub_left, sub_add_cancel, zero_add] using hh

variable {X E : Type*} [MeasurableSpace X] {mu : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem lp_norm_sq_integral (u : Lp E 2 mu) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

omit [CompleteSpace E] in
private theorem quadratic_integrable
    (B : X → E →L[ℝ] E →L[ℝ] ℝ) (hB : AEStronglyMeasurable B mu)
    {K : ℝ} (hb : ∀ᵐ x ∂mu, ‖B x‖ ≤ K) (u : Lp E 2 mu) :
    Integrable (fun x => B x (u x) (u x)) mu := by
  have hc : Continuous (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × E => q.1 q.2 q.2) :=
    (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd
  have hm := hc.comp_aestronglyMeasurable (hB.prodMk (Lp.aestronglyMeasurable u))
  have hi : Integrable (fun x => K * ‖u x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
      |>.const_mul K
  apply hi.mono' hm
  filter_upwards [hb] with x hx
  have hh := (B x).le_opNorm₂ (u x) (u x)
  have hs := mul_le_mul_of_nonneg_right hx (sq_nonneg ‖u x‖)
  nlinarith

theorem m64MovingQuadratic_le_liminf
    (B : ℕ → X → E →L[ℝ] E →L[ℝ] ℝ) (B0 : X → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ j, AEStronglyMeasurable (B j) mu) (hB0 : AEStronglyMeasurable B0 mu)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ j, ∀ᵐ x ∂mu, ‖B j x‖ ≤ K)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun j => B j x) atTop (𝓝 (B0 x)))
    (hpos : ∀ j, ∀ᵐ x ∂mu, ∀ v, 0 ≤ B j x v v)
    (hsymm : ∀ j, ∀ᵐ x ∂mu, ∀ v w, B j x v w = B j x w v)
    {u : ℕ → Lp E 2 mu} {v : Lp E 2 mu} (hu : WeakConverges u v)
    {A : ℝ} (hA : ∀ j, ‖u j‖ ≤ A) :
    (∫ x, B0 x (v x) (v x) ∂mu) ≤
      liminf (fun j => ∫ x, B j x (u j x) (u j x) ∂mu) atTop := by
  let R := (InnerProductSpace.toDual ℝ E).symm
  let w := fun j x => R (B j x (v x))
  let w0 := fun x => R (B0 x (v x))
  obtain ⟨hw, hw0, hstrong⟩ := m64Metric_test_columns_strong B B0 hB hB0 hK hbound hlim v
  let W := fun j => (hw j).toLp (w j)
  let W0 := hw0.toLp w0
  have hmixed : Tendsto (fun j => inner ℝ (W j) (u j)) atTop (𝓝 (inner ℝ W0 v)) :=
    inner_tendsto_of_weak_strong hu hstrong hA
  have hfixed : Tendsto (fun j => inner ℝ (W j) v) atTop (𝓝 (inner ℝ W0 v)) :=
    hstrong.inner tendsto_const_nhds
  have hq0 : inner ℝ W0 v = ∫ x, B0 x (v x) (v x) ∂mu := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw0.coeFn_toLp] with x hx
    change W0 x = w0 x at hx
    rw [hx]
    exact InnerProductSpace.toDual_symm_apply
  have hsupport : Tendsto (fun j => 2 * inner ℝ (W j) (u j) - inner ℝ (W j) v) atTop
      (𝓝 (∫ x, B0 x (v x) (v x) ∂mu)) := by
    have hh := (hmixed.const_mul 2).sub hfixed
    simpa only [two_mul, add_sub_cancel_right, hq0] using hh
  have hqi (j : ℕ) : Integrable (fun x => B j x (u j x) (u j x)) mu :=
    quadratic_integrable (B j) (hB j) (hbound j) (u j)
  have hsupport_le (j : ℕ) : 2 * inner ℝ (W j) (u j) - inner ℝ (W j) v ≤
      ∫ x, B j x (u j x) (u j x) ∂mu := by
    rw [L2.inner_def, L2.inner_def, ← integral_const_mul,
      ← integral_sub ((L2.integrable_inner (W j) (u j)).const_mul 2)
        (L2.integrable_inner (W j) v)]
    apply integral_mono_ae
      (((L2.integrable_inner (W j) (u j)).const_mul 2).sub (L2.integrable_inner (W j) v))
      (hqi j)
    filter_upwards [(hw j).coeFn_toLp, hpos j, hsymm j] with x hx hp hs
    change W j x = w j x at hx
    simp only [Pi.sub_apply, hx]
    change 2 * inner ℝ (R (B j x (v x))) (u j x) -
      inner ℝ (R (B j x (v x))) (v x) ≤ B j x (u j x) (u j x)
    rw [InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply]
    have hh := hp (u j x - v x)
    simp only [map_sub, sub_apply] at hh
    rw [hs (u j x) (v x)] at hh
    linarith
  have hA0 : 0 ≤ A := (norm_nonneg (u 0)).trans (hA 0)
  have hupper (j : ℕ) : (∫ x, B j x (u j x) (u j x) ∂mu) ≤ K * A ^ 2 := by
    have hnint := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (u j))).mp
      (Lp.memLp (u j))
    calc
      _ ≤ ∫ x, K * ‖u j x‖ ^ 2 ∂mu := by
        apply integral_mono_ae (hqi j) (hnint.const_mul K)
        filter_upwards [hbound j] with x hx
        exact (le_abs_self _).trans (by
          have hnorm := (B j x).le_opNorm₂ (u j x) (u j x)
          have hs := mul_le_mul_of_nonneg_right hx (sq_nonneg ‖u j x‖)
          rw [Real.norm_eq_abs] at hnorm
          nlinarith)
      _ = K * ‖u j‖ ^ 2 := by rw [integral_const_mul, ← lp_norm_sq_integral]
      _ ≤ K * A ^ 2 := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) hA0).mpr (hA j)) hK
  rw [← hsupport.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall hsupport_le) hsupport.isBoundedUnder_ge
    ((isBoundedUnder_of_eventually_le (Eventually.of_forall hupper)).isCoboundedUnder_ge)

end PoincareConjecture
