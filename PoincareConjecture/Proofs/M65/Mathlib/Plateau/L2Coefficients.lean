import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Tactic

set_option autoImplicit false

open Filter
open scoped Topology ENNReal

namespace MeasureTheory

variable {X E F : Type*} [MeasurableSpace X] {mu : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem MemLp.clm_apply_of_ae_bound {p : ℝ≥0∞} {u : X → E}
    (hu : MemLp u p mu) {A : X → E →L[ℝ] F}
    (hA : AEStronglyMeasurable A mu) {C : ℝ}
    (hbound : ∀ᵐ x ∂mu, ‖A x‖ ≤ C) : MemLp (fun x => A x (u x)) p mu := by
  refine hu.of_le_mul (c := C)
    ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).aestronglyMeasurable_comp₂ hA hu.1) ?_
  filter_upwards [hbound] with x hx
  exact (A x).le_opNorm (u x) |>.trans
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

noncomputable def Lp.coefficientL2 (A : X → E →L[ℝ] F)
    (hA : AEStronglyMeasurable A mu) (C : ℝ)
    (hbound : ∀ᵐ x ∂mu, ‖A x‖ ≤ C) : Lp E 2 mu →L[ℝ] Lp F 2 mu := by
  let action (u : Lp E 2 mu) : Lp F 2 mu :=
    ((Lp.memLp u).clm_apply_of_ae_bound hA hbound).toLp (fun x => A x (u x))
  have hae (u : Lp E 2 mu) : action u =ᵐ[mu] fun x => A x (u x) :=
    MemLp.coeFn_toLp _
  let L : Lp E 2 mu →ₗ[ℝ] Lp F 2 mu :=
    { toFun := action
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [hae (u + v), hae u, hae v, Lp.coeFn_add u v,
          Lp.coeFn_add (action u) (action v)] with x huv hu hv hsum hout
        simp only [huv, hsum, hout, Pi.add_apply, hu, hv, map_add]
      map_smul' := by
        intro r u
        apply Lp.ext
        filter_upwards [hae (r • u), hae u, Lp.coeFn_smul r u,
          Lp.coeFn_smul r (action u)] with x hru hu hsmul hout
        simp only [RingHom.id_apply, hru, hsmul, hout, Pi.smul_apply, hu, map_smul] }
  exact L.mkContinuous C fun u => Lp.norm_le_mul_norm_of_ae_le_mul (by
    filter_upwards [hae u, hbound] with x hx hAx
    change ‖action u x‖ ≤ C * ‖u x‖
    rw [hx]
    exact ((A x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right hAx (norm_nonneg _)))

theorem Lp.coefficientL2_ae (A : X → E →L[ℝ] F)
    (hA : AEStronglyMeasurable A mu) (C : ℝ)
    (hbound : ∀ᵐ x ∂mu, ‖A x‖ ≤ C) (u : Lp E 2 mu) :
    Lp.coefficientL2 A hA C hbound u =ᵐ[mu] fun x => A x (u x) :=
  ((Lp.memLp u).clm_apply_of_ae_bound hA hbound).coeFn_toLp

theorem Lp.norm_sq_eq_integral_norm_sq (u : Lp E 2 mu) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq u, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem Lp.tendsto_coefficientL2_apply
    {A : ℕ → X → E →L[ℝ] F} {A0 : X → E →L[ℝ] F}
    (hA : ∀ n, AEStronglyMeasurable (A n) mu)
    (hA0 : AEStronglyMeasurable A0 mu) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ∀ᵐ x ∂mu, ‖A n x‖ ≤ C)
    (hbound0 : ∀ᵐ x ∂mu, ‖A0 x‖ ≤ C)
    (hconv : ∀ᵐ x ∂mu, Tendsto (fun n => A n x) atTop (𝓝 (A0 x)))
    (u : Lp E 2 mu) :
    Tendsto (fun n => Lp.coefficientL2 (A n) (hA n) C (hbound n) u) atTop
      (𝓝 (Lp.coefficientL2 A0 hA0 C hbound0 u)) := by
  let error (n : ℕ) (x : X) : ℝ := ‖A n x (u x) - A0 x (u x)‖ ^ 2
  have hmeas (n : ℕ) : AEStronglyMeasurable (error n) mu :=
    (((Lp.memLp u).clm_apply_of_ae_bound (hA n) (hbound n)).1.sub
      ((Lp.memLp u).clm_apply_of_ae_bound hA0 hbound0).1).norm.pow 2
  have hmajorant : Integrable (fun x => (2 * C) ^ 2 * ‖u x‖ ^ 2) mu :=
    ((Lp.memLp u).norm.integrable_sq).const_mul _
  have herr_bound (n : ℕ) :
      ∀ᵐ x ∂mu, ‖error n x‖ ≤ (2 * C) ^ 2 * ‖u x‖ ^ 2 := by
    filter_upwards [hbound n, hbound0] with x hx hx0
    have hnorm : ‖A n x (u x) - A0 x (u x)‖ ≤ 2 * C * ‖u x‖ := by
      calc
        _ ≤ ‖A n x (u x)‖ + ‖A0 x (u x)‖ := norm_sub_le _ _
        _ ≤ C * ‖u x‖ + C * ‖u x‖ := add_le_add
          (((A n x).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right hx (norm_nonneg _)))
          (((A0 x).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right hx0 (norm_nonneg _)))
        _ = _ := by ring
    change ‖‖A n x (u x) - A0 x (u x)‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  have herr_lim : ∀ᵐ x ∂mu, Tendsto (fun n => error n x) atTop (𝓝 0) := by
    filter_upwards [hconv] with x hx
    have happly : Tendsto (fun n => A n x (u x)) atTop (𝓝 (A0 x (u x))) :=
      ((ContinuousLinearMap.apply ℝ F (u x)).continuous.tendsto (A0 x)).comp hx
    simpa only [error, sub_self, _root_.norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (happly.sub (tendsto_const_nhds (x := A0 x (u x)))).norm.pow 2
  have hint := tendsto_integral_of_dominated_convergence
    (fun x => (2 * C) ^ 2 * ‖u x‖ ^ 2) hmeas hmajorant herr_bound herr_lim
  simp only [integral_zero] at hint
  let L (n : ℕ) := Lp.coefficientL2 (A n) (hA n) C (hbound n) u
  let L0 := Lp.coefficientL2 A0 hA0 C hbound0 u
  have heq (n : ℕ) : ‖L n - L0‖ ^ 2 = ∫ x, error n x ∂mu := by
    rw [Lp.norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (L n) L0,
      Lp.coefficientL2_ae (A n) (hA n) C (hbound n) u,
      Lp.coefficientL2_ae A0 hA0 C hbound0 u] with x hsub hn h0
    rw [hsub, Pi.sub_apply, hn, h0]
  have hsq : Tendsto (fun n => ‖L n - L0‖ ^ 2) atTop (𝓝 0) := by
    simpa only [heq] using hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt

end MeasureTheory
