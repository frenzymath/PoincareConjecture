import PoincareLib.Analysis.Sobolev.WeakCompactness.DerivativeLimit

/-! Strong square errors pass every actual continuous L2 test integral.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareMT

open Poincare.Analysis.Sobolev.WeakCompactness

/-- Restricting to a smaller set preserves vanishing squared L2 approximation errors. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64StrongSquare_restrict
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {mu : Measure X}
    {S K : Set X} (hSK : S ⊆ K) (f : ℕ → X → E) (u : X → E)
    (hi : ∀ j, IntegrableOn (fun x => ‖f j x - u x‖ ^ 2) K mu)
    (hlim : Tendsto (fun j => ∫ x in K, ‖f j x - u x‖ ^ 2 ∂mu) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in S, ‖f j x - u x‖ ^ 2 ∂mu) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => integral_nonneg (fun x => sq_nonneg _)) ?_ hlim
  intro j
  exact setIntegral_mono_set (hi j) (Eventually.of_forall (fun x => sq_nonneg _))
    (Eventually.of_forall hSK)

/-- Actual squared L2 convergence passes every fixed continuous L2 test pairing. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64StrongSquare_pairing_tendsto
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {mu : Measure X}
    (f : ℕ → X → E) (u : X → E) (hf : ∀ j, MemLp (f j) 2 mu) (hu : MemLp u 2 mu)
    (hlim : Tendsto (fun j => ∫ x, ‖f j x - u x‖ ^ 2 ∂mu) atTop (𝓝 0))
    (phi : X → ℝ) (hp : MemLp phi 2 mu) :
    Tendsto (fun j => ∫ x, phi x • f j x ∂mu) atTop (𝓝 (∫ x, phi x • u x ∂mu)) := by
  have hn (j : ℕ) : ‖(hf j).toLp (f j) - hu.toLp u‖ ^ 2 = ∫ x, ‖f j x - u x‖ ^ 2 ∂mu := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf j).toLp (f j)) (hu.toLp u),
      (hf j).coeFn_toLp, hu.coeFn_toLp] with x hx hfx hux
    simp only [hx, Pi.sub_apply, hfx, hux]
  have hL : Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hu.toLp u)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hs : Tendsto (fun j => ‖(hf j).toLp (f j) - hu.toLp u‖ ^ 2) atTop (𝓝 0) := by
      simpa only [hn] using hlim
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs.sqrt
  have hl := ((testIntegral phi hp).continuous.tendsto (hu.toLp u)).comp hL
  simpa only [Function.comp_def, testIntegral_toLp] using hl

end PoincareMT
