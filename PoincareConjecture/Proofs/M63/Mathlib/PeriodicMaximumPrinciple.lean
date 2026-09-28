import PoincareConjecture.Proofs.M63.Mathlib.CompactMaximumPrinciple
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.ScalarOperators.Extrema
import Mathlib.Algebra.Field.Periodic

set_option autoImplicit false

open Set

namespace Poincare.Parabolic

theorem periodic_nonpos_of_deriv_le_mul_at_localMax
    {F V : ℝ → ℝ → ℝ} {p K a b : ℝ} (hp : 0 < p) (hab : a < b)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => F x t) p)
    (hderiv : ∀ x t, t ∈ Ioo a b → HasDerivAt (F x) (V x t) t)
    (hmax : ∀ x t, t ∈ Ioo a b → 0 < F x t →
      IsLocalMax (fun y => F y t) x → V x t ≤ K * F x t)
    (hinit : ∀ x, F x a ≤ 0) :
    ∀ x t, t ∈ Icc a b → F x t ≤ 0 := by
  have hcont : ContinuousOn
      (Function.uncurry (fun (q : Icc (0 : ℝ) p) t => F q t))
      (univ ×ˢ Icc a b) :=
    hF.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      continuous_snd).continuousOn (fun z hz => ⟨mem_univ z.1, hz.2⟩)
  have hcompact := nonpos_of_deriv_le_mul_at_max_interior hab hcont
    (fun q t ht => hderiv q t ht)
    (fun q t ht hpos hq => hmax q t ht hpos <| by
      apply Filter.Eventually.of_forall
      intro x
      obtain ⟨y, hy, hxy⟩ := (hper t ⟨ht.1.le, ht.2.le⟩).exists_mem_Ico₀ hp x
      change F x t ≤ F q t
      rw [hxy]
      exact hq ⟨y, Ico_subset_Icc_self hy⟩)
    (fun q => hinit q)
  intro x t ht
  obtain ⟨y, hy, hxy⟩ := (hper t ht).exists_mem_Ico₀ hp x
  rw [hxy]
  exact hcompact ⟨y, Ico_subset_Icc_self hy⟩ t ht

theorem periodic_nonpos_of_parabolic_le
    {F V A B C : ℝ → ℝ → ℝ} {p K a b : ℝ} (hp : 0 < p) (hab : a < b)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => F x t) p)
    (hderiv : ∀ x t, t ∈ Ioo a b → HasDerivAt (F x) (V x t) t)
    (hA : ∀ x t, t ∈ Ioo a b → 0 ≤ A x t)
    (hC : ∀ x t, t ∈ Ioo a b → C x t ≤ K)
    (hpde : ∀ x t, t ∈ Ioo a b →
      V x t ≤ A x t * deriv (deriv (fun y => F y t)) x +
        B x t * deriv (fun y => F y t) x + C x t * F x t)
    (hinit : ∀ x, F x a ≤ 0) :
    ∀ x t, t ∈ Icc a b → F x t ≤ 0 := by
  refine periodic_nonpos_of_deriv_le_mul_at_localMax (K := K)
    hp hab hF hper hderiv ?_ hinit
  intro x t ht hpos hmax
  have hslice : Continuous (fun y => F y t) := continuousOn_univ.mp <|
    hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun y _ => ⟨mem_univ y, ht.1.le, ht.2.le⟩)
  have hfirst := hmax.deriv_eq_zero
  have hsecond := PoincareConjecture.LeviCivitaData.deriv_deriv_nonpos_of_isLocalMax
    hmax hslice.continuousAt
  have hdiffusion := mul_nonpos_of_nonneg_of_nonpos (hA x t ht) hsecond
  have hreaction := mul_le_mul_of_nonneg_right (hC x t ht) hpos.le
  have h := hpde x t ht
  rw [hfirst, mul_zero, add_zero] at h
  linarith

theorem periodic_le_of_parabolic_le_barrier
    {F V A B : ℝ → ℝ → ℝ} {H H' D : ℝ → ℝ} {p K a b : ℝ}
    (hp : 0 < p) (hab : a < b)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => F x t) p)
    (hderiv : ∀ x t, t ∈ Ioo a b → HasDerivAt (F x) (V x t) t)
    (hA : ∀ x t, t ∈ Ioo a b → 0 ≤ A x t)
    (hpde : ∀ x t, t ∈ Ioo a b →
      V x t ≤ A x t * deriv (deriv (fun y => F y t)) x +
        B x t * deriv (fun y => F y t) x + K * F x t + D t)
    (hH : ContinuousOn H (Icc a b))
    (hHderiv : ∀ t ∈ Ioo a b, HasDerivAt H (H' t) t)
    (hbarrier : ∀ t ∈ Ioo a b, K * H t + D t ≤ H' t)
    (hinit : ∀ x, F x a ≤ H a) :
    ∀ x t, t ∈ Icc a b → F x t ≤ H t := by
  have hcont : ContinuousOn (Function.uncurry (fun x t => F x t - H t))
      (univ ×ˢ Icc a b) :=
    hF.sub (hH.comp continuous_snd.continuousOn (fun _ hz => hz.2))
  have hzero := periodic_nonpos_of_parabolic_le
    (F := fun x t => F x t - H t) (V := fun x t => V x t - H' t)
    (A := A) (B := B) (C := fun _ _ => K) (K := K) hp hab hcont
    (fun t ht x => by simp only [(hper t ht) x])
    (fun x t ht => (hderiv x t ht).sub (hHderiv t ht))
    hA (fun _ _ _ => le_rfl)
    (fun x t ht => by
      simp only [deriv_sub_const_fun, deriv_sub_const]
      linarith [hpde x t ht, hbarrier t ht])
    (fun x => sub_nonpos.mpr (hinit x))
  intro x t ht
  exact sub_nonpos.mp (hzero x t ht)

theorem periodic_le_affine_mul_exp
    {F V A B : ℝ → ℝ → ℝ} {p K d R a b : ℝ}
    (hp : 0 < p) (hab : a < b) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => F x t) p)
    (hderiv : ∀ x t, t ∈ Ioo a b → HasDerivAt (F x) (V x t) t)
    (hA : ∀ x t, t ∈ Ioo a b → 0 ≤ A x t)
    (hpde : ∀ x t, t ∈ Ioo a b →
      V x t ≤ A x t * deriv (deriv (fun y => F y t)) x +
        B x t * deriv (fun y => F y t) x + K * F x t + d)
    (hinit : ∀ x, F x a ≤ R) :
    ∀ x t, t ∈ Icc a b →
      F x t ≤ (R + d * (t - a)) * Real.exp (K * (t - a)) := by
  apply periodic_le_of_parabolic_le_barrier
    (D := fun _ => d)
    (H' := fun t => d * Real.exp (K * (t - a)) +
      K * ((R + d * (t - a)) * Real.exp (K * (t - a))))
    hp hab hF hper hderiv hA hpde
  · exact (by fun_prop : Continuous
      (fun t => (R + d * (t - a)) * Real.exp (K * (t - a)))).continuousOn
  · intro t _
    have hlin : HasDerivAt (fun s => R + d * (s - a)) d t := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id t).sub_const a).const_mul d).const_add R
    have hexp : HasDerivAt (fun s => Real.exp (K * (s - a)))
        (Real.exp (K * (t - a)) * K) t := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id t).sub_const a).const_mul K).exp
    simpa only [Pi.mul_def, mul_assoc, mul_comm, mul_left_comm] using hlin.mul hexp
  · intro t ht
    have h := Real.one_le_exp_iff.mpr (mul_nonneg hK (sub_nonneg.mpr ht.1.le))
    nlinarith
  · simpa using hinit

theorem periodic_exp_le_of_parabolic_ge
    {F V A B C : ℝ → ℝ → ℝ} {p K L m a b : ℝ}
    (hp : 0 < p) (hab : a < b) (hm : 0 ≤ m)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => F x t) p)
    (hderiv : ∀ x t, t ∈ Ioo a b → HasDerivAt (F x) (V x t) t)
    (hA : ∀ x t, t ∈ Ioo a b → 0 ≤ A x t)
    (hClower : ∀ x t, t ∈ Ioo a b → -K ≤ C x t)
    (hCupper : ∀ x t, t ∈ Ioo a b → C x t ≤ L)
    (hpde : ∀ x t, t ∈ Ioo a b →
      A x t * deriv (deriv (fun y => F y t)) x +
        B x t * deriv (fun y => F y t) x + C x t * F x t ≤ V x t)
    (hinit : ∀ x, m ≤ F x a) :
    ∀ x t, t ∈ Icc a b → m * Real.exp (-K * (t - a)) ≤ F x t := by
  let H : ℝ → ℝ := fun t => m * Real.exp (-K * (t - a))
  have hH : Continuous H := by dsimp [H]; fun_prop
  have hHnonneg : ∀ t, 0 ≤ H t := fun t => mul_nonneg hm (Real.exp_pos _).le
  have hHderiv : ∀ t, HasDerivAt H (-K * H t) t := by
    intro t
    simpa only [H, id_eq, mul_one, mul_assoc, mul_comm, mul_left_comm] using
      ((((hasDerivAt_id t).sub_const a).const_mul (-K)).exp.const_mul m)
  have hcont : ContinuousOn (Function.uncurry (fun x t => H t - F x t))
      (univ ×ˢ Icc a b) :=
    (hH.comp continuous_snd).continuousOn.sub hF
  have hzero := periodic_nonpos_of_parabolic_le
    (F := fun x t => H t - F x t) (V := fun x t => -K * H t - V x t)
    (A := A) (B := B) (C := C) (K := L) hp hab hcont
    (fun t ht x => by simp only [(hper t ht) x])
    (fun x t ht => (hHderiv t).sub (hderiv x t ht)) hA hCupper
    (fun x t ht => by
      have hfirst : deriv (fun y => H t - F y t) = -deriv (fun y => F y t) := by
        ext y
        exact deriv_const_sub (H t)
      rw [hfirst, deriv.neg]
      simp only [Pi.neg_apply]
      have hreaction := mul_le_mul_of_nonneg_right (hClower x t ht) (hHnonneg t)
      nlinarith [hpde x t ht])
    (fun x => by simpa only [H, sub_self, mul_zero, Real.exp_zero, mul_one,
      sub_nonpos] using hinit x)
  intro x t ht
  exact sub_nonpos.mp (hzero x t ht)

theorem weighted_deriv_eq
    {f w : ℝ → ℝ} {x : ℝ} (hw : DifferentiableAt ℝ w x)
    (hf' : DifferentiableAt ℝ (deriv f) x) :
    w x * deriv (fun y => w y * deriv f y) x =
      w x ^ 2 * deriv (deriv f) x + (w x * deriv w x) * deriv f x := by
  change w x * deriv (w * deriv f) x = _
  rw [deriv_mul hw hf']
  ring

theorem weighted_deriv_nonpos_of_isLocalMax
    {f w : ℝ → ℝ} {x : ℝ} (hmax : IsLocalMax f x)
    (hf : ContinuousAt f x) (hw : DifferentiableAt ℝ w x)
    (hf' : DifferentiableAt ℝ (deriv f) x) :
    w x * deriv (fun y => w y * deriv f y) x ≤ 0 := by
  change w x * deriv (w * deriv f) x ≤ 0
  rw [deriv_mul hw hf', hmax.deriv_eq_zero, mul_zero, zero_add, ← mul_assoc]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) <|
    PoincareConjecture.LeviCivitaData.deriv_deriv_nonpos_of_isLocalMax hmax hf

theorem periodic_le_affine_mul_exp_of_weighted_parabolic_le
    {F V w B : ℝ → ℝ → ℝ} {p K d R a b : ℝ}
    (hp : 0 < p) (hab : a < b) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => F x t) p)
    (hderiv : ∀ x t, t ∈ Ioo a b → HasDerivAt (F x) (V x t) t)
    (hw : ∀ x t, t ∈ Ioo a b → DifferentiableAt ℝ (fun y => w y t) x)
    (hspace : ∀ x t, t ∈ Ioo a b → DifferentiableAt ℝ (deriv (fun y => F y t)) x)
    (hpde : ∀ x t, t ∈ Ioo a b →
      V x t ≤ w x t * deriv (fun y => w y t * deriv (fun z => F z t) y) x +
        B x t * (w x t * deriv (fun y => F y t) x) + K * F x t + d)
    (hinit : ∀ x, F x a ≤ R) :
    ∀ x t, t ∈ Icc a b →
      F x t ≤ (R + d * (t - a)) * Real.exp (K * (t - a)) := by
  refine periodic_le_affine_mul_exp
    (A := fun x t => w x t ^ 2)
    (B := fun x t => w x t * deriv (fun y => w y t) x + B x t * w x t)
    hp hab hK hd hF hper hderiv (fun x t _ => sq_nonneg (w x t)) ?_ hinit
  intro x t ht
  have h := hpde x t ht
  rw [weighted_deriv_eq (hw x t ht) (hspace x t ht)] at h
  nlinarith

theorem periodic_exp_le_of_weighted_parabolic_ge
    {F V w B C : ℝ → ℝ → ℝ} {p K L m a b : ℝ}
    (hp : 0 < p) (hab : a < b) (hm : 0 ≤ m)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => F x t) p)
    (hderiv : ∀ x t, t ∈ Ioo a b → HasDerivAt (F x) (V x t) t)
    (hw : ∀ x t, t ∈ Ioo a b → DifferentiableAt ℝ (fun y => w y t) x)
    (hspace : ∀ x t, t ∈ Ioo a b → DifferentiableAt ℝ (deriv (fun y => F y t)) x)
    (hClower : ∀ x t, t ∈ Ioo a b → -K ≤ C x t)
    (hCupper : ∀ x t, t ∈ Ioo a b → C x t ≤ L)
    (hpde : ∀ x t, t ∈ Ioo a b →
      w x t * deriv (fun y => w y t * deriv (fun z => F z t) y) x +
        B x t * (w x t * deriv (fun y => F y t) x) + C x t * F x t ≤ V x t)
    (hinit : ∀ x, m ≤ F x a) :
    ∀ x t, t ∈ Icc a b → m * Real.exp (-K * (t - a)) ≤ F x t := by
  refine periodic_exp_le_of_parabolic_ge
    (A := fun x t => w x t ^ 2)
    (B := fun x t => w x t * deriv (fun y => w y t) x + B x t * w x t)
    hp hab hm hF hper hderiv (fun x t _ => sq_nonneg (w x t))
    hClower hCupper ?_ hinit
  intro x t ht
  have h := hpde x t ht
  rw [weighted_deriv_eq (hw x t ht) (hspace x t ht)] at h
  nlinarith

end Poincare.Parabolic
