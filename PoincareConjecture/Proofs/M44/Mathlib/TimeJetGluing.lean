import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem hasDerivAt_of_eventually_hasDerivAt_of_ne
    {f g : ℝ → E} {t : ℝ} (hf : ContinuousAt f t) (hg : ContinuousAt g t)
    (hderiv : ∀ᶠ s in 𝓝 t, s ≠ t → HasDerivAt f (g s) s) :
    HasDerivAt f (g t) t := by
  have hleft : ∀ᶠ s in 𝓝[<] t, HasDerivAt f (g s) s := by
    filter_upwards [hderiv.filter_mono inf_le_left, self_mem_nhdsWithin] with s hs hst
    exact hs (ne_of_lt hst)
  have hright : ∀ᶠ s in 𝓝[>] t, HasDerivAt f (g s) s := by
    filter_upwards [hderiv.filter_mono inf_le_left, self_mem_nhdsWithin] with s hs hst
    exact hs (ne_of_gt hst)
  have hL : HasDerivWithinAt f (g t) (Iic t) t :=
    hasDerivWithinAt_Iic_of_tendsto_deriv
      (s := {s | HasDerivAt f (g s) s})
      (fun _ hs => hs.differentiableAt.differentiableWithinAt) hf.continuousWithinAt
      hleft ((hg.mono_left inf_le_left).congr' (hleft.mono fun _ hs => hs.deriv.symm))
  have hR : HasDerivWithinAt f (g t) (Ici t) t :=
    hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := {s | HasDerivAt f (g s) s})
      (fun _ hs => hs.differentiableAt.differentiableWithinAt) hf.continuousWithinAt
      hright ((hg.mono_left inf_le_left).congr' (hright.mono fun _ hs => hs.deriv.symm))
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hL.union hR




theorem hasDerivAt_of_hasDerivAt_off_finite
    {f g : ℝ → E} {J S : Set ℝ} (hJ : IsOpen J) (hS : S.Finite)
    (hf : ContinuousOn f J) (hg : ContinuousOn g J)
    (hderiv : ∀ t ∈ J, t ∉ S → HasDerivAt f (g t) t)
    {t : ℝ} (ht : t ∈ J) : HasDerivAt f (g t) t := by
  apply hasDerivAt_of_eventually_hasDerivAt_of_ne
    (hf.continuousAt (hJ.mem_nhds ht)) (hg.continuousAt (hJ.mem_nhds ht))
  have hnear : (S \ {t})ᶜ ∈ 𝓝 t :=
    hS.sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [hJ.mem_nhds ht, hnear] with s hs houtside hne
  exact hderiv s hs (fun hmem => houtside ⟨hmem, hne⟩)






theorem contDiffOn_of_finite_jet_evolution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ℕ → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {J S : Set ℝ} {U : Set V} (hJ : IsOpen J) (hU : IsOpen U) (hS : S.Finite)
    (f : ∀ i, ℝ × V → F i)
    (spatial : ∀ i, F (i + 1) →L[ℝ] V →L[ℝ] F i)
    (arity : ℕ → ℕ)
    (rhs : ∀ i, (∀ j : Fin (arity i), F j.1) → F i)
    (domain : ∀ i, Set (∀ j : Fin (arity i), F j.1))
    (hrhs : ∀ i, ContDiffOn ℝ ∞ (rhs i) (domain i))
    (hrange : ∀ i p, p ∈ J ×ˢ U → (fun j : Fin (arity i) => f j.1 p) ∈ domain i)
    (hcont : ∀ i, ContinuousOn (f i) (J ×ˢ U))
    (hspatial : ∀ i t, t ∈ J → ∀ x ∈ U,
      HasFDerivAt (fun y => f i (t, y)) (spatial i (f (i + 1) (t, x))) x)
    (htime : ∀ i t, t ∈ J → t ∉ S → ∀ x ∈ U,
      HasDerivAt (fun s => f i (s, x))
        (rhs i (fun j : Fin (arity i) => f j.1 (t, x))) t) :
    ∀ i, ContDiffOn ℝ ∞ (f i) (J ×ˢ U) := by
  let H (i : ℕ) (p : ℝ × V) := rhs i (fun j : Fin (arity i) => f j.1 p)
  have hH : ∀ i, ContinuousOn (H i) (J ×ˢ U) := by
    intro i
    exact (hrhs i).continuousOn.comp (continuousOn_pi.mpr fun j => hcont j.1) (hrange i)
  have htimeAll (i : ℕ) (t : ℝ) (ht : t ∈ J) (x : V) (hx : x ∈ U) :
      HasDerivAt (fun s => f i (s, x)) (H i (t, x)) t := by
    apply hasDerivAt_of_hasDerivAt_off_finite hJ hS
      ((hcont i).comp (continuousOn_id.prodMk continuousOn_const) (fun _ hs => ⟨hs, hx⟩))
      ((hH i).comp (continuousOn_id.prodMk continuousOn_const) (fun _ hs => ⟨hs, hx⟩))
      (fun s hs hnot => htime i s hs hnot x hx) ht
  let D (i : ℕ) (p : ℝ × V) : ℝ × V →L[ℝ] F i :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (H i p)).coprod (spatial i (f (i + 1) p))
  have hD (i : ℕ) (p : ℝ × V) (hp : p ∈ J ×ˢ U) : HasFDerivAt (f i) (D i p) p := by
    have hcH : ContinuousOn
        (fun q => (ContinuousLinearMap.id ℝ ℝ).smulRight (H i q)) (J ×ˢ U) :=
      (ContinuousLinearMap.smulRightL ℝ ℝ (F i)
        (ContinuousLinearMap.id ℝ ℝ)).continuous.comp_continuousOn
        (hH i)
    have hcX : ContinuousOn (fun q => spatial i (f (i + 1) q)) (J ×ˢ U) :=
      (spatial i).continuous.comp_continuousOn (hcont (i + 1))
    apply (hasStrictFDerivAt_uncurry_coprod (f := fun t x => f i (t, x))
      (f₁ := fun t x => (ContinuousLinearMap.id ℝ ℝ).smulRight (H i (t, x)))
      (f₂ := fun t x => spatial i (f (i + 1) (t, x))) ?_ ?_
      (hcH.continuousAt ((hJ.prod hU).mem_nhds hp))
      (hcX.continuousAt ((hJ.prod hU).mem_nhds hp))).hasFDerivAt
    · filter_upwards [(hJ.prod hU).mem_nhds hp] with q hq
      exact (htimeAll i q.1 hq.1 q.2 hq.2).hasFDerivAt
    · filter_upwards [(hJ.prod hU).mem_nhds hp] with q hq
      exact hspatial i q.1 hq.1 q.2 hq.2
  have hfinite : ∀ n : ℕ, ∀ i, ContDiffOn ℝ n (f i) (J ×ˢ U) := by
    intro n
    induction n with
    | zero => exact fun i => contDiffOn_zero.mpr (hcont i)
    | succ n ih =>
      intro i
      have hHn : ContDiffOn ℝ n (H i) (J ×ˢ U) :=
        ((hrhs i).of_le (by exact_mod_cast le_top)).comp
          (contDiffOn_pi.mpr fun j => ih j.1) (hrange i)
      have hTn := (contDiffOn_const (c := ContinuousLinearMap.id ℝ ℝ)).smulRight hHn
      have hXn : ContDiffOn ℝ n (fun p => spatial i (f (i + 1) p)) (J ×ˢ U) :=
        (spatial i).contDiff.comp_contDiffOn (ih (i + 1))
      have hDn : ContDiffOn ℝ n (D i) (J ×ˢ U) :=
        (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := ℝ)
          (F := V) (G := F i) ℝ).contDiff.comp_contDiffOn
          (hTn.prodMk hXn)
      rw [Nat.cast_add, Nat.cast_one]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
        (hJ.prod hU).uniqueDiffOn).mpr
      exact ⟨by simp, D i, hDn, fun p hp => (hD i p hp).hasFDerivWithinAt⟩
  exact fun i => contDiffOn_infty.mpr (fun n => hfinite n i)

end Poincare
