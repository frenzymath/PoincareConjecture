import PoincareConjecture.Proofs.Horizon.Analysis.ODE.BoundedExistence

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.ODE.Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem contDiffAt_solution_family_of_nonneg
    {F : E → E} (hF : ContDiff ℝ ∞ F) {Φ : E × ℝ → E}
    (hinit : ∀ x, Φ (x, 0) = x)
    (hflow : ∀ x t, HasDerivAt (fun s => Φ (x, s)) (F (Φ (x, t))) t)
    (x : E) {t : ℝ} (ht : 0 ≤ t) : ContDiffAt ℝ ∞ Φ (x, t) := by
  obtain ⟨V, ε, Ψ, hV, hxV, hε, hΨ, hiΨ, hdΨ⟩ :=
    LocalFlow.exists_smooth_flow_along_compact_interval
      isOpen_univ hF.contDiffOn isOpen_univ convex_univ
      (γ := fun s => Φ (x, s)) (fun s _ => ⟨mem_univ _, hflow x s⟩)
      ht (subset_univ _)
  rw [hinit x] at hxV
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (t + ε) := ⟨by linarith, by linarith⟩
  have heq : EqOn Φ Ψ (V ×ˢ Ioo (-ε) (t + ε)) := by
    rintro ⟨y, s⟩ ⟨hy, hs⟩
    exact eqOn_of_hasDerivAt isOpen_univ hF.contDiffOn isOpen_Ioo
      (convex_Ioo _ _).isPreconnected
      (fun r _ => ⟨mem_univ _, hflow y r⟩) (hdΨ y hy)
      h0 ((hinit y).trans (hiΨ y hy).symm) hs
  have hmem : V ×ˢ Ioo (-ε) (t + ε) ∈ 𝓝 (x, t) :=
    (hV.prod isOpen_Ioo).mem_nhds ⟨hxV, by constructor <;> linarith⟩
  exact (hΨ.contDiffAt hmem).congr_of_eventuallyEq
    (Filter.Eventually.mono hmem fun _ hz => heq hz)

theorem contDiff_solution_family
    {F : E → E} (hF : ContDiff ℝ ∞ F) {Φ : E × ℝ → E}
    (hinit : ∀ x, Φ (x, 0) = x)
    (hflow : ∀ x t, HasDerivAt (fun s => Φ (x, s)) (F (Φ (x, t))) t) :
    ContDiff ℝ ∞ Φ := by
  apply contDiff_iff_contDiffAt.mpr
  rintro ⟨x, t⟩
  by_cases ht : 0 ≤ t
  · exact contDiffAt_solution_family_of_nonneg hF hinit hflow x ht
  · let Ψ : E × ℝ → E := fun z => Φ (z.1, -z.2)
    have hiΨ (y : E) : Ψ (y, 0) = y := by simp only [Ψ, neg_zero, hinit]
    have hdΨ (y : E) (s : ℝ) :
        HasDerivAt (fun r => Ψ (y, r)) ((-F) (Ψ (y, s))) s := by
      simpa only [Ψ, Function.comp_def, neg_smul, one_smul, Pi.neg_apply] using
        (hflow y (-s)).scomp s (hasDerivAt_neg s)
    have hs := contDiffAt_solution_family_of_nonneg hF.neg hiΨ hdΨ x
      (neg_nonneg.mpr (le_of_not_ge ht))
    have hr : ContDiff ℝ ∞ (fun z : E × ℝ => (z.1, -z.2)) :=
      contDiff_fst.prodMk contDiff_snd.neg
    simpa only [Ψ, Function.comp_def, neg_neg] using hs.comp (x, t) hr.contDiffAt

theorem exists_smooth_parametric_flow
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P]
    {H : P × E → E} (hH : ContDiff ℝ ∞ H)
    {K : Set E} (hK : IsCompact K) {v : E}
    (hfix : ∀ p x, x ∉ K → H (p, x) = v) :
    ∃ Φ : P → ℝ → E → E,
      ContDiff ℝ ∞ (fun z : P × (ℝ × E) => Φ z.1 z.2.1 z.2.2) ∧
      (∀ p x, Φ p 0 x = x) ∧
      (∀ p x t, HasDerivAt (fun s => Φ p s x) (H (p, Φ p t x)) t) ∧
      (∀ p s t x, Φ p (s + t) x = Φ p s (Φ p t x)) ∧
      ∀ p t, Function.LeftInverse (Φ p (-t)) (Φ p t) ∧
        Function.RightInverse (Φ p (-t)) (Φ p t) := by
  classical
  have hHp (p : P) : ContDiff ℝ ∞ (fun x => H (p, x)) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  have hex (p : P) (x : E) : ∃ γ : ℝ → E,
      γ 0 = x ∧ ∀ t, HasDerivAt γ (H (p, γ t)) t :=
    exists_global_solution_of_eq_const_off_compact (hHp p) hK (hfix p) x
  choose γ hγinit hγflow using hex
  let Φ : P → ℝ → E → E := fun p t x => γ p x t
  have hiΦ (p : P) (x : E) : Φ p 0 x = x := hγinit p x
  have hdΦ (p : P) (x : E) (t : ℝ) :
      HasDerivAt (fun s => Φ p s x) (H (p, Φ p t x)) t := hγflow p x t
  let F : P × E → P × E := fun z => (0, H z)
  let Ψ : (P × E) × ℝ → P × E := fun z => (z.1.1, Φ z.1.1 z.2 z.1.2)
  have hF : ContDiff ℝ ∞ F := contDiff_const.prodMk hH
  have hiΨ (z : P × E) : Ψ (z, 0) = z := by
    exact Prod.ext rfl (hiΦ z.1 z.2)
  have hdΨ (z : P × E) (t : ℝ) :
      HasDerivAt (fun s => Ψ (z, s)) (F (Ψ (z, t))) t :=
    (hasDerivAt_const t z.1).prodMk (hdΦ z.1 z.2 t)
  have hΨ : ContDiff ℝ ∞ Ψ := contDiff_solution_family hF hiΨ hdΨ
  have hsΦ : ContDiff ℝ ∞ (fun z : P × (ℝ × E) => Φ z.1 z.2.1 z.2.2) := by
    exact (contDiff_snd.comp hΨ).comp
      ((contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)).prodMk
        (contDiff_fst.comp contDiff_snd))
  have hcomp (p : P) (s t : ℝ) (x : E) :
      Φ p (s + t) x = Φ p s (Φ p t x) := by
    have hdshift (r : ℝ) : HasDerivAt (fun u => Φ p (u + t) x)
        (H (p, Φ p (r + t) x)) r := by
      simpa only [Function.comp_def, one_smul, id_eq] using
        (hdΦ p x (r + t)).scomp r ((hasDerivAt_id r).add_const t)
    exact eqOn_of_hasDerivAt isOpen_univ (hHp p).contDiffOn isOpen_univ
      (convex_univ (𝕜 := ℝ)).isPreconnected
      (fun r _ => ⟨mem_univ _, hdshift r⟩)
      (fun r _ => ⟨mem_univ _, hdΦ p (Φ p t x) r⟩)
      (mem_univ 0) (by simp only [zero_add, hiΦ]) (mem_univ s)
  refine ⟨Φ, hsΦ, hiΦ, hdΦ, hcomp, ?_⟩
  intro p t
  constructor
  · intro x
    rw [← hcomp, neg_add_cancel, hiΦ]
  · intro x
    rw [← hcomp, add_neg_cancel, hiΦ]

end Poincare.ODE.Flow
