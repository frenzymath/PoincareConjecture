import PoincareConjecture.Proofs.M07.Analysis.ODE.ParameterJoint

noncomputable section

open Set Metric
open scoped ContDiff

namespace Poincare.ODE.Parameter

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_local_linearOperator
    (A : P × ℝ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A)
    (p₀ : P) (a : ℝ) (B₀ : E →L[ℝ] E) :
    ∃ (r δ : ℝ) (Φ : (P × (E →L[ℝ] E)) → ℝ → E →L[ℝ] E),
      0 < r ∧ 0 < δ ∧
      (∀ z ∈ ball (p₀, B₀) r,
        Φ z 0 = z.2 ∧ ∀ t ∈ Ioo (-δ) δ,
          HasDerivAt (Φ z) ((A (z.1, a + t)).comp (Φ z t)) t) ∧
      ContDiffOn ℝ ∞ (fun q : (P × (E →L[ℝ] E)) × ℝ => Φ q.1 q.2)
        (ball (p₀, B₀) r ×ˢ Ioo (-δ) δ) := by
  let F := P × ℝ × (E →L[ℝ] E)
  let X : F → F := fun z => (0, 1, (A (z.1, z.2.1)).comp z.2.2)
  have hX : ContDiff ℝ ∞ X := by
    exact contDiff_const.prodMk (contDiff_const.prodMk
      ((hA.comp (contDiff_fst.prodMk contDiff_snd.fst)).clm_comp contDiff_snd.snd))
  let z₀ : F := (p₀, a, B₀)
  obtain ⟨r, δ, Ψ, hr, hδ, hΨ, hΨsmooth⟩ :=
    exists_local_flow_joint_contDiff X hX z₀
  let init : P × (E →L[ℝ] E) → F := fun z => (z.1, a, z.2)
  have hinit : ContDiff ℝ ∞ init :=
    contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
  have hinit_mem : ∀ z ∈ ball (p₀, B₀) r, init z ∈ ball z₀ r := by
    intro z hz
    change dist (z.1, a, z.2) (p₀, a, B₀) < r
    simpa [mem_ball, Prod.dist_eq, max_eq_right (dist_nonneg :
      0 ≤ dist z.2 B₀)] using hz
  let Φ : (P × (E →L[ℝ] E)) → ℝ → E →L[ℝ] E :=
    fun z t => (Ψ (init z) t).2.2
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
  have hparam : ∀ z ∈ ball (p₀, B₀) r, ∀ t ∈ Ioo (-δ) δ,
      (Ψ (init z) t).1 = z.1 := by
    intro z hz t ht
    have hder : ∀ s ∈ Ioo (-δ) δ,
        HasDerivAt (fun s => (Ψ (init z) s).1) (0 : P) s := by
      intro s hs
      exact ((hΨ (init z) (hinit_mem z hz)).2 s hs).fst
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-δ) δ).isPreconnected
      (fun s hs => (hder s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hder s hs).deriv) ht hzero
    simpa [(hΨ (init z) (hinit_mem z hz)).1, init] using hc
  have hclock : ∀ z ∈ ball (p₀, B₀) r, ∀ t ∈ Ioo (-δ) δ,
      (Ψ (init z) t).2.1 = a + t := by
    intro z hz t ht
    have hder : ∀ s ∈ Ioo (-δ) δ,
        HasDerivAt (fun s => (Ψ (init z) s).2.1 - s) (0 : ℝ) s := by
      intro s hs
      have hc : HasDerivAt (fun s => (Ψ (init z) s).2.1) 1 s :=
        ((hΨ (init z) (hinit_mem z hz)).2 s hs).snd.fst
      convert hc.sub (hasDerivAt_id s) using 1 <;> first | rfl | simp
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-δ) δ).isPreconnected
      (fun s hs => (hder s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hder s hs).deriv) ht hzero
    have hc' : (Ψ (init z) t).2.1 - t = a := by
      simpa [(hΨ (init z) (hinit_mem z hz)).1, init] using hc
    exact sub_eq_iff_eq_add.mp hc'
  refine ⟨r, δ, Φ, hr, hδ, ?_, ?_⟩
  · intro z hz
    refine ⟨?_, ?_⟩
    · change (Ψ (init z) 0).2.2 = _
      rw [(hΨ (init z) (hinit_mem z hz)).1]
    · intro t ht
      have hd : HasDerivAt (fun t => (Ψ (init z) t).2.2)
          ((A ((Ψ (init z) t).1, (Ψ (init z) t).2.1)).comp (Ψ (init z) t).2.2) t :=
        ((hΨ (init z) (hinit_mem z hz)).2 t ht).snd.snd
      simpa [X, Φ, hparam z hz t ht, hclock z hz t ht] using hd
  · have harg : ContDiff ℝ ∞
        (fun q : (P × (E →L[ℝ] E)) × ℝ => (init q.1, q.2)) :=
      (hinit.comp contDiff_fst).prodMk contDiff_snd
    exact (hΨsmooth.comp harg.contDiffOn
      (fun q hq => ⟨hinit_mem q.1 hq.1, hq.2⟩)).snd.snd

end Poincare.ODE.Parameter
