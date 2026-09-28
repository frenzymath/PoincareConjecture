import PoincareConjecture.Proofs.Horizon.Analysis.Complex.SmoothLogarithm
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.DividedDifferences











noncomputable section
set_option autoImplicit false

open Set Function
open scoped ContDiff

namespace Poincare.Topology.Plane

private theorem not_periodic_of_exp_antiperiodic
    {L : ℝ → ℂ} (hL : Continuous L) (a : ℝ)
    (hper : Function.Periodic L (2 * a))
    (hanti : ∀ s, Complex.exp (L (s + a)) = -Complex.exp (L s)) : False := by
  let D : ℝ → ℂ := fun s => L (s + a) - L s
  have hD : Continuous D := by fun_prop
  have hexp (s : ℝ) : Complex.exp (D s) = -1 := by
    simp [D, Complex.exp_sub, hanti s, Complex.exp_ne_zero]
  have hc : D a = D 0 := Complex.isCoveringMap_exp.const_of_comp hD
    (fun s t => Subtype.ext ((hexp s).trans (hexp t).symm)) a 0
  have hp : L (a + a) = L 0 := by simpa [two_mul] using hper 0
  have hz : D 0 = 0 := by
    dsimp only [D] at hc ⊢
    simp only [zero_add] at hc ⊢
    linear_combination (hp - hc) / 2
  have := hexp 0
  norm_num [hz] at this



theorem not_periodic_tangent_logarithm
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) {P : ℝ} (hP : 0 < P)
    (hper : Function.Periodic γ P)
    (hsep : ∀ s u, 0 < u → u < P → γ (s + u) ≠ γ s)
    {L : ℝ → ℂ} (hL : Continuous L) (hLper : Function.Periodic L P)
    (hderiv : ∀ s, Complex.exp (L s) = deriv γ s) : False := by
  let u : ℝ → ℝ := fun t => max 0 (min t (P / 2))
  have hu : Continuous u := by fun_prop
  have hu0 : u 0 = 0 := by simp [u]
  have huhalf : u (P / 2) = P / 2 := by simp [u, (half_pos hP).le]
  have hu_bounds (t : ℝ) : 0 ≤ u t ∧ u t ≤ P / 2 :=
    ⟨le_max_left _ _, max_le (by positivity) (min_le_right _ _)⟩
  let f : ℝ × ℝ → ℂ := fun z => dslope γ z.1 (z.1 + u z.2)
  have hf : Continuous f := (Poincare.Analysis.contDiff_dslope_uncurry hγ).continuous.comp
    (continuous_fst.prodMk (continuous_fst.add (hu.comp continuous_snd)))
  have hfzero (s : ℝ) : f (s, 0) = deriv γ s := by simp [f, hu0]
  have hfne (z : ℝ × ℝ) : f z ≠ 0 := by
    by_cases hz : u z.2 = 0
    · simp [f, hz, ← hderiv z.1]
    · have huz : 0 < u z.2 := lt_of_le_of_ne (hu_bounds z.2).1 (Ne.symm hz)
      have hneq : γ (z.1 + u z.2) ≠ γ z.1 := hsep _ _ huz (by linarith [(hu_bounds z.2).2])
      intro h
      have hd := sub_smul_dslope γ z.1 (z.1 + u z.2)
      change dslope γ z.1 (z.1 + u z.2) = 0 at h
      rw [h, smul_zero] at hd
      exact hneq (sub_eq_zero.mp hd.symm)
  have hfper (s t : ℝ) : f (s + P, t) = f (s, t) := by
    by_cases ht : u t = 0
    · simp only [f, ht, add_zero, dslope_same, ← hderiv, hLper s]
    · have hs : s + u t ≠ s := by simpa using ht
      have hsP : s + P + u t ≠ s + P := by simpa using ht
      simp only [f, dslope_of_ne γ hs, dslope_of_ne γ hsP, slope]
      rw [show s + P + u t = (s + u t) + P by ring, hper, hper]
      congr 1
      ring
  obtain ⟨G, ⟨hG0, hG⟩, _⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
      ⟨f, hf⟩ (a₀ := (0, 0)) (e₀ := L 0)
      (by simpa [hfzero] using hderiv 0) (by simpa using hfne)
  have hexp (s t : ℝ) : Complex.exp (G (s, t)) = f (s, t) := congrFun hG (s, t)
  have hGzero : ∀ s, G (s, 0) = L s := by
    have he := Complex.isCoveringMap_exp.eq_of_comp_eq
      (G.continuous.comp (continuous_id.prodMk continuous_const)) hL
      (funext fun s => Subtype.ext (by
        change Complex.exp (G (s, 0)) = Complex.exp (L s)
        rw [hexp, hfzero, hderiv])) 0 hG0
    exact congrFun he
  have hGper : ∀ s t, G (s + P, t) = G (s, t) := by
    have he := Complex.isCoveringMap_exp.eq_of_comp_eq
      (G.continuous.comp ((continuous_fst.add (continuous_const (y := P))).prodMk continuous_snd))
      G.continuous
      (funext fun z => Subtype.ext (by
        change Complex.exp (G (z.1 + P, z.2)) = Complex.exp (G z)
        rw [hexp, hexp, hfper])) (0, 0)
      (by change G (0 + P, 0) = G (0, 0); rw [hGzero, hGzero, hLper])
    exact fun s t => congrFun he (s, t)
  apply not_periodic_of_exp_antiperiodic
    (L := fun s => G (s, P / 2))
    (G.continuous.comp (continuous_id.prodMk continuous_const)) (P / 2)
    (fun s => by convert hGper s (P / 2) using 1; congr 2; ring)
  intro s
  rw [hexp, hexp]
  have hhalf : P / 2 ≠ 0 := ne_of_gt (half_pos hP)
  simp only [f, huhalf,
    dslope_of_ne γ (by simpa using hhalf : s + P / 2 + P / 2 ≠ s + P / 2),
    dslope_of_ne γ (by simpa using hhalf : s + P / 2 ≠ s), slope]
  rw [show s + P / 2 + P / 2 = s + P by ring, hper]
  rw [show s + P - (s + P / 2) = P / 2 by ring,
    show s + P / 2 - s = P / 2 by ring]
  simp only [vsub_eq_sub]
  rw [← neg_sub (γ (s + P / 2)) (γ s), smul_neg]

end Poincare.Topology.Plane
