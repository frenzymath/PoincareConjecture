import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Plane.FlowCoordinates
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Manifold Topology

namespace Poincare.Manifold.PlaneDiffeomorph

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "v₀" => (!₂[(1 : ℝ), 0] : E₂)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

theorem exists_smooth_horizontal_section_map
    {H : P × E₂ → E₂} (hH : ContDiff ℝ ∞ H) (hne : ∀ p x, H (p, x) ≠ 0)
    {L R B T : ℝ} (hLR : L < R)
    (hfix : ∀ p x, x 0 ≤ L ∨ R ≤ x 0 ∨ x 1 ≤ B ∨ T ≤ x 1 → H (p, x) = v₀)
    {Φ : P → ℝ → E₂ → E₂}
    (hΦ : ContDiff ℝ ∞ (fun z : P × (ℝ × E₂) => Φ z.1 z.2.1 z.2.2))
    (hinit : ∀ p x, Φ p 0 x = x)
    (hflow : ∀ p x t, HasDerivAt (fun s => Φ p s x) (H (p, Φ p t x)) t)
    (hcomp : ∀ p s t x, Φ p (s + t) x = Φ p s (Φ p t x)) :
    ∃ σ ρ κ : P × ℝ → ℝ,
      ContDiff ℝ ∞ σ ∧ ContDiff ℝ ∞ ρ ∧ ContDiff ℝ ∞ κ ∧
      (∀ p y, Φ p (σ (p, y)) (!₂[L, y]) = !₂[R, ρ (p, y)]) ∧
      (∀ p y, 0 < σ (p, y)) ∧
      (∀ p, Function.Bijective (fun y => ρ (p, y))) ∧
      (∀ p y, κ (p, ρ (p, y)) = y) ∧
      (∀ p y, ρ (p, κ (p, y)) = y) ∧
      (∀ p y, 0 < deriv (fun z => ρ (p, z)) y) ∧
      ∀ p y, y ≤ B ∨ T ≤ y → ρ (p, y) = y ∧ σ (p, y) = R - L := by
  obtain ⟨τL, hsL, hL, huL⟩ :=
    exists_smooth_horizontal_section_time hH hne hfix L (Or.inl le_rfl) hΦ hflow
  obtain ⟨τR, hsR, hR, huR⟩ :=
    exists_smooth_horizontal_section_time hH hne hfix R (Or.inr le_rfl) hΦ hflow
  let σ : P × ℝ → ℝ := fun z => τR (z.1, !₂[L, z.2])
  let ρ : P × ℝ → ℝ := fun z => Φ z.1 (σ z) (!₂[L, z.2]) 1
  let κ : P × ℝ → ℝ := fun z => Φ z.1 (τL (z.1, !₂[R, z.2])) (!₂[R, z.2]) 1
  have hpoint (c : ℝ) : ContDiff ℝ ∞ (fun z : P × ℝ => (!₂[c, z.2] : E₂)) := by
    apply contDiff_euclidean.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_snd
  have hsσ : ContDiff ℝ ∞ σ := hsR.comp (contDiff_fst.prodMk (hpoint L))
  have hsρ : ContDiff ℝ ∞ ρ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp
      (hΦ.comp (contDiff_fst.prodMk (hsσ.prodMk (hpoint L))))
  have hsκ : ContDiff ℝ ∞ κ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp
      (hΦ.comp (contDiff_fst.prodMk
        ((hsL.comp (contDiff_fst.prodMk (hpoint R))).prodMk (hpoint R))))
  have hcross (p : P) (y : ℝ) :
      Φ p (σ (p, y)) (!₂[L, y]) = !₂[R, ρ (p, y)] := by
    ext i
    fin_cases i
    · exact hR p (!₂[L, y])
    · rfl
  have hbackcross (p : P) (y : ℝ) :
      Φ p (τL (p, !₂[R, y])) (!₂[R, y]) = !₂[L, κ (p, y)] := by
    ext i
    fin_cases i
    · exact hL p (!₂[R, y])
    · rfl
  have hinv (p : P) (t : ℝ) (x : E₂) : Φ p (-t) (Φ p t x) = x := by
    rw [← hcomp, neg_add_cancel, hinit]
  have hleft (p : P) (y : ℝ) : κ (p, ρ (p, y)) = y := by
    have hback : Φ p (-σ (p, y)) (!₂[R, ρ (p, y)]) = !₂[L, y] := by
      rw [← hcross]
      exact hinv p (σ (p, y)) (!₂[L, y])
    have ht : τL (p, !₂[R, ρ (p, y)]) = -σ (p, y) := by
      symm
      apply huL
      rw [hback]
      rfl
    change Φ p (τL (p, !₂[R, ρ (p, y)])) (!₂[R, ρ (p, y)]) 1 = y
    rw [ht, hback]
    rfl
  have hright (p : P) (y : ℝ) : ρ (p, κ (p, y)) = y := by
    have hback : Φ p (-τL (p, !₂[R, y])) (!₂[L, κ (p, y)]) = !₂[R, y] := by
      rw [← hbackcross]
      exact hinv p (τL (p, !₂[R, y])) (!₂[R, y])
    have ht : σ (p, κ (p, y)) = -τL (p, !₂[R, y]) := by
      symm
      apply huR
      rw [hback]
      rfl
    change Φ p (σ (p, κ (p, y))) (!₂[L, κ (p, y)]) 1 = y
    rw [ht, hback]
    rfl
  have hbij (p : P) : Function.Bijective (fun y => ρ (p, y)) :=
    ⟨(show Function.LeftInverse (fun y => κ (p, y)) (fun y => ρ (p, y)) from
      hleft p).injective,
      (show Function.RightInverse (fun y => κ (p, y)) (fun y => ρ (p, y)) from
        hright p).surjective⟩
  have hHp (p : P) : ContDiff ℝ ∞ (fun x => H (p, x)) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  have hpositive (p : P) (y : ℝ) : 0 < σ (p, y) := by
    by_contra! hn
    have heq := Poincare.ODE.Plane.eq_horizontal_backward_ray (hHp p)
      (hflow p (!₂[L, y])) (a := 0)
      (fun x hx => hfix p x (Or.inl hx))
      (by simp only [hinit, Matrix.cons_val_zero]; exact le_rfl)
      (-σ (p, y)) (neg_nonneg.mpr hn)
    have hx := congrArg (fun x : E₂ => x 0) heq
    simp only [zero_sub, neg_neg, hinit, PiLp.sub_apply, PiLp.smul_apply,
      Matrix.cons_val_zero, smul_eq_mul, mul_one] at hx
    have hr := hR p (!₂[L, y])
    change Φ p (σ (p, y)) (!₂[L, y]) 0 = R at hr
    linarith
  have houtside (p : P) (y : ℝ) (hy : y ≤ B ∨ T ≤ y) :
      ρ (p, y) = y ∧ σ (p, y) = R - L := by
    have hline (s : ℝ) : Φ p s (!₂[L, y]) = (!₂[L, y] : E₂) + s • v₀ := by
      have hder (t : ℝ) : HasDerivAt (fun u => (!₂[L, y] : E₂) + u • v₀)
          (H (p, (!₂[L, y] : E₂) + t • v₀)) t := by
        rw [hfix p _ (Or.inr (Or.inr (by simpa using hy)))]
        simpa using ((hasDerivAt_id t).smul_const v₀).const_add (!₂[L, y] : E₂)
      exact Poincare.ODE.eqOn_of_hasDerivAt isOpen_univ (hHp p).contDiffOn
        isOpen_univ isPreconnected_univ
        (fun t _ => ⟨mem_univ _, hflow p (!₂[L, y]) t⟩)
        (fun t _ => ⟨mem_univ _, hder t⟩) (mem_univ 0)
        (by simp [hinit]) (mem_univ s)
    have ht : σ (p, y) = R - L := by
      symm
      apply huR
      rw [hline]
      simp
    refine ⟨?_, ht⟩
    change Φ p (σ (p, y)) (!₂[L, y]) 1 = y
    rw [hline]
    simp
  have hsρp (p : P) : ContDiff ℝ ∞ (fun y => ρ (p, y)) :=
    hsρ.comp (contDiff_const.prodMk contDiff_id)
  have hsκp (p : P) : ContDiff ℝ ∞ (fun y => κ (p, y)) :=
    hsκ.comp (contDiff_const.prodMk contDiff_id)
  have hmono (p : P) : StrictMono (fun y => ρ (p, y)) := by
    rcases (hsρp p).continuous.strictMono_of_inj (hbij p).injective with h | h
    · exact h
    · have he := h (show B - 1 < B by linarith)
      change ρ (p, B) < ρ (p, B - 1) at he
      rw [(houtside p B (Or.inl le_rfl)).1,
        (houtside p (B - 1) (Or.inl (by linarith))).1] at he
      linarith
  have hderiv (p : P) (y : ℝ) : 0 < deriv (fun z => ρ (p, z)) y := by
    have hρd := ((hsρp p).differentiable (by simp) y).hasDerivAt
    have hκd := ((hsκp p).differentiable (by simp) (ρ (p, y))).hasDerivAt
    have hd := hκd.comp y hρd
    have he : ((fun z => κ (p, z)) ∘ fun z => ρ (p, z)) = id :=
      funext (hleft p)
    rw [he] at hd
    have hmul := hd.unique (hasDerivAt_id y)
    have hn : deriv (fun z => ρ (p, z)) y ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hmul
      exact zero_ne_one hmul
    exact lt_of_le_of_ne (hmono p).monotone.deriv_nonneg hn.symm
  exact ⟨σ, ρ, κ, hsσ, hsρ, hsκ, hcross, hpositive, hbij, hleft, hright, hderiv, houtside⟩

omit [CompleteSpace P] in

theorem deriv_section_inverse_pos
    {ρ κ : P × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hκ : ContDiff ℝ ∞ κ)
    (hright : ∀ p y, ρ (p, κ (p, y)) = y)
    (hpos : ∀ p y, 0 < deriv (fun z => ρ (p, z)) y) :
    ∀ p y, 0 < deriv (fun z => κ (p, z)) y := by
  intro p y
  have hsρ : ContDiff ℝ ∞ (fun z => ρ (p, z)) :=
    hρ.comp (contDiff_const.prodMk contDiff_id)
  have hsκ : ContDiff ℝ ∞ (fun z => κ (p, z)) :=
    hκ.comp (contDiff_const.prodMk contDiff_id)
  have hd := ((hsρ.differentiable (by simp) (κ (p, y))).hasDerivAt).comp y
    (hsκ.differentiable (by simp) y).hasDerivAt
  have he : ((fun z => ρ (p, z)) ∘ fun z => κ (p, z)) = id := funext (hright p)
  rw [he] at hd
  have hmul := hd.unique (hasDerivAt_id y)
  have hforward := hpos p (κ (p, y))
  nlinarith

end Poincare.Manifold.PlaneDiffeomorph
